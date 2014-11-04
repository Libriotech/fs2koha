#!/usr/bin/perl
 
# Copyright 2014 Magnus Enger Libriotech
 
=head1 NAME
 
fs2koha.pl - Parse data from FS and insert them into Koha
 
=head1 SYNOPSIS
 
perl fs2koha.pl -i bas.xml -v

sudo koha-shell -c "perl fs2koha.pl -i bas.xml -v -c STUDENT -b MYLIB" kohadev

=head1 PREREQUISITES

  $ sudo apt-get install libxml-libxml-simple-perl

=cut

use Koha::Database;
use C4::Members qw( GetMember AddMember ModMember );
use C4::Members::Messaging;
use XML::LibXML::Simple qw(XMLin);
use Modern::Perl; 
use Getopt::Long;
use Data::Dumper;
use DateTime;
use Time::Piece;
use Pod::Usage;
use Modern::Perl;
 
my $dt = DateTime->now;
my $date = $dt->ymd;
 
# Get options
my ( $input_file, $categorycode, $branchcode, $limit, $verbose, $debug ) = get_options();
 
# Check that the file exists
if ( !-e $input_file ) {
print "The file $input_file does not exist...\n";
exit;
}

# REad the whle file
my $xml = XMLin( $input_file );

# Setup some counters
my $faculty_count   = 0;
my $student_count   = 0;
my $student_new     = 0;
my $student_updated = 0;
my $student_failed  = 0;

# Skip faculty for now
# foreach my $person ( @{ $xml->{'fagperson'} } ) {
#     say 'F ' . $person->{'fornavn'} . ' ' . $person->{'etternavn'};
#     $faculty_count++;
# }

# Iterate over students
foreach my $person ( @{ $xml->{'student'} } ) {
    print 'S ' . $person->{'fornavn'} . ' ' . $person->{'etternavn'} . ' ' . $person->{'studentnr'} if $verbose;
    # This just gets in the way of debugging
    $person->{'studieTilknytninger'} = undef;
    # Email
    if ( $person->{'epost'} ) {
        # Make sure $person->{'emails'} is an arrayref
        if ( ref $person->{'epost'} eq 'HASH' ) {
            push @{ $person->{'emails'} }, $person->{'epost'};
        } else {
            push @{ $person->{'emails'} }, @{ $person->{'epost'} };
        }
        # Pick out the different email types
        foreach my $email ( @{ $person->{'emails'} } ) {
            if ( $email->{'type'} eq 'ekstern' ) {
                $person->{'epost_ekstern'} = $email->{'content'}
            }
            if ( $email->{'type'} eq 'intern' ) {
                $person->{'epost_intern'} = $email->{'content'}
            }
        }
    }
    # Address
    if ( $person->{'adresse'} ) {
        # Make sure $person->{'adresser'} is an arrayref
        if ( ref $person->{'adresse'} eq 'HASH' ) {
            push @{ $person->{'adresser'} }, $person->{'adresse'};
        } else {
            push @{ $person->{'adresser'} }, @{ $person->{'adresse'} };
        }
        # Pick out the different addresses
        foreach my $adr ( @{ $person->{'adresser'} } ) {
            # The zip code is repeated here, so we need to remove the first 5 
            # chars and store the rest
            if ( $adr->{'sted'} ) {
                $adr->{'poststed'} = substr $adr->{'sted'}, 5;
            }
            # Now put the right address in the right slot
            if ( $adr->{'type'} && $adr->{'type'} eq 'semester' ) {
                $person->{'adresse_semester'} = $adr;
            }
            if ( $adr->{'type'} && $adr->{'type'} eq 'hjem' ) {
                $person->{'adresse_hjem'} = $adr;
            }
        }
    }
    # Phone
    if ( $person->{'telefon'} ) {
        # Make sure $person->{'telefoner'} is an arrayref
        if ( ref $person->{'telefon'} eq 'HASH' ) {
            push @{ $person->{'telefoner'} }, $person->{'telefon'};
        } else {
            push @{ $person->{'telefoner'} }, @{ $person->{'telefon'} };
        }
        # Now look for the mobile phone
        foreach my $phone ( @{ $person->{'telefoner'} } ) {
            if ( $phone->{'type'} eq 'mobil' ) {
                $person->{'mobil'} = $phone->{'nr'};
            }
        }
    }
    # Calculate expiration date
    my $year = substr $person->{'studierettSlutt'}, 0, 4;
    if ( $year eq '9999' ) {
        $person->{'expires'} = $person->{'studierettSlutt'};
    } else {
        my $expires = Time::Piece->strptime( $person->{'studierettSlutt'}, "%Y-%m-%d" );
        $expires = $expires->add_years( 5 );
        $person->{'expires'} = $expires->ymd;
    }
    # Dump all of $person if we are debugging
    say Dumper $person if $debug;
    # Figure out if the borrower already exists
    if ( my $member = GetMember( 'cardnumber' => $person->{'studentnr'} ) ) {
        my $borrowernumber = $member->{'borrowernumber'};
        my $success = ModMember( 
            'borrowernumber' => $borrowernumber,
            'cardnumber'   => $person->{'studentnr'},
            'categorycode' => $categorycode,
            'branchcode'   => $branchcode,
            'firstname'    => $person->{'fornavn'}, 
            'surname'      => $person->{'etternavn'},
            'email'        => $person->{'epost_intern'},
            'emailpro'     => $person->{'epost_ekstern'},
            'phone'        => $person->{'mobil'},
            'userid'       => $person->{'brukernavn'},
            'dateexpiry'   => $person->{'expires'},
            # Main address
            'address'      => $person->{'adresse_semester'}->{'gate'}     || '',
            'address2'     => $person->{'adresse_semester'}->{'co'}       || '',
            'zipcode'      => $person->{'adresse_semester'}->{'postnr'}   || '',
            'city'         => $person->{'adresse_semester'}->{'poststed'} || '',
            # Secondary address
            'B_address'      => $person->{'adresse_hjem'}->{'gate'}     || '',
            'B_address2'     => $person->{'adresse_hjem'}->{'co'}       || '',
            'B_zipcode'      => $person->{'adresse_hjem'}->{'postnr'}   || '',
            'B_city'         => $person->{'adresse_hjem'}->{'poststed'} || '',
        );
        if ( $success ) {
            say " - Updated ($borrowernumber)" if $verbose;
            $student_updated++;
        } else {
            say " - FAILED to update ($borrowernumber)" if $verbose;
            $student_failed++;
        }
    } else {
        # Add the borrower
        my $borrowernumber = AddMember(
            'cardnumber'   => $person->{'studentnr'},
            'categorycode' => $categorycode,
            'branchcode'   => $branchcode,
            'firstname'    => $person->{'fornavn'}, 
            'surname'      => $person->{'etternavn'},
            'email'        => $person->{'epost_intern'},
            'emailpro'     => $person->{'epost_ekstern'},
            'phone'        => $person->{'mobil'},
            'userid'       => $person->{'brukernavn'},
            'dateexpiry'   => $person->{'expires'},
            # Main address
            'address'      => $person->{'adresse_semester'}->{'gate'}     || '',
            'address2'     => $person->{'adresse_semester'}->{'co'}       || '',
            'zipcode'      => $person->{'adresse_semester'}->{'postnr'}   || '',
            'city'         => $person->{'adresse_semester'}->{'poststed'} || '',
            # Secondary address
            'B_address'      => $person->{'adresse_hjem'}->{'gate'}     || '',
            'B_address2'     => $person->{'adresse_hjem'}->{'co'}       || '',
            'B_zipcode'      => $person->{'adresse_hjem'}->{'postnr'}   || '',
            'B_city'         => $person->{'adresse_hjem'}->{'poststed'} || '',
        );
        # Set default messaging preferences
        C4::Members::Messaging::SetMessagingPreferencesFromDefaults({
            'borrowernumber' => $borrowernumber,
            'categorycode'   => $categorycode,
        });
        say " - Inserted as new ($borrowernumber)" if $verbose;
        $student_new++;
    }
    $student_count++;
    if ( $limit > 0 && $student_count == $limit ) {
        last;
    }
}

# Summarize
if ( $verbose ) {
    say "\nFaculty:  $faculty_count";
    say "Students: $student_count ($student_new new, $student_updated updated, $student_failed failed)";
}
 
=head1 OPTIONS
 
=over 4
 
=item B<-i, --infile>
 
Name of input file.

=item B<-c, --categorycode>
 
Which categorycode to put people in. Must exist in the Koha you are running against. 

=item B<-b, --branchcode>
 
Which branchcode to put popele in. Must exist in the Koha you are running against. 

=item B<-l, --limit>
 
Limit the number of records processed.
 
=item B<-v --verbose>
 
More verbose output.
 
=item B<-d --debug>
 
Even more verbose output.
 
=item B<-h, -?, --help>
 
Prints this help message and exits.
 
=back

=cut

sub get_options {
 
# Options
my $input_file   = '';
my $categorycode = '';
my $branchcode   = '';
my $limit        = 0;
my $verbose      = '';
my $debug        = '';
my $help         = '';
 
GetOptions (
    'i|infile=s'       => \$input_file,
    'c|categorycode=s' => \$categorycode,
    'b|branchcode=s'   => \$branchcode,
    'l|limit=i'        => \$limit,
    'v|verbose'        => \$verbose,
    'd|debug'          => \$debug,
    'h|?|help'         => \$help
);
 
pod2usage( -exitval => 0 ) if $help;
pod2usage( -msg => "\nMissing Argument: -i, --infile required\n",       -exitval => 1 ) if !$input_file;
pod2usage( -msg => "\nMissing Argument: -c, --categorycode required\n", -exitval => 1 ) if !$categorycode;
pod2usage( -msg => "\nMissing Argument: -b, --branchcode required\n",   -exitval => 1 ) if !$branchcode;
 
return ( $input_file, $categorycode, $branchcode, $limit, $verbose, $debug );
 
}
 
=head1 AUTHOR
 
Magnus Enger
 
=head1 LICENSE
 
This program is free software: you can redistribute it and/or modify
it under the terms of the GNU General Public License as published by
the Free Software Foundation, either version 3 of the License, or
(at your option) any later version.
 
This program is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
GNU General Public License for more details.
 
You should have received a copy of the GNU General Public License
along with this program. If not, see <http://www.gnu.org/licenses/>.
 
=cut