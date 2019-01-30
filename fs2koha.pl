#!/usr/bin/perl
 
# Copyright 2014 Magnus Enger Libriotech
 
=head1 NAME
 
fs2koha.pl - Parse data from FS and insert them into Koha
 
=head1 SYNOPSIS
 
perl fs2koha.pl -i bas.xml -v

sudo koha-shell -c "perl fs2koha.pl -i bas.xml -v -s STUDENT -f FACULTY -b MYLIB" kohadev

=head1 PREREQUISITES

  $ sudo apt-get install libxml-libxml-simple-perl

=cut

use Koha::Database;
use Koha::AuthUtils;
use Koha::Patrons;

use C4::Members::Messaging;

use XML::LibXML::Simple qw(XMLin);
use Modern::Perl; 
use Getopt::Long;
use Data::Dumper;
use DateTime;
use Time::Piece;
use Email::Sender::Simple qw(sendmail);
use Email::Simple;
use Email::Sender::Transport::Sendmail qw();
use Try::Tiny;
use File::Slurper qw( read_text );
use Digest::MD5 qw( md5_base64 );
use Pod::Usage;
use Modern::Perl;
 
my $dt = DateTime->now;
my $date = $dt->ymd;
 
# Get options
my ( $input_file, $students, $faculty, $branchcode, $password, $pwnotify, $limit, $verbose, $debug ) = get_options();
 
# Check that the file exists
if ( !-e $input_file ) {
    say "The file $input_file does not exist...";
    exit;
}
if ( $password && !-e $password ) {
    say "The file $password does not exist...";
    exit;
}
if ( $pwnotify && !-e $pwnotify ) {
    say "The file $pwnotify does not exist...";
    exit;
}

# Read the whole file
my $xml = XMLin( $input_file );

# Setup some counters
my $faculty_count   = 0;
my $faculty_new     = 0;
my $faculty_updated = 0;
my $faculty_failed  = 0;
my $student_count   = 0;
my $student_new     = 0;
my $student_updated = 0;
my $student_failed  = 0;

my %seen_fslopenr;

if ( $faculty ne '' ) {
    foreach my $person ( @{ $xml->{'fagperson'} } ) {
        print 'F ' . $person->{'fornavn'} . ' ' . $person->{'etternavn'} if $verbose;

        $seen_fslopenr{ $person->{'fsLopenr'} }++;
        next if $seen_fslopenr{ $person->{'fsLopenr'} } > 1;

        $person = fix_email( $person );
        $person = fix_phone( $person );
        # Try to find patron based on cardnumber
        my $member = Koha::Patrons->find({ 'cardnumber' => $person->{'fsLopenr'} });
        if ( !$member && $person->{'brukernavn'} ) {
            # If cardnumber failed, try userid
            $member = Koha::Patrons->find({ 'userid' => $person->{'brukernavn'} });
        }
        my $borrowernumber;
        if ( $member ) {
            # Update the borrower
            $borrowernumber = $member->{'borrowernumber'};
            my %borrower = (
                'borrowernumber' => $borrowernumber,
                'cardnumber'   => $person->{'fsLopenr'},
                'categorycode' => $faculty,
                'branchcode'   => $branchcode,
                'firstname'    => $person->{'fornavn'}, 
                'surname'      => $person->{'etternavn'},
                'email'        => $person->{'epost_intern'},
                'phone'        => $person->{'mobil'},
                'userid'       => $member->userid ? $member->userid : $person->{'brukernavn'},
            );
            eval { $member->set(\%borrower)->store };
            if ( $@ ) {
                say " - FAILED to update ($borrowernumber)" if $verbose;
                $faculty_failed++;
            } else {
                say " - Updated ($borrowernumber)" if $verbose;
                $faculty_updated++;
            }
        } else {
            # Add the borrower
            my %borrower = (
                'cardnumber'   => $person->{'fsLopenr'},
                'categorycode' => $faculty,
                'branchcode'   => $branchcode,
                'firstname'    => $person->{'fornavn'}, 
                'surname'      => $person->{'etternavn'},
                'email'        => $person->{'epost_intern'},
                'emailpro'     => $person->{'epost_ekstern'},
                'phone'        => $person->{'mobil'},
                'userid'       => $person->{'brukernavn'},
            );
            my $patron = Koha::Patron->new(\%borrower)->store;
            $borrowernumber = $patron->borrowernumber;
            # Set default messaging preferences
            C4::Members::Messaging::SetMessagingPreferencesFromDefaults({
                'borrowernumber' => $borrowernumber,
                'categorycode'   => $faculty,
            });
            say " - Inserted as new ($borrowernumber)" if $verbose;
            $faculty_new++;
        }
        set_password_and_notify( $borrowernumber, $person->{'epost_intern'}, $password, $pwnotify );
        $faculty_count++;
        if ( $limit > 0 && $faculty_count == $limit ) {
            last;
        }
    }
}

if ( $students ne '' ) {
    foreach my $person ( @{ $xml->{'student'} } ) {
        print 'S ' . $person->{'fornavn'} . ' ' . $person->{'etternavn'} . ' ' . $person->{'studentnr'} if $verbose;

        $seen_fslopenr{ $person->{'fsLopenr'} }++;
        next if $seen_fslopenr{ $person->{'fsLopenr'} } > 1;

        # This just gets in the way of debugging
        $person->{'studieTilknytninger'} = undef;
        $person = fix_email( $person );
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
                if ( $adr->{'sted'} && length $adr->{'sted'} > 5 ) {
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
        $person = fix_phone( $person );
        # Calculate expiration date
        my $year = substr $person->{'studierettSlutt'}, 0, 4;
        if ( $year eq '9999' ) {
            $person->{'expires'} = $person->{'studierettSlutt'};
        } else {
            my $expires = Time::Piece->strptime( $person->{'studierettSlutt'}, "%Y-%m-%d" );
            $expires = $expires->add_years( 1 );
            $person->{'expires'} = $expires->ymd;
        }
        # Dump all of $person if we are debugging
        say Dumper $person if $debug;
        # Figure out if the borrower already exists
        my $borrowernumber;
        if ( my $member = Koha::Patrons->find({ 'cardnumber' => $person->{'studentnr'} }) ) {
            $borrowernumber = $member->{'borrowernumber'};
            my %borrower = (
                'borrowernumber' => $borrowernumber,
                'cardnumber'   => $person->{'studentnr'},
                'categorycode' => $students,
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
            eval { $member->set(\%borrower)->store };
            if ( $@ ) {
                say " - FAILED to update ($borrowernumber)" if $verbose;
                $student_failed++;
            } else {
                say " - Updated ($borrowernumber)" if $verbose;
                $student_updated++;
            }
        } else {
            # Add the borrower
            my %borrower = (
                'cardnumber'   => $person->{'studentnr'},
                'categorycode' => $students,
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
            my $patron = Koha::Patron->new(\%borrower)->store;
            $borrowernumber = $patron->borrowernumber;
            # Set default messaging preferences
            C4::Members::Messaging::SetMessagingPreferencesFromDefaults({
                'borrowernumber' => $borrowernumber,
                'categorycode'   => $students,
            });
            say " - Inserted as new ($borrowernumber)" if $verbose;
            $student_new++;
        }
        set_password_and_notify( $borrowernumber, $person->{'epost_intern'}, $password, $pwnotify );
        $student_count++;
        if ( $limit > 0 && $student_count == $limit ) {
            last;
        }
    }
}

# Summarize
if ( $verbose ) {
    say "\nFaculty:  $faculty_count ($faculty_new new, $faculty_updated updated, $faculty_failed failed)";
    say "Students: $student_count ($student_new new, $student_updated updated, $student_failed failed)";
}

sub set_password_and_notify {

    my ( $borrowernumber, $email, $password, $pwnotify ) = @_;

    return unless $password;

    my $member = Koha::Patrons->find({ 'borrowernumber' => $borrowernumber });
    # Check password is not set
    if ( $member->password eq '!' ) {
        # Generate password
        my $salt = read_text( $password );
        my $cardnumber = $member->cardnumber;
        my $string = $cardnumber . $salt;
        my $pword = md5_base64( $string );
        $pword = substr $pword, 0, 8;
        my $digest=Koha::AuthUtils::hash_password( $pword );
        # Set password
        my $koha_member = Koha::Patrons->find({ 'borrowernumber' => $borrowernumber });
        if ( $koha_member->update_password( $member->userid, $digest ) ) {
            say "password was set";
        }
        # Send email
        send_email( $email, $member->userid, $pword, $pwnotify );
    }
}

sub send_email {

    my ( $to, $username, $password, $pwnotify ) = @_;
    
    return unless $pwnotify;

    my $from    = 'bibliotek@westerdals.no';
    my $subject = 'Passord til bibibliotekets katalog. Password for library services.';
    my $body    = read_text( $pwnotify );
    
    # Do substitutions on body text
    $body =~ s/__USERNAME__/$username/g;
    $body =~ s/__PASSWORD__/$password/g;
    
    my $email = Email::Simple->create(
        header =>[
            To      => $to,
            From    => $from,
            Subject => $subject
        ],
        body => $body,
    );

    try {
        sendmail( $email, {
            from      => $from,
            transport => Email::Sender::Transport::Sendmail->new
        });
    } catch {
        print "Can't send mail: $_";
    }

}

sub fix_phone {

    my ( $person ) = @_;

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

    return $person;

}

sub fix_email {

    my ( $person ) = @_;

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
            if ( $email->{'type'} eq 'intern' || $email->{'type'} eq 'arbeid' ) {
                $person->{'epost_intern'} = $email->{'content'}
            }
        }
    }
    
    return $person;

}
 
=head1 OPTIONS
 
=over 4
 
=item B<-i, --infile>
 
Name of input file.

=item B<-s, --students>
 
Which categorycode to put students in. Must exist in the Koha you are running
against. If this option is not given, students will not be processed.

=item B<-f, --faculty>
 
Which categorycode to put faculty in. Must exist in the Koha you are running
against. If this option is not given, faculty will not be processed.

=item B<-b, --branchcode>
 
Which branchcode to put popele in. Must exist in the Koha you are running against.

=item B<-p, --password>
 
Create a new password for users that do not have one. The argument to this option 
should be the path to a simple text file that just contains some random (but 
never changing) string that will be combined with sundry other information to 
form the basis of a predictably generated password.

=item B<--pwnotify>
 
Send an email when a new password has been set. The argument to this option should 
be the path to a template file that will be sent out as email. Possible variables:

=over 4

=item * [% username %]

=item * [% password %]

=back

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
my $input_file = '';
my $students   = '';
my $faculty    = '';
my $branchcode = '';
my $password   = '';
my $pwnotify   = '';
my $limit      = 0;
my $verbose    = '';
my $debug      = '';
my $help       = '';
 
GetOptions (
    'i|infile=s'     => \$input_file,
    's|students=s'   => \$students,
    'f|faculty=s'    => \$faculty,
    'b|branchcode=s' => \$branchcode,
    'p|password=s'   => \$password,
    'pwnotify=s'     => \$pwnotify,
    'l|limit=i'      => \$limit,
    'v|verbose'      => \$verbose,
    'd|debug'        => \$debug,
    'h|?|help'       => \$help
);
 
pod2usage( -exitval => 0 ) if $help;
pod2usage( -msg => "\nMissing Argument: -i, --infile required\n",                    -exitval => 1 ) if !$input_file;
pod2usage( -msg => "\nMissing Argument: -s, --students AND/OR -f, --faculty required\n", -exitval => 1 ) if !$students && !$faculty;
pod2usage( -msg => "\nMissing Argument: -b, --branchcode required\n",                -exitval => 1 ) if !$branchcode;
pod2usage( -msg => "\nMissing Argument: -p, --password required\n",                  -exitval => 1 ) if !$password && $pwnotify;
 
return ( $input_file, $students, $faculty, $branchcode, $password, $pwnotify, $limit, $verbose, $debug );
 
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
