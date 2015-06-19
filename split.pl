#!/usr/bin/env perl

my $out;

while (<ARGV>) {
  if ( /^\\coqdockw{([A-Z].+?)} \\coqdocvar{(.+?)}/ ) {
    my $name = $2;
    $name =~ s/\\_/_/g;
    print "Writing $1 definition $name...\n";
    open $out, '>', "${name}.tex" or die $!;
  }
  print $out $_ if $out;
}
