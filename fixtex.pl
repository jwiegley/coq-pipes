undef $/;

while (<ARGV>) {
    s/(\\coqdocemptyline\n)*\\coqdocnoindent\n$//;
    print $_;
}
