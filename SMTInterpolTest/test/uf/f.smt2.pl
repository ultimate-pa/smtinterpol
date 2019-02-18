#!/usr/bin/perl

$i = shift @ARGV;
$k = (shift @ARGV) || 1;
if (shift @ARGV) {
   print "(set-option :print-terms-cse false)\n";
}

$unsat = $i % $k == 0;
$status = $unsat ? "unsat" : "sat";
$artifact = $unsat ? "proof" : "model";

print <<"EOF";
(set-option :print-success false)
(set-option :produce-proofs true)
(set-option :proof-check-mode true)
(set-option :produce-models true)
(set-option :model-check-mode true)
(set-option :verbosity 3)
(set-info :status $status)
(set-logic QF_UFLIA)
(declare-fun f (Int) Int)
(declare-fun x () Int)
(assert (and 
EOF

print "  (= x ";
for ($j = 0; $j < $k; $j++) {
    print "(f ";
}
print "x";
for ($j = 0; $j < $k; $j++) {
    print ")";
}
print ")\n";

print "  (not (= x ";
for ($j = 0; $j < $i; $j++) {
    print "(f ";
}
print "x";
for ($j = 0; $j < $i; $j++) {
    print ")";
}
print "))\n";

print <<"EOF" ;
))
(check-sat)
(get-$artifact)
(exit)
EOF
