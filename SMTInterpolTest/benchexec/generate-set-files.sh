#!/bin/bash
declare -A n2p
# declare -A recursive

# SMT-LIB benchmarks
n2p["crafted"]="/storage/repos/smtlib/QF_BV/crafted"
n2p["Heizmann2017"]="/storage/repos/smtlib/QF_BV/20170501-Heizmann-UltimateAutomizer"
n2p["Heizmann2019"]="/storage/repos/smtlib/QF_BV/20190429-UltimateAutomizerSvcomp2019"
n2p["bruttomesso"]="/storage/repos/smtlib/QF_BV/bruttomesso"
n2p["tacas07"]="/storage/repos/smtlib/QF_BV/tacas07"
n2p["bmc-bv"]="/storage/repos/smtlib/QF_BV/bmc-bv"
n2p["bmc-bv-svcomp14"]="/storage/repos/smtlib/QF_BV/bmc-bv-svcomp14"
n2p["challenge"]="/storage/repos/smtlib/QF_BV/challenge"
n2p["20200415-Yurichev"]="/storage/repos/smtlib/QF_BV/20200415-Yurichev"
n2p["2017-BuchwaldFried"]="/storage/repos/smtlib/QF_BV/2017-BuchwaldFried"
n2p["galois"]="/storage/repos/smtlib/QF_BV/galois"
n2p["pipe"]="/storage/repos/smtlib/QF_BV/pipe"
n2p["20170531-Hansen-Check"]="/storage/repos/smtlib/QF_BV/20170531-Hansen-Check"
n2p["pspace"]="/storage/repos/smtlib/QF_BV/pspace"
n2p["uum"]="/storage/repos/smtlib/QF_BV/uum"
n2p["brummayerbiere"]="/storage/repos/smtlib/QF_BV/brummayerbiere"
n2p["sage-app10"]="/storage/repos/smtlib/QF_BV/sage/app10"
# recursive["bruttomesso"]=1

for set in "${!n2p[@]}"; do 
  # if [[ ${recursive[$set]} -eq 1 ]] ; then 
    find "${n2p[$set]}" -iname *.smt2 -exec readlink -f {} \; > sets/bench_${set}.set
  # else 
  #   find "${n2p[$set]}" -maxdepth 1 -iname *.smt2 -exec readlink -f {} \; > sets/bench_${set}.set
  # fi
done

