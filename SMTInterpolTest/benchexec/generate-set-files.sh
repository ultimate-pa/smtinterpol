#!/bin/bash
declare -A n2p
declare -A recursive

# SMT-LIB benchmarks
n2p["crafted"]="/storage/repos/smtlib/QF_BV/crafted"
n2p["Heizmann2017"]="/storage/repos/smtlib/QF_BV/20170501-Heizmann-UltimateAutomizer"
n2p["Heizmann2019"]="/storage/repos/smtlib/QF_BV/20190429-UltimateAutomizerSvcomp2019"
n2p["bruttomesso"]="/storage/repos/smtlib/QF_BV/bruttomesso"
recursive["bruttomesso"]=1

for set in "${!n2p[@]}"; do 
  if [[ ${recursive[$set]} -eq 1 ]] ; then 
    find "${n2p[$set]}" -iname *.smt2 -exec readlink -f {} \; > bench_${set}.set
  else 
    find "${n2p[$set]}" -maxdepth 1 -iname *.smt2 -exec readlink -f {} \; > bench_${set}.set
  fi
done

