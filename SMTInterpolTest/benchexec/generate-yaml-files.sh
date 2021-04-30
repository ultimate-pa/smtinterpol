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
  out="bench_${set}.set"
  if [[ ${recursive[$set]} -eq 1 ]] ; then 
    find "${n2p[$set]}" -iname *.smt2 -exec readlink -f {} \; > "$out"
  else 
    find "${n2p[$set]}" -maxdepth 1 -iname *.smt2 -exec readlink -f {} \; > "$out"
  fi

  # generate .yaml files 

  rm tmp-file

  while read -r line ; do
    verdict=$(grep -oPi "set-info :status \K.*" "$line" | sed s:\)::)
    if [ "$verdict" == "sat" ]; then 
      bverdict="true"
    elif [ "$verdict" == "unsat" ]; then 
      bverdict="false"
    else
      bverdict="unknown"
    fi

    yaml="$line".yml
    echo "$line".yml >> tmp-file

    filename=$(basename "$line")

    cat << EOF > "$yaml"
format_version: '2.0'

input_files: '$filename'

properties:
  - property_file: /storage/repos/smtinterpol/bench/smt.prop
    expected_verdict: $bverdict
EOF

  done < "$out"

  mv tmp-file "$out"

done



