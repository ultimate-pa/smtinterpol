#!/bin/bash
# Load SDKman to switch Java versions 
source "/root/.sdkman/bin/sdkman-init.sh"

BENCH_BASE="/storage/repos/smtinterpol/bench"
RESULT_DIR="${BENCH_BASE}/results/"
OPTS=()

echo "Running Benchexec for SMTInterpol"
sdk use java 8.0.275.open-adpt
pushd /storage/repos/smtinterpol > /dev/null
/storage/repos/benchexec/bin/benchexec --no-container --no-compress-results --maxLogfileSize=-1 --numOfThreads=14 -o "${RESULT_DIR}" "${BENCH_BASE}/def_smtinterpol.xml"
popd > /dev/null
/storage/repos/benchexec/bin/table-generator "${RESULT_DIR}/"'*.BV.SMT-LIB.xml' -x "${BENCH_BASE}/td-bitvectors.xml" -o "$RESULT_DIR"