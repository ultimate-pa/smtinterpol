#!/bin/bash
# Load SDKman to switch Java versions 
source "/root/.sdkman/bin/sdkman-init.sh"

TOOL_DIR="/storage/repos/smtinterpol"
BENCH_BASE="$( cd "$( dirname "${BASH_SOURCE[0]}" )" &> /dev/null && pwd )"
RESULT_DIR="${BENCH_BASE}/results/"
OPTS=()

echo "Running Benchexec for SMTInterpol"
sdk use java 8.0.275.open-adpt
pushd "${TOOL_DIR}" > /dev/null
version=$(ant get-version | grep -oP "Version is \K.*")
ant
jar_file="smtinterpol-${version}.jar"
cp dist/${jar_file} smtinterpol.jar
if [ ! $? -eq 0 ] ; then echo "could not copy smtinterpol.jar" ; exit 1 ; fi 
/storage/repos/benchexec/bin/benchexec --no-container --no-compress-results --maxLogfileSize=-1 --numOfThreads=14 -o "${RESULT_DIR}" "${BENCH_BASE}/defs/bv-preprocessing-tests.xml"
popd > /dev/null

#/storage/repos/benchexec/bin/table-generator "${RESULT_DIR}/"'*.BV.SMT-LIB.xml' -x "${BENCH_BASE}/td-bitvectors.xml" -o "$RESULT_DIR"