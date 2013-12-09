#!/bin/bash

find SMTInterpol* -name 'Parser.java' -prune -o -name 'Lexer*.java' -prune -o -name '*.java' -print | xargs grep -L GNU
find Library-SMTLIB -name '*.java' | xargs grep -L GNU
find DeltaDebugger -name '*.java' | xargs grep -L GNU

