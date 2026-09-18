# SMTInterpol — Developer Notes

## Build

```
ant compile
```

Compiles all modules. Class files land in per-module `release/` subdirectories:
- `SMTInterpol/release/`
- `Library-SMTLIB/release/`
- `Library-SMTLIBTest/release/`

## Run the solver

```
java -cp "SMTInterpol/release:Library-SMTLIB/release:SMTInterpol/lib/jh-javacup-1.2.jar" \
    de.uni_freiburg.informatik.ultimate.smtinterpol.Main [OPTIONS] [FILE.smt2]
```

Useful options:
- `-v` — verbose/debug output (decisions, backtracking, theory propagation)
- `-q` — quiet mode (suppress INFO messages)
- `-smt2` — read SMT-LIB 2 format (default)

To build a self-contained jar instead: `ant smtinterpol.jar` → `dist/smtinterpol.jar`

## Run tests

```
ant runtests
```

Runs all JUnit tests. Reports land in `testreports/`. Individual test classes are under
`SMTInterpolTest/src/` and `Library-SMTLIBTest/src/`.

## Architecture overview

SMTInterpol follows the DPLL(T) architecture:

1. **SMT-LIB 2 front-end** (`smtlib2/`) — parser and solver API (`SMTInterpol.java`)
2. **Clausifier / preprocessor** (`convert/`) — converts formulas to CNF; key files: `Clausifier.java`, `TermCompiler.java`, `SMTAffineTerm.java`, `EqualityProxy.java`
3. **CDCL engine** (`dpll/`) — core SAT solver with theory hooks via the `ITheory` interface; key files: `DPLLEngine.java`, `Clause.java`, `Literal.java`, `DPLLAtom.java`
4. **Theory solvers** (all implement `ITheory`):
   - `theory/cclosure/` — congruence closure for EUF/equality (`CClosure.java`); array theory (`ArrayTheory.java`) and datatype theory (`DataTypeTheory.java`) are also in this package since they build on CC
   - `theory/linar/` — simplex-based linear arithmetic over rationals/integers (`LinArSolve.java`, `MutableAffineTerm.java`, `LinVar.java`, `BoundConstraint.java`, `CutCreator.java`)
   - `theory/quant/` — quantifier instantiation with e-matching (`QuantifierTheory.java`, `InstantiationManager.java`, subpackages `ematching/` and `dawg/`)
   - `theory/epr/` — EPR theory solver (~51 files, DAWG-heavy); **outdated**, plan is to improve `QuantifierTheory` to subsume it
   - `theory/bitvector/` — bit-vector support via translation to integer arithmetic in the preprocessor (`BvToIntUtils.java`)
5. **Proof generation** (`proof/`) — uses Resolute as the outer proof framework; a simpler hyperresolution-based intermediate representation is used for clause-level proofs (`ProofTracker.java`, `ResolutionNode.java`, `ProofSimplifier.java`, `resolute/`)
6. **Interpolation** (`interpolate/`) — Craig interpolant generation; theory-specific interpolators: `CCInterpolator`, `LAInterpolator`, `ArrayInterpolator`, `DatatypeInterpolator`
7. **Model generation** (`model/`) — satisfying model construction and evaluation (`Model.java`, `ModelEvaluator.java`)

### Library-SMTLIB module

Provides the term data structures shared across all modules: `Term`, `ApplicationTerm`, `TermVariable`, `LetTerm`, `QuantifiedFormula`, `Sort`, `FunctionSymbol`, `Theory.java` (predefined theory symbols), `Logics.java`, `Rational.java`, `TermTransformer`, `NonRecursive`.

## Key source files

- `SMTInterpol/src/de/uni_freiburg/informatik/ultimate/smtinterpol/dpll/DPLLEngine.java` — core DPLL/CDCL engine
- `SMTInterpol/src/de/uni_freiburg/informatik/ultimate/smtinterpol/smtlib2/SMTInterpol.java` — SMT-LIB API entry point
- `SMTInterpol/src/de/uni_freiburg/informatik/ultimate/smtinterpol/theory/linar/LinArSolve.java` — linear arithmetic theory
- `SMTInterpol/src/de/uni_freiburg/informatik/ultimate/smtinterpol/theory/cclosure/CClosure.java` — congruence closure theory

## check-sat-assuming

`check-sat-assuming` is implemented by deciding assumption literals at consecutive decision levels
starting from 1, then setting `mBaseLevel` to the number of assumptions. The assumptions are
tracked in `mAssumptionLiterals` (a `LinkedHashSet`).

Key invariant: all assumption decisions occupy levels 1..mBaseLevel on the DPLL stack.
`mNumSolvedAtoms` counts literals propagated unconditionally at or below mBaseLevel.

`clearAssumptions()` in `DPLLEngine` must be called before each new `check-sat-assuming` call
(and on push/pop/assert). It backtracks all levels > 0 and resets mBaseLevel and mNumSolvedAtoms.

## Other useful targets

- `ant clean` — remove build artifacts
- `ant smtinterpol.jar` — build `dist/smtinterpol.jar`
- `ant javadoc` — generate API docs
