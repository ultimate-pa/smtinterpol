# Piecewise-Constant Models for Quantifiers

Goal: a lightweight model-based quantifier instantiation (MBQI) for the almost
uninterpreted fragment (Ge & de Moura 2009), where the candidate model of every
uninterpreted function is *piecewise constant*, and the same model is what
`get-model` prints after a `sat` answer.

This is a plan, not yet a design document.  It builds on the earlier attempt in
`origin/quantifier_models` (Tanja Schindler, 2021–22, `PiecewiseConstantModel`,
`IterativeModelBasedInstantiation`), which predates offset equalities (see
`offset-equality-plan.md`) and never connected its model to the model output.

## The old branch in brief

* `PiecewiseConstantModel` keeps a trie per function symbol, one level per
  argument: `TreeMap<Rational, …>` for numeric arguments (keyed by the LA model
  value), `HashMap<CCTerm, …>` for uninterpreted ones (keyed by representative).
  Leaves are the CC class of a ground application `f(c1,…,cn)` (a *corner*).
* Lookup of `(a1,…,an)`: numeric levels walk `headMap(ai, true)` descending with
  backtracking, so the result is the lexicographically greatest corner `c` with
  `c ≤ a` componentwise; uninterpreted levels try the exact class, then the
  λ entry.  No corner: λ of the return sort.
* λ (`@0` of the sort) is evaluated as `Rational.NEGATIVE_INFINITY`; an affine
  term with λ-coefficient `k ≠ 0` evaluates to `∓∞`.
* The iterative search walks the grid of interesting terms upwards from the
  all-λ substitution, always jumping to the smallest substitutions falsifying
  the literal that was satisfied.

Known defects to fix when porting: `Rational` compared with `==`
(`evaluateInCC`, select branch; `Rational.equals` is required), values read
via `SharedTermEvaluator` from the representative's flat term (no LinVar ⇒
NPE), no `get-model` integration, symbolic `−∞` default never concretized, and
an undocumented completeness argument for the queue pruning (`addToQueue`).

## Semantics

### Function model

For `f : S1 × … × Sn → S` the model is determined by the set of corners, the
ground applications `f(c)` in the E-graph after the final check:

```
f(a) = value(f(c))  where c = lexmax { c corner | ci ≤ ai for numeric i,
                                                  ci ~ ai or ci = λ for uninterpreted i }
f(a) = λ_S          if no such corner exists
```

`f` is constant on every cell `[t_1, t_1') × … × [t_n, t_n')` of the grid
spanned by the corner coordinates.

### Why grid points suffice

The fragment normalisation in `QuantifierTheory.getQuantInequality` turns
integer `x ≤ t` into `¬(t+1 ≤ x)`; the only arithmetical literals are strict
`x < t`, `t < x`, `x < y` and integer `x = t` (which adds `t ± 1`).  Every
arithmetical literal is therefore either constant on a cell or false at the
cell's left endpoint, so a clause that holds at all grid points holds
everywhere.  This argument must hold for every new interesting-term source we
add (array indices ± 1, offsets).

## Value domain

During MBQI the model is *symbolic*; concrete values are fixed only by
`ModelBuilder` after the last final check.  A numeric value is one of

| kind      | meaning                                         | order                    |
|-----------|-------------------------------------------------|--------------------------|
| `λ`       | a value below every other value (like ε, but negative and large) | smallest |
| concrete  | `rep + offset` with an LA-shared representative (`realValue`)    | by value |
| CC-only   | `rep + offset` with a representative without LA shared term      | above all concrete values; by class order, then offset |

All values are *CC values* `(representative, offsetToRep)`, i.e. exactly
`CCParameter.getValueKey()`.  Two interesting terms with the same value key are
interchangeable; two with different keys but the same concrete value are also
interchangeable for the model (everything is evaluated by value).

### CC-only classes

`ModelBuilder.fillInTermValues` gives classes without shared term a fresh value
larger than everything registered so far.  Comparing such a value with a
concrete one or with λ is sound.  Comparing two different CC-only classes
(corner order of `f(c1)`, `f(c2)`; an EU literal `f(x) ≤ g(y)`) depends on the
order `ModelBuilder` will pick.  Plan: fix a deterministic class order (e.g.
representative age) used by both MBQI and `ModelBuilder`; today the `delayed`
set in `fillInTermValues` is a `HashSet` and must become a sorted list.  This is
sound because the model is rebuilt at every final check.

Fallback, if this turns out to be fragile: treat such comparisons as unknown
and instantiate, which makes the terms LA-shared.

### λ

For reasoning, λ is just an arbitrary constant: any instance with λ is a valid
instance, and unsat proofs never use that it is small.  Smallness is a pure
model-construction assumption, so it must hold at the end without the solver
ever having been told.  Invariants:

* **CC only.**  A numeric λ never gets an LA shared term.  Otherwise LA assigns
  it a concrete value, MBTC compares it, and nothing keeps it small.
* **Singleton class.**  A constant's CC class can only grow through an equality
  atom mentioning it, so it suffices that no atom mentions λ (no `CCEquality`,
  no LA bound).  `f(λ)` is an ordinary term and may be equal to anything.
* **Instances.**  `SubstitutionHelper` evaluates arithmetical literals with
  λ instead of building atoms: `λ = t` and `t < λ` are false, `λ < t` is true,
  `λ < y` with `y := λ` is false.  λ under an offset (`f(x + k)` with
  `x := λ`) or inside any other arithmetic is rejected.  On master none of this
  is checked yet: `QuantUtil.isLambda` exists but `SubstitutionHelper` does not
  use it.
* **Arrays (to verify).**  An Int-indexed `select(a, λ)` / `store(a, λ, v)`
  lets the array theory create index equalities `λ = j`, which the DPLL engine
  may set to true.  Either never instantiate numeric array indices with λ, or
  make sure the array lemmas never introduce such atoms.
* **Not in the input.**  λ is currently `@0` of its sort, i.e. the model-value
  symbol (`Theory.getModelValueSymbol`, pattern `@\d+`), and `TermCompiler`
  lets `@0` through.  So `(as @0 Int)` in the input (e.g. a round-tripped
  model) is λ.  Plan:
  * Rename λ to `@lambda`.  This removes the clash with the model element `@0`
    that `FiniteSortInterpretation` prints for uninterpreted sorts.
    `QuantUtil.isLambda` changes accordingly.
  * The theory can only build the term if the symbol is defined, so declare it
    like `@diff`: a polymorphic constant
    `declareInternalPolymorphicFunction(theory, "@lambda", X, [], X,
    UNINTERPRETEDINTERNAL | RETURNOVERLOAD)` in `SMTInterpol`'s solver setup for
    quantified logics, so `(as @lambda Int)` resolves.  `UNINTERPRETEDINTERNAL`
    makes `isInterpreted()` false, so the model and the proof checker treat it
    as an uninterpreted constant.  Being in the function factories, the name
    cannot be declared by the user any more.
  * `ProofRules` must declare it too, the way it declares `@diff` "in case
    SMTInterpol is not running", since instances in proofs contain λ.  (Today
    a proof prints λ as `(as @0 Int)`, which a checker reads as a model value.)
  * Every symbol in the theory can be referenced by name, so the input must be
    checked anyway: `SMTInterpol.assertTerm` and `checkSatAssuming` reject terms
    containing λ.  Since the symbol is always defined, this is a DAG walk with a
    visited set on every input term, unless it is folded into a traversal the
    input already gets (e.g. an input-mode flag on `TermCompiler`, see below).
    This also covers terms built through the Java API.  `get-value` may allow
    it, since evaluation does not feed the solver.
  * The check cannot go into `TermCompiler` unconditionally: `SubstitutionHelper`
    and `DestructiveEqualityReasoning` compile instances, which contain λ,
    through it.  An input-mode flag would distinguish the two callers.  Its `case "@0"` goes away, so
    numeric `(as @n Int)` is uniformly rejected as an unsupported internal
    function.

### λ in proofs

λ enters proofs as an instantiation term: `(forall- ((as @0 Int)) …)`.  That
step is valid for any ground term, and today nothing else about λ is used.
There are no rules for `λ < t`, and none are needed as long as smallness is
only used to *skip* instances (a literal `λ < t` is true, so the instance is
trivially true and not built; skipping needs no proof).

Smallness is used for reasoning as soon as an instance is *strengthened*:
dropping `λ = t` or `t < λ` as false turns `λ = t ∨ φ(λ)` into `φ(λ)`, which
needs `λ ≠ t`.  This is the case MBQI needs, because the alternative (keeping
the atom) violates the singleton invariant.  The proof then has to fix λ:

* Resolute supports `define-fun` inside proofs (`ProofRules.defineFun`,
  checked by `MinimalProofChecker`).  Define
  `@lambda := (min t_1 … t_n) − 1` as an `ite` chain, where `t_i` are the
  λ-free terms of all strengthening steps in the proof (known when the proof is
  printed).  Each `λ < t_i` then follows from `:expand`, `:ite1`/`:ite2` and
  `farkas`.  If no step uses smallness, `declare-fun` is enough.
* The `t_i` must be λ-free, otherwise the definition is circular (`f` is
  uninterpreted in the proof, so `λ < f(λ)` cannot be justified, although it
  holds in the piecewise model where `value(f(λ))` does not depend on the
  concrete λ).  Ground sides of arithmetical literals come from the clause and
  are λ-free; a variable bound `y < x` with `y := f(λ)`, `x := λ` is not.  For
  those either skip strengthening (and instantiate differently), or only
  allow λ-free interesting terms opposite λ.
* The old branch gets this wrong.  Its `normalizeAndSimplifyLitTerm` rewrites
  every arithmetical literal with a λ-substituted variable by an unjustified
  `:intern` step, also when the other side contains λ.  Counterexample
  (satisfiable with `f(x) = x − 1`, `h(x,y) = ite(y = x − 1, 0, 1)`), answered
  `unsat` by all three `:quant-fc-method`s on `origin/quantifier_models`:

  ```
  (declare-fun f (Int) Int)
  (declare-fun h (Int Int) Int)
  (assert (forall ((x Int) (y Int)) (or (< y x) (= (h x y) 1))))
  (assert (forall ((x Int)) (= (h x (f x)) 0)))
  ```

  `x := λ` in the second clause creates `h(λ, f(λ))`; `f(λ)` becomes
  interesting for `y`, and the instance `x := λ, y := f(λ)` of the first
  clause drops `f(λ) < λ` as false (proof: `(= (<= (+ @0 (- (f @0))) 0) true)
  :intern`), leaving `h(λ, f(λ)) = 1`.  Master (λ as a plain constant) times
  out instead.  This must become a regression test.

  A sat proof of the counterexample in the `refine-fun` format, accepted by
  `proof.checker.Main` (`valid`, 14 axioms, 13 resolutions):

  ```
  sat
  ((refine-fun f ((z Int)) (+ z (- 1)))
  ((refine-fun h ((a Int) (b Int)) (ite (= b (+ a (- 1))) 0 1))
  (let ((A1 (forall ((x Int) (y Int)) (or (< y x) (= (h x y) 1))))
        (A2 (forall ((x Int)) (= (h x (f x)) 0))))
  (let ((sx (choose (x Int) (not (forall ((y Int)) (or (< y x) (= (h x y) 1)))))))
  (let ((sy (choose (y Int) (not (or (< y sx) (= (h sx y) 1)))))
        (s  (choose (x Int) (not (= (h x (f x)) 0)))))
  (let ((C1 (= sy (+ sx (- 1)))) (H1 (h sx sy)))
  (let ((ITE1 (ite C1 0 1)) (L1 (< sy sx)) (L2 (= H1 1)))
  (let ((B1 (or L1 L2))
        (F (f s)))
  (let ((H2 (h s F)) (C2 (= F (+ s (- 1)))))
  (let ((ITE2 (ite C2 0 1)))
  (let ((B2 (= H2 0)))
  (let-proof (
    ; {L2, C1}: if the ite condition is false, h(sx,sy) = 1
    (pL2 (res (= H1 ITE1) (expand H1)
           (res (= ITE1 1) (ite2 ITE1) (trans H1 ITE1 1))))
    ; {L1, ~C1}: if sy = sx - 1, then sy < sx
    (pL1 (res (<= sx sy) (total sx sy) (farkas 1 (<= sx sy) 1 C1)))
    ; {B2}: h(s, f(s)) = 0, since f(s) = s - 1
    (pB2 (res (= H2 ITE2) (expand H2)
           (res (= ITE2 0) (res C2 (expand F) (ite1 ITE2)) (trans H2 ITE2 0)))))
  (let-proof (
    (pB1 (res L2 (res L1 (res C1 pL2 pL1) (or+ 0 B1)) (or+ 1 B1))))
  (res A1 (res B1 pB1 (forall+ A1))
    (res A2 (res B2 pB2 (forall+ A2))
      (and+ (and A1 A2)))))))))))))))))
  ```
* Satisfiability argument (why this is sound even without the definition):
  for finitely many λ-free `t_i`, adding `λ < t_i` for a fresh λ preserves
  satisfiability.  The definition just makes this checkable with existing
  rules.

*Status (2026-10-22).*  λ is the polymorphic internal constant `@lambda`
(`SMTInterpolConstants.LAMBDA`, `UNINTERPRETEDINTERNAL | RETURNOVERLOAD`),
declared by `SMTInterpol` for quantified logics and by `ProofRules` for the
external checker.  `LambdaBound.analyze` recognizes a normalized ground atom
`(<= P 0)` or numeric `(= L R)` in which λ occurs only as a linear summand
`k·λ`; `SubstitutionHelper.evaluateLambdaBound` rewrites it to its value
(`<=` true iff `k > 0`, `=` false) with the new rewrite `:lambdaBound`, so
no atom with λ is built and `λ < t` instances are skipped as true.  Other
atoms with λ (e.g. `f(λ) < λ`) are still built.  `ProofSimplifier` collects
the bounds of all `:lambdaBound` steps (`-q`, plus `0` if `c > 1`, or `-q/c`
if `c < 1`, where `Q = c·λ + q` is the atom times the sign of `k`), defines
`λ := min(b_j - 1)` as an `ite` chain through `mAuxDefs` (so the definition
is innermost), and proves each step with one `farkas` over `-Q` and the facts
`λ <= b - 1`.  `PrintProof` prints plain names in `define-fun` heads and
`ProofParser` reuses the polymorphic `@lambda` instead of declaring it.
Checked with `proof.checker.Main` on Int, Real (`c < 1`, `c > 1`) and an
uninterpreted λ, and on equalities with positive and negative `k`; tests in
`LambdaProofTest` (the equality tests also check that the full proof
contains a `:lambdaBound` rewrite of an equality).  The parser accepts `@lambda`
(proofs use it), but `TermCompiler.transformInput`, used by the `Clausifier`
for assertions and all-sat literals, rejects it as an unsupported internal
function; instances with λ use the normal `transform`.

### Concretization

Concretization after the last final check, analogous to ε (`ModelBuilder` must
special-case λ; today it would land in `delayed` and get a large fresh value):

* argument position: `λ < min` over all numeric corner coordinates, including
  their offset ranges (`ModelBuilder.mMinOffset`);
* return position: for every evaluated affine term `k·λ + r` the sign must be
  preserved.  With `M` the largest absolute model value or literal constant,
  `K` the largest sum of absolute coefficients in a quantified literal, and
  `k_min` the smallest non-zero absolute λ-coefficient, `λ < −(K·M + 1)/k_min`
  suffices (`k_min ≥ 1` for Int).

## Interesting terms as CCParameters

### Current state (master)

* `QuantEquality` / `QuantBoundConstraint` store only `Term`s / a `Polynomial`;
  there is no `CCParameter`.
* `getQuantEquality` / `getQuantInequality` call `addGroundCCTerms`, which
  creates a CCTerm for every ground offset-free subterm that needs one.  So for
  `x = c + 5` the CCTerm of `c` exists, and `getCCParameter(c + 5)` is
  `(c, 5)`.  For a multi-summand `t = a + b` there is no CCTerm for `t` (the
  summands `a`, `b` get CCTerms, but not necessarily LA shared terms).
* `QuantClause.collectVarInfos` builds `t ± 1` as new `Polynomial` terms; the
  store-index case in `updateInterestingTermsForFuncArgs` does the same.  With
  offset equalities `getRepresentativeTerm` already maps them back to
  `(c, k ± 1)`, so no CCTerm is created, but this is implicit.
* `addAllInteresting` dedups by `getRepresentativeTerm`, i.e. by CC value key —
  but not by concrete value.

### Plan

1. Compute the `CCParameter` of the ground side once when the literal is
   created (`QuantEquality.getRhsParam()`, and the bound term of an
   arithmetical `QuantBoundConstraint`); `t ± 1` becomes
   `CCParameter.of(rhs.getCCTerm(), rhs.getOffset() ± 1)` without building a
   term.  Same for store indices ± 1.
2. Ground sides that are not `term + constant` (e.g. `a + b`): decided
   (2026-10-20), the ground side becomes a `CCParameter` and is shared with LA
   at literal creation, so its value is concrete and comparable.  This only
   adds unconstrained LinVars.
3. Interesting terms become values: keyed by `getValueKey()`.  Merging by
   concrete value only happens in the final check, which the model-based check
   runs in, so it can assume the merge already happened.

*Implementation status (2026-10-20).*  Items 1 and 2 are done:
`QuantifierTheory.createGroundBound` builds the ground side's `CCParameter`
(via `Clausifier.createCCTerm` on the canonical polynomial, which shares sums
with LA through `addTermAxioms`) and stores it on the atom
(`QuantLiteral.getGroundBound()`, copied by `getLiteralCopies`).
`QuantClause.collectVarInfos` takes the bounds from it, and `t ± 1` for
`x = t` and for store indices is `QuantifierTheory.getOffsetTerm`, i.e.
`CCParameter.of(cc, offset ± 1)` with offset equalities (canonical
`unifyPolynomial` term without).  The substitutions themselves stay `Term`s:
`InstantiationManager` keys its DAWGs, age order and instance caches by
`Term`.

### Use sites in model production

The quantified literals reference CC classes at offsets that no ground term
uses: `x = c + 5` gives `c+4`, `c+5`, `c+6`.  These must be registered as use
sites in `ModelBuilder` (`updateOffsetRange`), otherwise a fresh value can land
inside the range MBQI assumed to be free.

Failure scenario without it: `c` and `d` are CC-only, MBQI orders `c < d`, so
`c + 6 < d` symbolically, and a ground corner `f(d)` exists.  `ModelBuilder`
picks `value(c) = 10`, `value(d) = 16` (it only knows the ground use sites of
`c`), so `c + 6 = d` and `f(c + 6)` is now `f(d)`, not the value MBQI checked
the clause instance for `x := c + 6` against.

Likewise the concrete values of LA-only interesting terms (case 2 above, if
they are not shared) must be registered in `NumericSortInterpretation`, so that
fresh CC-only values are chosen above them.  In the ground case this never
mattered, since a CC-only term is never compared with an LA term.

## Placement

* **CC side** (`theory/cclosure`): `PiecewiseModel` built from `CClosure`
  after the final check, with the symbolic value domain above; it replaces
  the old branch's `PartialFunction` trie and is queried by the quantifier
  theory.  Arrays: weak-representative models as in the old
  `buildArrayModelWeakRep`.
* **Model output**: `FunctionValue` gains a step representation;
  `getDefinition` prints `ite` chains with `>=` conditions (numeric levels) and
  `=` conditions (uninterpreted levels); `ModelEvaluator` evaluates the same
  structure.  `ModelBuilder` concretizes λ and CC-only classes in the order
  MBQI used.
* **Quantifier side** (`theory/quant`): literal evaluation in the model, the
  iterative search, `:quant-fc-method` option.

*Implementation status (2026-10-20).*  `theory/cclosure/PiecewiseModel`
implements the function model for uninterpreted functions with the symbolic
value domain (`PiecewiseModel.Value`): lambda, concrete (the representative's
LA shared term, evaluated like `ModelBuilder` does), and CC-only values ordered
by the creation index of the representative in `CClosure.mAllTerms`, then by
offset.  This is the order in which `ModelBuilder.fillInTermValues` meets the
representatives, so making its `delayed` set a list (Step 4) gives the same
order.  Lambda is recognised as the class of the CCTerm the caller supplies
per sort.  Unit tests: `PiecewiseModelTest` (ported Int tests, CC-only order,
uninterpreted arguments).

Arrays (`PiecewiseModel.evaluateSelect`): the weak representative of each
weak equivalence class gets a piecewise-constant model whose corners are its
`mSelects` (the selects whose weak-i representative it is); below the smallest
corner the value is the class default (const value, the value
`computeWeakeqExt` fixed for finite sorts, or λ).  Every other array is the
weak representative with the stores on its primary path applied on top: at a
store index whose weak-i representative is not the weak representative, the
value is that weak-i class's select, or λ if it has none.  Extensionality is
left to the array theory (it adds a `diff` witness for arrays it considers
different).  Consequences for Step 3:

* Which node is the weak representative depends on edge inversion, so the
  model of an array `a` can step at the index of a select on a weakly
  equivalent array.  The interesting terms of an index variable in
  `select(a, x)` must therefore include the select indices of the whole weak
  class, not only those on `a`, besides the store indices ± 1.
* `store(a, x, v)` with a quantified index or value has no CC class; its
  selects must be evaluated symbolically (`x = y ? v : select(a, y)`).
* `ModelBuilder`'s array output (Step 4) has to produce the same model
  (piecewise default instead of a fresh array with point stores).

## Steps

1. Interesting terms as `CCParameter`s on the literals; dedup by value (no
   behaviour change for the enumerative final check).
2. `PiecewiseModel` on the CC side with symbolic values; unit tests ported
   from `PiecewiseConstantModelTest`.
3. Model-based final check (non-iterative variant first), using the
   `Rational.equals` and LinVar fixes.
4. `ModelBuilder`/`FunctionValue`: piecewise output, quantifier use-site
   offsets, deterministic CC-only order, λ concretization.  Check models of
   `sat` quantified benchmarks with the model checker.
5. Iterative search; write down (or fix) the completeness argument for the
   queue pruning before enabling it.

*Step 3 status (2026-10-20).*  Option `:quant-fc-method` (`enumerative`,
default, or `model_based`).  With `model_based`,
`InstantiationManager.instantiateSomeNotSat` builds a `QuantModelEvaluator`
(and with it a `PiecewiseModel`) per final check and walks the interesting
substitutions by age, always from age 0, since the model changes between
final checks.  A clause instance that is true in the model is skipped; the
first one false in the model is instantiated (if its ground instance is not
already satisfied); instances the model cannot decide are tried after those
of the same age.  `QuantModelEvaluator`:

* evaluates uninterpreted functions, `@AUX` predicates (as uninterpreted
  predicates; their defining clauses are checked too), `select` (with
  quantified `store`s evaluated symbolically), `ite`, and Boolean connectives;
* evaluates arithmetic as a symbolic sum `r + Σ k_c·c + k_λ·λ` over CC-only
  classes `c`.  The sign is decided if λ occurs (λ dominates), with no or one
  CC-only class, or with two classes with opposite coefficients (the later
  class dominates, as in `Value.compareTo`); otherwise the literal is unknown;
* reads ground values through `CClosure.getCCParamRep` (CC value) or the LA
  shared term (`LASharedTerm` + `realValue`, no `SharedTermEvaluator` on terms
  without LinVar);
* treats array equalities between different classes, non-linear arithmetic,
  and other interpreted functions as unknown;
* keeps λ symbolic (smallest value) only while its class is a singleton
  without shared term; otherwise λ is read like any other ground term;
* returns from the final check without building a model while LA's model-based
  theory combination still has pending suggestions or propagations
  (`LinArSolve.hasPendingSuggestions`): `DPLLEngine.checkConsistency` only
  stops at a theory that produces new atoms, so the quantifier final check
  would otherwise see classes that MBTC is about to merge.

Still missing: atoms where λ is compared with terms containing λ (`f(λ) < λ`)
are still built, so such an instance can give λ an LA value; the counterexample
above then times out instead of answering `unsat` (accepted for now; the
λ-free case is done, see "λ in proofs").  If the model cannot decide some
instance, `check-sat` answers `unknown` instead of `sat`.  `get-model`
(Step 4) is open.  Tests: `QuantModelBasedTest`.

## Open questions

* Is the CC-only class order stable enough across final checks, or does it
  cause instance churn?
* Offsets in function arguments (`f(x + k)`, Ge & de Moura's shifting) are now
  representable as `CCParameter`s; do we extend the fragment?
* Interaction with the sat-proof records (`modelproofs` branch): a checkable
  model for quantified formulas needs the piecewise definitions.
