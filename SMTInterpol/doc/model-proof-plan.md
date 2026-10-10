# Model Proofs (sat-proof tracking) — Implementation Plan

## Goal

Track proofs not only for `unsat` but also for `sat`.  For `unsat` the clausifier
tracks *why each clause follows from the input*.  For `sat` we need the opposite
direction: *why the input follows from the clauses*.  Together with the model,
which shows that every clause is true, this yields a proof that the input
formula is satisfiable.

## What already exists

- `model/ModelProver.java` — builds a model proof by *evaluating* the asserted
  formulas in the model: `buildModelProof(assertions)` returns a proof of the
  unit clause `{(and a1 ... an)}`, prefixed with `refineFun` for every function
  defined by the model.  Used from `SMTInterpol.getProof()` (line 820ff) when
  the status is `SAT`.
- `MinimalProofChecker.checkModelProof(proof)` — the checker for that format:
  strip the `refineFun` prefix, then the proof must prove exactly the unit
  clause `{(and <assertions>)}`.  Reachable from the standalone checker
  (`proof/checker/CheckingScript.java:240`).

Limitations of the evaluating approach, which this feature fixes:

1. **Quantifiers are unsupported** — `ModelProver` throws
   *"Quantifiers not supported in model proofs"* (`ModelProver.java:397`).
2. It re-does the whole Boolean structure of the input on formula level, even
   though the clausifier has already decomposed it.
3. It needs the model to evaluate whole formulas, not just atoms.

The clause-based construction keeps the same **output format** (a proof of
`{(and <assertions>)}` under a `refineFun` prefix), so the checker, the
`get-proof` plumbing and the tests stay reusable.  Model evaluation is still
needed, but only for **atoms**.

## The four tracked artifacts

Every clause `C` gets a **target** `T_C`: a clause (a set of literals, never an
`(or ...)` formula — see "Literal vs. clause" in "The aux-clause contract") that
is fixed when `C` is created and that `C`'s record proves from whichever literal
the model sets true.  For an input clause the target is the single literal `{ψ_C}`,
the disjunction of the clause's disjuncts as they were when the clause was created.
All tracked proofs are ordinary Resolute clause proofs; a record combines its
hypotheses' targets by resolution — when every target is a single literal `ψ_j`,
that is the familiar start proof `{¬ψ_1, ..., ¬ψ_m, ρ}` resolved with the hyps,
so no separate hypothesis or placeholder mechanism is needed.

1. **Per input assertion** (`Clausifier.addFormula`): a record concluding `{φ}`
   from the targets `{ψ_i}` of the clauses created from `φ`.
2. **Per clause** (`BuildClause`): the target `T_C`, plus for every literal `l`
   of the clause a proof of `{¬l} ∪ T_C` ("this literal implies the target"), or
   nothing when `l ∈ T_C`.  It is composed of the *reversed* intern/rewrite clause
   from the DPLL literal to the term it came from, and the step from that term to
   the target — for an input clause the `or+` duals of `CollectLiteral`'s
   inlining, for an aux clause the per-literal proof supplied by
   `createDefiningClausesForLiteral`.

   **`T_C` is fixed when the clause is created** and everything the clausifier
   does afterwards (literal rewriting, `or`/`=>`/`and` inlining, interning) is
   absorbed into these per-literal proofs.  That is what lets the consumers of
   `T_C` (artifacts 1 and 3) be built at clause-creation time, before the literals
   are collected.  For an inlined disjunct `(or x y)` the entry for literal `x` is
   `{¬x, (or x y)}`, one extra `or+` step.
3. **Per auxiliary literal** (`Clausifier.createAnonLiteral`,
   `createQuantAuxTerm`, `QuantifierTheory.createAuxLiteral`): a record proving
   that the aux literal `ρ` is true — as an SMT-LIB formula, i.e. the subformula
   it stands for — from the targets of its aux clauses.  Examples (all in "The
   aux-clause contract"):
   - `ρ = (and a b c)`, aux clauses `{¬ρ, a}`, `{¬ρ, b}`, `{¬ρ, c}` with targets
     `{a}`, `{b}`, `{c}`; the record is the `and+` tautology
     `{ρ, ¬a, ¬b, ¬c}` resolved with the three.
   - `ρ = (or a b)`, one aux clause `{¬ρ, a, b}` with target `{ρ}` (the literal
     `(or a b)`, not the clause `{a, b}`) and per-literal proofs `or+`
     `{ρ, ¬a}`, `{ρ, ¬b}`: the record is just that clause's.
   - `ρ = (ite c a b)`: see the worked example below.

   No fresh symbol and no `defineFun` is involved for ground aux literals: a
   `NamedAtom`'s `getSMTFormula` returns the subformula itself, so the assertion
   proof (artifact 1) assumes the *subformula*, and the aux record proves exactly
   that.  Which polarity of the definition was added lazily is therefore
   irrelevant.

   For quantified aux terms (`createQuantAuxTerm`) the existing `@AUX` machinery
   is reused as is.  The fresh function symbol from
   `Theory.createFreshAuxFunction` is kept in the proof — it is needed because
   congruence closure works on these functions as terms — and is expanded to its
   definition only where a proof step needs the definition.  Everything for that
   exists: `FunctionSymbol.getDefinition()`/`getDefinitionVars()`,
   `ProofRules.expand`, the `let`/`unlet` expansion in `ProofSimplifier`
   (line 4509), the `defineFun` wrapping from `mAuxDefs` (line 4900ff), and
   definition expansion in `MinimalProofChecker` (line 224ff).
4. **Per quantified clause** (`QuantClause`): a proof that the target follows
   from the universal closure of its clause formula, and a proof of that closure
   from the model.  See "Quantified clauses and free variables".

### Why clause formulas and not clause arrays

The alternative is to record the clause as an *array* of disjuncts and let the
proofs resolve over its literals directly.  That saves the `orElim`/`orIntro`
bridging (one tautology step per clause and per picked literal), but an array
cannot be a negative literal, so it needs a placeholder leaf (an oracle) plus a
substitution pass at assembly time, and the substituted subclauses then make
resolution steps vacuous — `MinimalProofChecker.walkResolution` warns
`"Could not find pivot"` — which has to be avoided with a subsumption-aware
`res` helper or cleaned up afterwards.

With clause formulas none of that arises: every tracked artifact is a complete,
independently checkable clause proof with **no oracle and no warning**, and
assembly is plain resolution.  The price is that a record proves the more general
lemma "if the clause formulas hold then `ρ`", so all branches of a case split stay
in the proof even when the model only realizes one — a bounded size overhead
(proportional to the clause set), not an exponential one.  Chosen for the
simplicity; see "No vacuous resolutions by construction" below.

## Key observation: rewrite proofs are already bidirectional

The rewrite proofs the clausifier builds (`FN_REFL`, `FN_REWRITE`, `FN_TRANS`,
`FN_CONG`, `FN_QUANT`, `FN_MATCH`) prove **equalities**.  `ProofSimplifier`
turns such a subproof into a proof of the unit clause `{(= lhs rhs)}` and then
applies `iffElim2` to get `{¬lhs, rhs}` (`ProofSimplifier.convertMP:4338`).
Using `iffElim1` on the very same subproof gives `{¬rhs, lhs}`.

Consequence: **no rewrite has to be tracked twice.**  `TermCompiler`,
`LogicSimplifier`, `SMTAffineTerm`, `BvToIntUtils`, `EqualityProxy` and all
`intern` steps need no changes at all; only a "reverse" variant of
`IProofTracker.rewriteToClause` is required.

What genuinely needs new tracking is the **resolution/structural** part: the
CNF decomposition (`AddAsAxiom`, `BuildClause`, `CollectLiteral`), the aux
definitions, and the quantifier handling.  Each structural step has a dual rule
that already exists in `ProofConstants`/`ProofRules`: `or-`/`or+`, `and-`/`and+`,
`=>-`/`=>+`, `ite-i`/`ite+i`, `xor-i`/`xor+i`, `forall+`/`forall-`,
`orIntro`/`orElim`, `andIntro`/`andElim`, `forallIntro`/`forallElim`.

Prerequisite (one task): audit that every `RW_*` rule used by the clausifier is
an equivalence, not just an implication.  `RW_AUX_INTRO` is the suspicious one —
it introduces an aux function symbol and is handled via `defineFun` in
`ProofSimplifier` (`mAuxDefs`, line 4900ff), so the reverse direction exists,
but the aux-literal records (artifact 3) are what actually justify it.

## Worked example: aux axioms for a Boolean `ite`

Input `(assert (or (ite c a b) d))` with `c`, `a`, `b`, `d` Boolean constants.
The clausifier creates an aux literal `l` for `ρ = (ite c a b)`; since the
occurrence is positive, `addAuxAxioms(ρ, true, …)` calls
`createDefiningClausesForLiteral(¬l, ρ, negative=true, …)` and takes the branch
at `Clausifier.java:1046`.  Verified against a debug run (`-v`), the clauses are

```
[!((ite c a b)), !(c), a]        ; :ite-1
[!((ite c a b)), c, b]           ; :ite-2
[!((ite c a b)), a, b]           ; :ite-red   (Config.REDUNDANT_ITE_CLAUSES)
[(ite c a b), d]                 ; the input clause
```

### What is recorded

Here `ρ = (ite c a b)` is the literal to prove (`negLit.negate()`, see "The
aux-clause contract" below). Each aux clause's record proves a **target clause**
(a set of literals, not an `(or ...)` formula):

| clause | rule | target `T` | per-literal proofs |
| --- | --- | --- | --- |
| `{¬ρ, ¬c, a}` | `:ite-1` | `{¬c, ρ}` | `¬c`: none (`¬c ∈ T`); `a`: `:ite+1` `{ρ, ¬c, ¬a}` |
| `{¬ρ, c, b}` | `:ite-2` | `{c, ρ}` | `c`: none; `b`: `:ite+2` `{ρ, c, ¬b}` |
| `{¬ρ, a, b}` | `:ite-red` | — **not recorded**, see below | |
| `{ρ, d}` | input | `{(or (ite c a b) d)}` | `ρ`, `d`: `or+` (from `CollectLiteral`'s inlining) |

- Artifact 3 (aux record for `ρ`): resolve the two targets on `c` — `{¬c, ρ}`
  and `{c, ρ}` give `{ρ}`.
- Artifact 2: `c`, `a`, `b`, `d` are Boolean constants, so no interning happens.
  With `a` replaced by `(<= (+ x 1) y)` the per-literal proof would additionally
  be composed with the reversed intern clause
  `{¬(<= (+ x (- y) 1) 0), (<= (+ x 1) y)}`.
- Artifact 1 for the assertion: the identity here, since the assertion *is* the
  input clause's formula.

### Deriving the aux record

The per-literal proofs are the dual tautologies of the rules that built the
clauses (`:ite+1`, `:ite+2`, emitted with `mTracker.tautology`); a literal that
is already part of the target needs none. Which literal the model sets true
only decides *which* of these proofs is used — there is no case distinction in
the record itself:

```
clause 1, T1 = {¬c, ρ}:  true literal ¬c  ->  {¬c}                        (subclause of T1)
                         true literal a   ->  res(a, {a}, {ρ, ¬c, ¬a})  =  {¬c, ρ}
clause 2, T2 = {c, ρ}:   true literal c   ->  {c}
                         true literal b   ->  res(b, {b}, {ρ, c, ¬b})   =  {c, ρ}
record:                  res(c, proof(T2), proof(T1))  =  {ρ}
```

The resolution on `c` never misses its pivot: exactly one of `c`/`¬c` is true,
and the clause whose case literal is false contributes its full target.

No new checker support is required: `ProofSimplifier.convertTautIte1Helper`
(line 580) and `convertTautIte2Helper` already take a polarity flag and handle
`:ite+i` and `:ite-i` alike.

The negative occurrence (`addAuxAxioms(ρ, false, …)`) is the mirror image:
clauses `{ρ, ¬c, ¬a}`, `{ρ, c, ¬b}` (`:ite+1/2`), targets `{¬c, ¬ρ}`,
`{c, ¬ρ}`, per-literal proofs `:ite-1` for `¬a` and `:ite-2` for `¬b`, and the
same resolution on `c` concludes `{¬ρ}`. Each polarity is derived from its own
clauses only; neither depends on the other having been built.

### Signatures and registries

The case distinction on `c` is hard-coded where the clauses are created, and so
are the duals — which are neither per literal nor even per clause:

- `and` for `(and a b c)`: three aux clauses, **one** shared dual `and+`;
- `or` for `(or a b)`: **one** aux clause, **two** duals `or+ 0`, `or+ 1`;
- `ite`: two clauses, two duals, plus a case split belonging to neither.

So the sat-side structure is per *case* and belongs to
`createDefiningClausesForLiteral`, right where the rule — and hence its dual —
is known. It hands `buildAuxClause` the target and the per-literal proofs for
each clause and gets the record back (signatures: see "The aux-clause
contract"). The `ite` branch reads:

```java
final Term axiom1 = mTracker.tautology(or(litTerm, not(c), a), TAUT_ITE_NEG_1);
final ClauseSatProof cl1 = buildAuxClause(lit, axiom1, source,
        new Term[] { not(c), ρ },
        new Term[] { null, mTracker.tautology(or(ρ, not(c), not(a)), TAUT_ITE_POS_1) });
final Term axiom2 = mTracker.tautology(or(litTerm, c, b), TAUT_ITE_NEG_2);
final ClauseSatProof cl2 = buildAuxClause(lit, axiom2, source,
        new Term[] { c, ρ },
        new Term[] { null, mTracker.tautology(or(ρ, c, not(b)), TAUT_ITE_POS_2) });
buildAuxClause(lit, axiomRed, source, null, null);              // redundant clause: no record
// start with cl1's proof, resolve cl2 on c
return new FormulaSatProof(null, new ClauseSatProof[] { cl1, cl2 }, new Term[] { null, c });
```

(`addAuxAxioms` stores it under `negLit.negate()`.)

The two scoped registries in the `Clausifier`, both `ScopedHashMap` like
`mLiterals` so `push`/`pop` work:

| registry | key → value | written by |
| --- | --- | --- |
| `mLiteralSatProofs` | aux literal `ρ` (`negLit.negate()`) → `FormulaSatProof` concluding `{ρ}` + its clause records | `addAuxAxioms` / `createDefiningClausesForLiteral` |
| `mAssertionSatProofs` | asserted term `φ` → `FormulaSatProof` concluding `{φ}` + its clause records | `addFormula` |

Keying literal records by `ILiteral` keeps the two polarities of an aux term
apart (`addAuxAxiomsQuant` creates both, `auxTrueLit`/`auxFalseLit`) and, more
fundamentally, keeps negative literals `ρ⁻` distinct from positive `(not ρ)⁺`
terms — see "Registries and the clause record", which also explains why clause
records are reached by reference instead of through a ψ-keyed map.

**Edge case — trivially true clauses.**  `BuildClause.perform` returns early when
`mIsTrue` (a `true` literal, or a complementary pair), so no clause reaches the
engine and no literal of it can be picked from the assignment.  The target is
then provable without the model, so `BuildClause` fills in `mReadyMadeProof`
instead of the literal map.  A `false` literal is the benign direction: dropped
from the DPLL clause, never picked.

### Two observations this example makes concrete

1. **The record uses a sufficient subset of the aux clauses.**  The redundant
   ite clause `{¬ρ, a, b}` is implied by the other two and gets no record, so
   the assembler never has to prove it.  Redundant/optional clauses must therefore be
   recognizable when the record is built; `Config`-guarded clauses are the obvious
   candidates.
2. **The literal-proof direction depends on the literal's polarity.**  For a
   positive literal the sat side needs the *reverse* rewrite clause `{¬a', a}`
   (`iffElim1`), for a negative literal the *forward* one `{¬c, c'}` (`iffElim2`,
   what `rewriteToClause` already builds): from `¬c'` we must derive `¬c`.
   Simplest implementation: build both directions in `BuildClause.addLiteral`
   and pick by `positive`.

### Assembling it, and how it compares to today

With `(assert (not d)) (assert c) (assert a)` added so that the aux literal is
the satisfying literal of the input clause, the assembler produces:

- clause 1, target `{¬c, ρ}`: true literal `a` → `res(a, proof_of_a, {ρ, ¬c, ¬a})`;
- clause 2, target `{c, ρ}`: true literal `c` → `proof_of_c`, i.e. `{c}`;
- `{ρ}`: resolve the two on `c`;
- input clause, target `{φ}`: true literal `ρ` → `res(ρ, {ρ}, {¬ρ, φ})`
  (the `or+` entry from `CollectLiteral`'s inlining) — this is the assertion's
  record, the identity here.

`ModelProver` is thus only asked for the *atoms* `a` and `c`.  Today's
evaluating proof for the same input instead evaluates the `ite` on formula
level, using `ite1` to rewrite `(ite c a b)` to `a`:

```
(res .cse0 (res .cse1 (res a .cse2 (let ((.cse3 (= .cse1 a)))
   (res .cse3 (res c .cse4 (ite1 .cse1)) (=-1 .cse3)))) (or+ 0 .cse0)) …)
```

Both are valid; the clause-based one is the shape that also works when `ρ`'s
subformula contains quantifiers, which `ite1`-style evaluation cannot handle.

### Invariant the assembler relies on

Every recorded clause must have a literal that is *set to true* in the final
assignment (`getDecideStatus`), since the engine reports sat only when every
clause is satisfied by a set literal.  Undecided atoms are never used, so the
model's completion of them cannot conflict.  Worth an assertion in debug mode.

## Sketch of the code changes

Gate everything on a `satProofsEnabled()` helper in the `Clausifier` (the existing
idiom is `mTracker instanceof ProofTracker`, plus the new option).  All sat proofs
below are clause proofs; `null` consistently means "identity", i.e. nothing to
prove, and composition treats it as such.

### Registries and the clause record

Artifacts 1 and 3 share the record type (`FormulaSatProof`) and the assembly
procedure, but **not** the key.  A record for a negative aux literal proves the
clause containing the *negative proof literal* `ρ⁻` — which is not the clause
containing the positive literal `(not ρ)⁺`; the two are related only by explicit
`notIntro`/`notElim` steps (`CoreRules.java:100ff`).  A `Term` key would conflate
them, so literal records are keyed by the `ILiteral` itself:

- **aux literals**: `mLiteralSatProofs.get(l)` proves `{atom^±}` with the
  polarity of `l` — resolutions then pivot on the atom, and no `not` terms appear;
- **assertions**: keyed by the asserted `Term`; the record concludes the assertion
  as a positive proof literal `{φ⁺}` (that is what the final `andIntro` needs,
  also when φ is itself a `(not …)` term).  The bridge between the two levels is
  the usual one: from `{p⁻}` a resolution with `notIntro` gives `{(not p)⁺}` —
  the same dance `ProofTracker.asserted` (line 275ff) does in reverse.

Clause records are **not** kept in a global map keyed by ψ.  Each clause gets its
own `ClauseSatProof` *object*, created by the consumer that requests the clause and
filled in by `BuildClause.perform`; the consumer's `FormulaSatProof` holds direct
references to the objects it needs.  Identity, not the formula, identifies a
record.

```java
/** aux literal ρ → record concluding {ρ}, ρ as a signed proof literal. */
private final ScopedHashMap<ILiteral, FormulaSatProof> mLiteralSatProofs = new ScopedHashMap<>();
/** asserted term φ → record concluding {φ}. */
private final ScopedHashMap<Term, FormulaSatProof> mAssertionSatProofs = new ScopedHashMap<>();
```

The record classes (`FormulaSatProof` with start proof, hyps and pivots;
`ClauseSatProof` with a target clause and a per-literal proof map) are given in
"The aux-clause contract" below.

`beginScope`/`endScope` for both maps next to `mLiterals` in `push`/`pop`.  The
assembler needs no separate assertion list: `SMTInterpol.mAssertions` already holds
the asserted terms in order, and each is a key into `mAssertionSatProofs`.

**Why identity and not ψ.**  Distinct clauses routinely share a clause formula —
terms are hash-consed, and the occurrence-counter inline threshold
(`mTmpCtr <= Config.OCC_INLINE_THRESHOLD` in `CollectLiteral`) can even clausify
the same ψ twice with different literal sets.  Sharing one record would be
*unsound*, not just lossy, because an aux clause's record is only usable in the
context that owns it: for the aux clause `{¬l, o_1..o_k}` the engine's sat
invariant guarantees a set-true literal among **all** of its literals, possibly
`¬l` itself, in which case no `o_i` need be set and `{ψ}` is not provable from the
assignment.  Inside `l`'s own record that cannot happen — the record is only used
while proving `{l}`, so `¬l` is false and some `o_i` must be set true.  A global
map could hand that record to an unrelated consumer that has no such guarantee.
`addExcludedMiddleAxiom` (line 1311) is a live example of a `buildAuxClause` caller
whose ψ (`(not term)`) can easily coincide with an unrelated clause formula.

With per-consumer records the question disappears: two aux literals whose proofs
use the same ψ each create their own clause and hold their own record.

Three kinds of clause records fall out of the existing call sites:

| created by | target | record |
| --- | --- | --- |
| `buildTautology`, `buildClause(rule, …)`, `buildClause(tautologyProof, …)` — theory axioms | — | **none**: these clauses are never a hypothesis of any record (they constrain the model, they do not derive the input), so they need no sat tracking at all |
| `buildAuxClause` | given by the caller (`{ρ}`, a single literal, or a case-split clause) | per-literal proofs given by the caller; owned by the aux `FormulaSatProof` — see "The aux-clause contract" |
| `buildClause(term, source)` (via `AddAsAxiom`) | `{φ}`, the collected formula as a literal | per-literal proofs from `CollectLiteral`'s rewrites/inlining duals; owned by an assertion `FormulaSatProof` |

`mReadyMadeProof` covers the `mIsTrue` case, where no clause reaches the engine:
a `true` literal gives `res(true, trueIntro, {¬true} ∪ T)`, and a complementary
pair `l`/`¬l` gives `res(atom, {¬l} ∪ T, {l} ∪ T)` — both built from the
per-literal proofs already recorded.

### The aux-clause contract (supersedes the earlier shapes)

This replaces the "identity / custom `SatEntry` / `N` hyps / case split" shapes
of the 2026-09-29/10-01 implementation with one uniform contract. It came out of
reviewing that implementation: `buildAuxClause` hard-coded that its
`ClauseSatProof` proves `(or params[1..])`, `and`-positive/`=>`-negative needed
something else and had to copy `buildAuxClause`'s body, and the lazy `orIntro`
in `proveFromLiterals` was only ever reached by `buildAuxClause`'s clauses. The
root of all three is a confusion between an `or` **literal** and a **clause**.

**Which literal is proved.** `ρ = negLit.negate()`: whichever occurrence calls
`addAuxAxioms(term, positive)` adds `positive ? lit : lit.negate()` to its own
enclosing clause in the same `CollectLiteral` call, and that literal is
`negLit.negate()` in both polarities. `addAuxAxioms` stores the record under
`negLit.negate()` (the committed code before 2026-09-29 used `negLit`, which was
the bug behind the earlier "cannot be wired in" detour). Every aux clause built
by `createDefiningClausesForLiteral` has the shape `{¬ρ, o_1, .., o_k}`.

**Literal vs. clause.** `ρ` is always a *literal* — for `ρ = (or l1 .. ln)` it is
the single atom `(or l1 .. ln)`, never the clause `{l1, .., ln}`. What a
`ClauseSatProof` proves, on the other hand, is a *clause*: its **target**
`T`, an array of literals. Usually `T = {ρ}`; for the `N`-clause cases
`T = {o}`, the clause's only non-aux literal; for the case splits of
`ite`/`xor`/`match` `T` contains `ρ` plus the case literal(s), e.g. `{¬c, ρ}`.
Representing `T` as a `Term[]` instead of an `(or ...)` term removes the
ambiguity (`(or l1 .. ln)` as a target would mean the clause, as `ρ` it means the
literal).

**The contract.**

- For every non-aux literal `o_i` of the clause, `buildAuxClause` is given a
  proof of `{¬o_i} ∪ T`, or `null` if `o_i ∈ T` (subsumption, no rule at all).
  It passes it on as `collectLiteral(o_i, …, proof)`, so the literal's
  `SatEntry` already reaches `T`.
- `proveClause` picks the literal set true by the model and resolves its proof
  with the entry: `{o_i}` and `{¬o_i} ∪ T` give `T`; if the entry descends
  from a target literal `o` (`o_i` itself, possibly rewritten) the result is
  `{o}`, a subclause of `T`. No `orIntro`, no index lookup at assembly time.
- `FormulaSatProof` combines the hyps into `{ρ}`: nothing for a single clause
  with `T = {ρ}`, otherwise an optional start proof plus one resolution per hyp
  (see below).

**All proofs are `TAUT_*` tautologies.** Every per-literal proof and every
start proof is `mTracker.tautology(clause, ProofConstants.TAUT_…)`, never one of
the raw checked rules `orIntro`/`orElim`/`andIntro`/`andElim`/`impIntro`/
`impElim`.  (`match`'s completeness fact uses `dtExhaust` simply because
there is no `TAUT_*` rule for it; its literals are `is` atoms, which never
carry a `not`, so it is already in the same form.  Note `tautology()` returns
the annotated term — unwrap with `getClauseProof` — while `dtExhaust` returns
the raw proof.) The difference matters: the raw rules take
the connective's parameters *opaquely* — `orIntro(i, (or a (not b)))` for
`i = 1` proves `{(or a (not b)), ¬(not b)}` with the atom `(not b)` —, while
`tautology` reads its argument as a clause and runs every disjunct through
`termToProofLiteral`, turning a top-level `not` into the sign of the literal and
removing double negations: `TAUT_OR_POS` on `(or ρ (not (not b)))` is the
clause `{ρ, b}`. `ProofTracker.resolve` strips its pivot the same way. With
`TAUT_*` throughout, every atom in the sat-side proofs is `not`-free, so none of
the `wrapNot`/`stripNot`/`notElim` bridging of the earlier implementation (the
source of every sign bug found while implementing it) is needed. The only
remaining boundaries between the two conventions are `ModelProver.proveAtom`'s
results (stripped once in `ModelProofBuilder.proveLiteral`) and the assertion
bridge in `addFormula`.

The per-literal proofs and start proofs are exactly the *duals* of the rules
that build the clauses — the observation the plan started from ("each
structural step has a dual rule").

| `ρ` | aux clauses (rule) | target `T` | per-literal proof | start proof / pivots |
| --- | --- | --- | --- | --- |
| `(or l..)` | `{¬ρ, l1..ln}` (`OR_NEG`) | `{ρ}` | `l_i`: `OR_POS` `{ρ, ¬l_i}` | — |
| `¬(and l..)` | `{(and..), ¬l1..¬ln}` (`AND_POS`) | `{ρ}` | `¬l_i`: `AND_NEG` `{¬(and..), l_i}` | — |
| `(=> t..)` | `{¬ρ, ¬t1..¬t(n-1), tn}` (`IMP_NEG`) | `{ρ}` | `¬t_i`: `IMP_POS` `{ρ, t_i}`; `tn`: `IMP_POS` `{ρ, ¬tn}` | — |
| `(and l..)` | `{¬ρ, l_i}` ×n (`AND_NEG`) | `{l_i}` | `null` | `AND_POS` `{ρ, ¬l1..¬ln}`; pivots `l_i` |
| `¬(or p..)` | `{(or..), ¬p_i}` ×n (`OR_POS`) | `{¬p_i}` | `null` | `OR_NEG` `{¬(or..), p1..pn}`; pivots `p_i` |
| `¬(=> t..)` | `{(=>..), t_i}`, `{(=>..), ¬tn}` (`IMP_POS`) | `{t_i}` / `{¬tn}` | `null` | `IMP_NEG`; pivots `t_i` / `tn` |
| `(ite c a b)` | `{¬ρ, ¬c, a}`, `{¬ρ, c, b}` (`ITE_NEG_1/2`) | `{¬c, ρ}`, `{c, ρ}` | `¬c`/`c`: `null`; `a`: `ITE_POS_1` `{ρ, ¬c, ¬a}`; `b`: `ITE_POS_2` `{ρ, c, ¬b}` | — ; pivot `c` |
| `¬(ite c a b)` | `{ite, ¬c, ¬a}`, `{ite, c, ¬b}` (`ITE_POS_1/2`) | `{¬c, ρ}`, `{c, ρ}` | `¬a`: `ITE_NEG_1`; `¬b`: `ITE_NEG_2` | — ; pivot `c` |
| `(xor p q)` | `{¬ρ, p, q}`, `{¬ρ, ¬p, ¬q}` (`XOR_NEG_1/2`) | `{p, ρ}`, `{¬p, ρ}` | `q`: `XOR_POS_1` `{ρ, p, ¬q}`; `¬q`: `XOR_POS_2` `{ρ, ¬p, q}` | — ; pivot `p` |
| `¬(xor p q)` | `{xor, p, ¬q}`, `{xor, ¬p, q}` (`XOR_POS_1/2`) | `{p, ρ}`, `{¬p, ρ}` | `¬q`: `XOR_NEG_1`; `q`: `XOR_NEG_2` | — ; pivot `p` |
| `match`, case `i` | `{¬ρ, ¬is_i, e_i}` (`MATCH_CASE`) | `{¬is_i, ρ}` | `¬is_i`: `null`; `e_i`: `MATCH_CASE` with `e_i` negated | `dtExhaust` `{is_1..is_n}`; pivots `is_i` |
| `match`, default | `{¬ρ, is_1..is_k, e_d}` (`MATCH_DEFAULT`) | `{is_1..is_k, ρ}` | `is_j`: `null`; `e_d`: `MATCH_DEFAULT` with `e_d` negated | — (the default hyp replaces `dtExhaust`) |

(Pivots are plain atoms; the side containing the atom positively becomes the
positive antecedent of the resolution, so `ite` and `xor` resolve on `c` resp.
`p` regardless of which clause has it negated — the implementation is
`Clausifier.caseSplitRecord`. The `¬ρ` cases are the mirror images: `ρ` stands for the negative literal of
the connective's atom, e.g. `{(and..), ¬l1..¬ln}` is `{¬ρ, ¬l1..¬ln}`. The
redundant `ite` clause `{¬ρ, a, b}` gets no record — `buildAuxClause` is called
with a `null` target.)

**`match` in detail.**  `dtExhaust(d)` is a checked Resolute axiom without
premises proving `{((_ is c_1) d), .., ((_ is c_n) d)}` for *all* constructors of
`d`'s datatype, in declaration order — independent of the `match`.  Without a
default case it is the start proof and each case hyp `{¬is_i, ρ}` cancels one
tester; this needs exactly one hyp per constructor, which holds because a `match`
without a default must be exhaustive, duplicate cases are skipped (in the
clausifier and, consistently, first-match-wins in
`ProofSimplifier.convertTautDtMatch`), and the tester terms are hash-consed
identically.  With a default case after `k` named cases the default clause's own
literals `is_1..is_k` are the completeness fact, so its hyp is the start and no
`dtExhaust` is needed; a `match` consisting only of a default case is a single
hyp with target `{ρ}` (previously an unhandled fallback; note that with
proof level LOWLEVEL `ProofSimplifier.convertTautDtMatch` currently fails an
assertion in `ProofRules.trans` for such a match, on the unsat side as well, so
that is a pre-existing checker-side bug, not a sat-proof one).  `convertTautDtMatch`
handles both polarities of the match literal, so the dual case/default
tautologies need no new checker support.  Example (three constructors, model
`d = c_2(..)`): case hyps prove `{¬is_1}`, `{¬is_2, ρ}` (via `e_2` and the dual),
`{¬is_3}`; resolving them into `{is_1, is_2, is_3}` leaves `{ρ}`.

**Vacuous resolutions, and the hyp order.**  When `mStart == null` the first hyp
is the start and its pivot slot is unused (`null`); for a `match` with a default
case the default hyp goes first, so every later pivot is that case's own tester
atom `is_i`, uniform with the no-default case.  A hyp's proof is either its full
target or, when the picked entry descends from a single target literal `o`
(see `SatEntry.mDisjunct` below), just `{o}`.  For `ite` that never makes a step
vacuous — whichever clause's true literal is its cond literal proves that
literal, and the other clause contributes its full target, so both contain the
pivot — nor for named `match` cases or records with a complete start proof
(`dtExhaust`, `TAUT_AND_POS`, ...).  Only the default case of `match` can — the
one record whose target has several literals that can each be the true literal
on their own: if `d = c_j` for a named case `j`, the default clause may be
satisfied by its tester `is_j`, so its proof is `{is_j}`, and resolving the other
case hyps on `¬is_m` (`m ≠ j`) would be vacuous.  So `proveFormula` tracks the
clause each proof proves (`{mDisjunct}` or the whole target; after a resolution,
the resolvent) and skips a step whose pivot's complement is not in the
accumulated clause — bookkeeping, not search.  In the example only case `j`'s
hyp `{¬is_j, ρ}` is resolved against `{is_j}`.

**Signatures.**

(As implemented 2026-10-05; the records differ slightly from the first sketch:
`ClauseSatProof` has no `mAssembled` — the assembler memoizes per record —,
`FormulaSatProof` also stores the start proof's clause and its conclusion
`ρ`, and its hyps are `SatRecord`s, so an `AddAsAxiom` join can have other
joins as hyps. `ModelProofBuilder.proveRecord` checks that a record proves
exactly `{conclusion}` and otherwise falls back to `ModelProver`.)

```java
/**
 * @param target    the clause the record proves (literals in clause form: (not x) is the negative
 *                  literal of x, never a double negation); null if sat proofs are off or no
 *                  record is needed (e.g. the redundant ite clause).
 * @param litProofs per axiom parameter params[1..]: a proof of {~params[i]} ∪ target, or null if
 *                  params[i] ∈ target.
 */
public ClauseSatProof buildAuxClause(ILiteral auxlit, Term axiom, SourceAnnotation source,
        Term[] target, Term[] litProofs) {
    final Term[] params = ((ApplicationTerm) mTracker.getProvedTerm(axiom)).getParameters();
    assert params[0] == auxlit.getSMTFormula(mTheory);
    final ClauseSatProof csp = target == null ? null : new ClauseSatProof(target);
    final BuildClause bc = new BuildClause(this, axiom, source, csp);
    pushOperation(bc);
    bc.addLiteral(auxlit);                       // no SatEntry: excluded by construction
    for (int i = params.length - 1; i >= 1; i--) {
        bc.collectLiteral(params[i], csp == null ? null : litProofs[i - 1]);
    }
    return csp;
}

abstract static class SatRecord {}

static final class ClauseSatProof extends SatRecord {
    final ProofLiteral[] mTarget;       // the clause proved, see above
    Term mReadyMadeProof;               // != null: proof of mTarget needing no model input
    Map<ILiteral, SatEntry> mLiterals;  // per literal l: proof of {~l, mDisjunct}, or of {~l} ∪ mTarget
                                        // when mDisjunct == null ("whole target")
}

static final class FormulaSatProof extends SatRecord {
    final Term mStart;                  // optional start proof (e.g. AND_POS, dtExhaust); null: start
                                        // with the first hyp's proof
    final ProofLiteral[] mStartClause;  // the clause mStart proves
    final SatRecord[] mHyps;
    final Term[] mPivots;               // per hyp: the pivot *atom* (never "not"-headed); unused for the
                                        // first hyp when mStart == null
    final ProofLiteral mConclusion;     // ρ resp. the asserted formula
}
```

`proveFormula` is then uniform: `proof = mStart`; for each hyp `j`,
`p = proveClause(hyp_j)`; if `proof == null`, `proof = p`; otherwise resolve
`p` and `proof` on the atom `mPivots[j]`, taking as positive antecedent the side
that contains the atom positively (the clauses of both sides are tracked), and
skipping the step if the atom does not occur with opposite polarities on the two
sides (see above).

**Literals are atom + polarity.**  Targets, start clauses, `mDisjunct` and
conclusions are `ProofLiteral`s (`proof.resolute`), pivots are plain atoms; no
`(not x)` term ever encodes a negative literal in the records.  Clause-form terms
(`(not x)` as a disjunct, as passed to `tautology`) are converted once, at the
record constructors, exactly as `ProofTracker.tautology` converts them. A single clause with `T = {ρ}` is just `mStart = null` and one hyp.

**No placeholders.** A `FormulaSatProof` is a recipe, not a proof term with
holes: `mStart` does not mention the hyps and is built eagerly, while the
resolution steps are only written down in `proveFormula`, once `proveClause`
has produced the concrete hyp proofs.  This is what makes clause-shaped targets
possible.  The earlier `{¬ψ_1, .., ¬ψ_m, ρ}` records were an eager placeholder
scheme — each hyp a hole represented by the negative literal `¬ψ_j` — which only
works when every `ψ_j` is a single literal; with clause-shaped hyps it would
need `orElim`/`orIntro` to turn the clause into a literal and back, or real
placeholders (let-bound proof variables substituted at the end).  Deferring
costs nothing: records are only checked as part of the assembled proof, and
`proveClause` is memoized, so a shared hyp is still proved once.

**Consequences for the rest of the code.**

- `SatEntry.mDisjunct` stays, with a precise meaning: which part of the target
  the entry reaches — a single target literal `o` (the collected literal descends
  from `o ∈ T`; its proof, possibly a reversed rewrite, is of `{¬l, o}`), or the
  whole target (descends from a per-literal proof; proof of `{¬l} ∪ T`).
  `buildAuxClause` collects `o_i ∈ T` with disjunct `o_i`, every other literal
  with a "whole target" marker; `descend`/`addLiteral` carry it through
  rewrites unchanged.  This is what tells the assembler which clause a hyp's
  proof actually proves.  Whether the entry's *proof* is `null` is not the
  criterion: a target literal such as `ite`'s `cond` may be interned or
  rewritten, giving a non-null reversed-rewrite proof that still only reaches
  `{cond}`.  (`is` atoms, too, can get a non-null reversed rewrite when they
  become CC literals — observed in the test suite —, which is fine since
  nothing relies on it being `null`.) `BuildClause` /
  `CollectLiteral` composition is unchanged otherwise (the reversed rewrites
  and `CollectLiteral`'s inlining duals are already `tautology`-based and
  stripped).
- `proveFromLiterals` loses its lazy `orIntro`/`disjunctIndex` bridge — it was
  only reached by `buildAuxClause`'s clauses; input clauses already land on
  their formula through `CollectLiteral`'s `TAUT_OR_POS` inlining duals.
- `startAuxClause` and the copied scaffolding in `and`-positive/`=>`-negative
  disappear: every branch calls `buildAuxClause`, as before the model-proof
  work.
- `createIteSatProof`/`createXorSatProof`/`createMatchSatProof` shrink to
  building the targets, per-literal proofs and pivots from the table.
- The `ProofTracker` passthroughs `orIntro`/`orElim`/`andIntro`/`andElim`/
  `impIntro`/`impElim`/`notElim`/`notIntro` are deleted (no callers left);
  `stripNot` (`proveLiteral`), `wrapNot`/`resolveAtom` (`buildProof`) and
  `dtExhaust` stay.
- `AddAsAxiom`'s joins and its toplevel `ite`/`xor` follow the same
  convention (`TAUT_*` duals, targets instead of `(or ...)` formulas); input
  clauses from `buildClause(term)` have `T = {φ}`. A join (`SplitJoin`) is a
  `FormulaSatProof` with start `OR_NEG` `{¬(or..), p_1..}` (negative `or`),
  `AND_POS` `{(and..), ¬p_1..}` (positive `and`) resp. `IMP_NEG` (negative
  `=>`), the children's records as hyps and the children's formulas as pivots.
  Toplevel `ite`/`xor` build their two clauses with a target-taking
  `buildClauseWithTautology` overload and reuse `caseSplitRecord`.
- `addFormula`'s bridge is itself a `FormulaSatProof`: the root record if the
  simplification is the identity, otherwise hyps `{getClauseProof(reverse)}`
  (`{¬simp, asserted}`, the reversed rewrite) and the root record, pivot `simp`.
- `addAuxAxiomsQuant` registers its records under `T` and `¬T`, not under the
  syntactic negations of its defining literals — see "Quantified aux literals"
  below.

**Fallback.** A record can still be incomplete (a `poisonSatRecord()`ed clause,
e.g. a quantified literal inside an `ite` branch). Proving a multi-literal
target via `ModelProver` is not possible (it proves atoms, and a proof of `{ρ}`
alone would make the later resolution on `c` vacuous), so the fallback moves up
one level: if any hyp of a `FormulaSatProof` cannot be proved structurally,
`proveLiteral` falls back to `ModelProver.proveAtom(ρ)` for the whole record,
exactly as it already does when no record exists.

**Quantified aux literals (decided 2026-10-05, records implemented 2026-10-06).**
`createQuantAuxTerm` introduces a fresh defined function `AUX` (`@AUX…`, defined as
the subformula `term`, free variables as arguments) and two `QuantAuxEquality`
atoms, `T = (= AUX true)` and `F = (= AUX false)`.  `T` is the quantified
counterpart of a `NamedAtom`: parent clauses only ever contain `T` or `¬T`
(`createAnonLiteral` returns `T`; `CollectLiteral` adds `T` or `T.negate()`).
`F` only occurs in defining clauses, as the stand-in for `¬T`: wherever the
ground encoding has `¬L`, the quantified one has `F` — the *strong* form, so that
the unsat side can use the existing tautologies with a positive `AUX` equality.

Records are therefore needed only under `T` and `¬T`, and the sat side must use
the same stand-in mapping instead of negating syntactically (which would give
`ρ = ¬F` resp. `¬T` and duals with a *negated* `AUX` equality, which
`ProofSimplifier` cannot convert):

| record built from | its aux atom stands for | conclusion | stored under |
| --- | --- | --- | --- |
| `auxFalseLit`'s clauses `{F, …}` | `¬L` | `T` | `T` |
| `auxTrueLit`'s clauses `{T, …}` | `L` | `F`, then bridge `F → ¬T` | `¬T` |

With this mapping every per-literal and start proof has the `AUX` equality
*positive* — exactly the forms the existing conversions accept:
`convertTautElimIntro` takes a positive `(= AUX true)` in intro rules and a
positive `(= AUX false)` in elim rules (expanding `AUX` via `expand`), and the
excluded-middle duals are the existing tautologies verbatim:

- `createExcludedMiddleSatProof` (subformulas that are not connectives:
  quantified formulas, theory atoms with free variables, …): the `auxFalse`
  record needs `{¬term, T}` for its literal `term` — `:excludedMiddle1`; the
  `auxTrue` record needs `{term, F}` for its literal `(not term)` —
  `:excludedMiddle2`.  No new rule.
- The connective branches (`or`, `and`, `=>`, `ite`, `xor`, `match`) apply the
  table of "The aux-clause contract" with `T` in the role of `ρ`'s atom and `F`
  in the role of its negation.

The one extra fact is the bridge `F → ¬T` for the `¬T` record: the exclusivity
clause `{¬F, ¬T}`, from `symm`/`trans` (`(= true AUX)`, `(= AUX false)` ⊢
`(= true false)`) and `¬(= true false)`.  This is the only place where the sat
side uses the weaker `¬F` form; everything else reuses the strong forms of the
unsat side.

**Ground Boolean terms used as function arguments** get
`addExcludedMiddleAxiom`'s CC equality proxies `(= p true)`/`(= p false)` (it
explicitly skips `@AUX` terms).  The model does not know the value of such a
`p` — it can be an arbitrary formula — so these equalities must be *proved*:
today `ModelProver` evaluates `p` recursively as a formula into `{p}`/`{¬p}` and
then applies `iffIntro2`+`trueIntro` resp. `iffIntro1`+`falseElim`
(`ModelProver.convertApplicationTerm`), which redoes `p`'s structure and throws
for quantified `p`.  Instead, take `{p}`/`{¬p}` from the assembler
(`proveLiteral` on `p`'s clausifier literal — its aux record if `p` is
compound) and resolve with the unsat side's clause verbatim: `:excludedMiddle1`
`{(= p true), ¬p}` resp. `:excludedMiddle2` `{(= p false), p}`.  Only the
positive equality matching `p`'s value is ever needed, so no dual and no bridge;
the excluded-middle clauses still need no `ClauseSatProof` record (the
tautology is rebuilt where it is used).  This plugs into `ModelProver` as a hook
(a small callback implemented by `ModelProofBuilder`):

- **Where:** at every Boolean subterm `ModelProver` would otherwise evaluate
  recursively — arguments of uninterpreted functions, Boolean arguments of
  `select`/`store`/constructors, and the condition `c` of a term-level
  `(ite c x y)` inside an LA/CC atom.  Non-Boolean terms can only contain
  formulas (and quantifiers) through such Boolean subterms, so this one hook is
  also what keeps `ModelProver` quantifier-free once Phase 4 records exist.
- **When:** only if the subterm's clausifier literal has an `mLiteralSatProofs`
  record, i.e. it is a compound formula the clausifier decomposed.  For atoms
  such as `((_ is c) d)`, `(= x y)` or `(<= x 0)` the evaluation *is* their sat
  proof; otherwise evaluate as today.

Non-Boolean terms are always proved by evaluation from the model and the
interpretation of the builtin functions — e.g. `(div (+ x y) 5)` is evaluated
recursively rather than derived from its axiom clauses, which stay record-less
theory axioms.

**Implemented (2026-10-05)** as `ModelProver.BooleanTermProver`, set by the
`ModelProofBuilder` constructor (`proveBooleanTerm`).  `ModelProver.convert`
asks it for every Boolean-sorted subterm other than `true`/`false`/`not`
(after stripping annotations), so it covers all the places above without
special-casing them; the resulting `{p}`/`{¬p}` proof then flows into the
existing `iffIntro` step of `convertApplicationTerm` resp. `postConvertIte`.
`proveBooleanTerm` uses only the record of the *true* one of `p`'s literal and
its negation (via `proveRecord`, never the `proveAtom` fallback, which would
evaluate `p` again) and returns null otherwise.  Two technicalities: the
`TermTransformer` is not re-entrant, so a `proveAtom` reached from inside the
hook (a record's fallback) runs on a fresh nested `ModelProver`; and `prove`
memoizes a record as `FAILED` while it is in progress, so a cycle through the
hook degrades to evaluation instead of looping.

The needed record often does not exist for ground `p`: the excluded-middle
clause `{(= p false), p}` *flattens* a positive `or` into the clause (likewise
`{(= p true), ¬p}` a negated `and`), so `p`'s aux axioms for that polarity are
never created.  The record exists only if `p` also occurs unflattened in that
polarity, e.g. negated in an input clause, as an xor/`=` argument or as a
term-ite condition (tests `testCompoundBooleanFunctionArgument`,
`testCompoundTermIteCondition`).  For ground `p` the evaluation fallback is
fine.  For Phase 4 it suffices too: the evaluation of a flattened `or`
descends to its children, and the hook takes over at the quantified child,
whose `QuantLiteral` is never flattened — provided its record exists for the
needed polarity.

All of this is still behind Phase 4: `T`/`F` are `QuantLiteral`s in quantified
clauses (the assembler's `isTrue` rejects them) and the records are schemas over
the free variables.  Until then these literals fall back to `ModelProver`
(which also cannot evaluate quantified formulas), so nothing is exercised end
to end.

*Implementation notes (2026-10-06).*  `createDefiningClausesForLiteral` takes
`ρ` as a parameter instead of computing `negate(litTerm)`: `addAuxAxioms` passes
the negation as before, `addAuxAxiomsQuant` passes `T` for `F`'s clauses and `F`
for `T`'s clauses, and wraps the latter in a `FormulaSatProof` whose start is the
exclusivity clause `{¬F, ¬T}` (`auxExclusivityProof`) with pivot `F`.
`createExcludedMiddleSatProof` now has target `{ρ}` with the other
excluded-middle tautology as its literal's proof.  Keying needed one more fix:
`createAnonLiteral` used to create a *second* `QuantAuxEquality` for the same
`AUX` term, and `QuantLiteral` has identity equality, so a record stored under
`addAuxAxiomsQuant`'s `T` could never be found from a parent clause.
`addAuxAxiomsQuant` now registers its `T` with `setLiteral`, and
`createAnonLiteral` returns it.

Since nothing consumes these records yet, they were checked directly: every
start and per-literal proof of every quantified record (or/and/=>/ite/xor/match,
negated occurrences, and the bridge), 56 in all, was run through
`ProofSimplifier` and `MinimalProofChecker` and proves exactly the clause the
record expects, without oracles.  This exposed two lowlevel bugs that also hit
the unsat side (regressions `datatype/match_bug4.smt2`,
`datatype/match_quant_aux.smt2`): `convertTautDtMatch` did not accept the
`(= AUX true/false)` literal of a quantified match (now expanded like in
`convertTautElimIntro`, sharing `replaceByAuxDefEq`), and `convertMatch` was off
by one for a match whose last case is a constructor case.  An `AUX` for a
quantified formula used as a Boolean argument (the excluded-middle case) still
has an incomplete record, because collecting the nested quantified formula as a
literal poisons its clause record (the nested-quantifier part of Phase 4).

### `BuildClause` and `CollectLiteral`

*(Describes the implemented state as of `8c305a76`. Under "The aux-clause
contract" the clause record carries a target instead of `mFormula`, and
`SatEntry.mDisjunct` records whether an entry reaches a single target literal or
the whole target; the propagation mechanism itself is unchanged.)*

**`mCurrentLits` stays exactly what it always was: a plain `Set<Term>`, used only
to stop the same term from being collected twice** (e.g. a literal occurring
twice in one clause) — it never held the sat-proof payload and does not need to.
Each `Term` gets collected at most once regardless, so its `SatEntry` — the
disjunct of ψ it descends from, and the proof connecting them — can live as an
**immutable field on the one `CollectLiteral` instance created for it**, fixed at
construction, rather than in a second, mutable, term-keyed map on `BuildClause`
that every `descend`/`addLiteral` call would otherwise have to look back up (and
that a duplicate `collectLiteral` call for the same term would silently
overwrite, before the map was even fully removed here — harmless, since any
valid derivation of ψ from a literal is as good as any other, but needless
aliasing between an unrelated occurrence's provenance and this one's). Binding
the entry at construction instead also means `addLiteral` can no longer *look
up* the entry — the caller (`CollectLiteral.perform()`, which already holds it
as its own field) must *pass* it in.

```java
 final LinkedHashSet<Term> mCurrentLits = new LinkedHashSet<>();    // dedup only, unchanged
+private final LinkedHashMap<ILiteral, SatEntry> mLitSatProofs = new LinkedHashMap<>();

 public void collectLiteral(Term term) { collectLiteral(term, term, null); }

+/** @param disjunct the disjunct of the clause formula this descends from
+ *  @param satProof a proof of {¬term, disjunct}, or null if term == disjunct */
+public void collectLiteral(Term term, Term disjunct, Term satProof) {
     while (isNotTerm(term) && isNotTerm(...)) { ... }
     if (mCurrentLits.add(term)) {
+        final SatEntry entry = mSatRecord == null ? null : new SatEntry(disjunct, satProof);
+        mClausifier.pushOperation(new CollectLiteral(mClausifier, term, this, entry));
-        mClausifier.pushOperation(new CollectLiteral(mClausifier, term, this));
     }
 }

+/** resolve {¬new, term} with {¬term, disjunct} on term; null == identity. Stays
+ *  on BuildClause (not CollectLiteral) only because it needs mClausifier.mTracker;
+ *  CollectLiteral calls it on its own mClauseBuilder. */
+Term compose(Term term, Term inner, Term outer) {
+    return outer == null ? inner : inner == null ? outer
+            : ((ProofTracker) mClausifier.mTracker).resolve(term, inner, outer);
+}
```

`CollectLiteral` itself gains the field and a `descend` of its own, operating on
`mLiteral`/`mSatEntry` instead of a lookup:

```java
 class CollectLiteral implements Operation {
     private final Term mLiteral;
     private final BuildClause mClauseBuilder;
+    private final Clausifier.SatEntry mSatEntry;   // null when this clause has no ClauseSatProof

-    public CollectLiteral(Clausifier clausifier, Term term, BuildClause collector) {
+    public CollectLiteral(Clausifier clausifier, Term term, BuildClause collector, Clausifier.SatEntry satEntry) {
         ...
+        mSatEntry = satEntry;
     }

+    /** compose {¬child, mLiteral} (dualProof, or null for identity) with this term's own entry. */
+    private Clausifier.SatEntry descend(final Term dualProof) {
+        return new Clausifier.SatEntry(mSatEntry.mDisjunct, mClauseBuilder.compose(mLiteral, dualProof, mSatEntry.mProof));
+    }
```

In `BuildClause.addLiteral`, `origAtom`/`positive` no longer need to reconstruct
a map key — the entry simply arrives as a parameter, straight from the caller's
own field:

```java
-public void addLiteral(final ILiteral lit, final Term origAtom, final Term rewriteAtom, final boolean positive) {
+public void addLiteral(final ILiteral lit, final Term origAtom, final Term rewriteAtom, final boolean positive,
+        final Clausifier.SatEntry entry) {
     ...
-    if (mClauseFormula != null) {
-        final SatEntry entry = mCurrentLits.get(origLiteral);
+    if (entry != null) {
         final Term reverse = mClausifier.mTracker.rewriteToClauseReverse(origLiteral, rewriteLiteral);
         mLitSatProofs.put(positive ? lit : lit.negate(),
                 new SatEntry(entry.mDisjunct, compose(origLiteral, reverse, entry.mProof)));
     }
-    mCurrentLits.remove(origLiteral);
```

`CollectLiteral.perform()`'s call sites then read, uniformly, `mSatEntry == null
? null : descend(...)` where they used to call `mClauseBuilder.descend(mLiteral,
...)`, and its one terminal `addLiteral` call becomes `mClauseBuilder.addLiteral(
positive ? lit : lit.negate(), at, rewrite, positive, mSatEntry)`. A welcome
side effect: the old sketch's `mCurrentLits.remove(mLiteral)` calls (and the
"must happen *after* the `descend` calls that read `mLiteral`'s entry" ordering
hazard they created, see the inlining example below) disappear entirely — there
is no shared entry left to go stale, so nothing needs removing once `mLiteral`
is fully handled; `mCurrentLits` itself is untouched except for the initial
`add` in `collectLiteral`.

and `perform()` fills in the record the consumer already holds — or, when
`mIsTrue`, its `mReadyMadeProof` instead, since no clause reaches the engine:

```java
+    if (mSatRecord != null) {
+        if (mIsTrue) {
+            mSatRecord.mReadyMadeProof = buildReadyMadeProof();   // true-literal or complementary pair
+        } else {
+            mSatRecord.mLiterals = mLitSatProofs;
+        }
+    }
```

The record object (`mSatRecord`, with its `mFormula` already set) is what the
`BuildClause` constructor now takes instead of a bare clause formula.

Under "The aux-clause contract" every entry's proof reaches the clause's whole
target at construction time (input clauses via `CollectLiteral`'s `or+` duals,
aux clauses via the per-literal proofs passed to `buildAuxClause`); the
assembler no longer adds an `orIntro` for the picked literal.

### `CollectLiteral`

Every branch that replaces or splits the collected term passes the descent along;
nothing has to be threaded *into* `collectLiteral` from outside.

| branch | sat step to compose |
| --- | --- |
| `rewriteLiteral` (line 71ff) | `rewriteToClauseReverse(mLiteral, litRewrite)`, then `collectLiteral(rewrittenLit, e.mDisjunct, …)` |
| `or`/`=>`/`and` inlining (line 102ff) | the dual of the tautology used: `TAUT_OR_POS` / `TAUT_IMP_POS` / `TAUT_AND_NEG`, one per inlined child |
| `QuantifiedFormula` (line 205ff) | the dual of `getTautForallNeg`/`getTautExistsPos`, plus the reverse of the `mCompiler.transform` rewrite |
| aux literal (line 191ff, 230ff) | nothing extra — the generic `addLiteral` path records the reversed `intern`; the *record* comes from `addAuxAxioms` |
| `TermVariable` (line 220ff), `MatchTerm`, `=`, `<=`, uninterpreted | nothing extra — generic `addLiteral` path |

Concretely for the inlining branch — no ordering hazard this time, `mSatEntry` is
`this`'s own field and is read as many times as needed, in any order, since
nothing here mutates it or removes it:

```java
     final Term taut = mClausifier.mTracker.tautology(theory.term("or", tautClause), rule);
     mClauseBuilder.addResolution(taut, mLiteral);
     for (int i = params.length - 1; i >= 0; i--) {
-        mClauseBuilder.collectLiteral(tautClause[i + 1]);
+        if (mSatEntry == null) {
+            mClauseBuilder.collectLiteral(tautClause[i + 1]);
+        } else {
+            final Term dualChild = Clausifier.isNotTerm(tautClause[i + 1]) ? Clausifier.toPositive(tautClause[i + 1])
+                    : theory.term("not", tautClause[i + 1]);
+            final Term dual = mClausifier.mTracker.tautology(theory.term("or", mLiteral, dualChild), dualRule);
+            final Clausifier.SatEntry e = descend(dual);
+            mClauseBuilder.collectLiteral(tautClause[i + 1], e.mDisjunct, e.mProof);
+        }
     }
```

### Input clauses and assertions

Structurally identical to aux literals, with `AddAsAxiom` in the role of
`createDefiningClausesForLiteral`: every `AddAsAxiom` node yields a
`FormulaSatProof` for *its* formula, and the assertion's record is the one from the
root node.

- **Leaf** (`buildClause(term, source)`): the node's formula φ *is* the clause
  formula ψ, so the record is the identity — `mProof == null`, `mHyps == {ψ}`.
  Recorded when `BuildClause` registers the clause.
- **Split** (`and` positive, `or`/`=>` negative, `xor`, `ite`, quantifier): the
  children's records are combined with the dual of the tautology the unsat side
  uses in `resolveBinaryTautology`, and the hypothesis lists concatenate.  For the
  positive `and` split, `{¬φ_i, …}` per child plus `and+` gives
  `{¬ψ_1..¬ψ_n, (and φ_1 … φ_k)}`.
- The join needs the children's records, which only exist after they have run, so
  this is the join `Operation` already noted for `AddAsAxiom` — push it under the
  children, then pop and combine.
- `addFormula` finally maps the root record's conclusion back to the *asserted*
  term — the clausifier works on `mCompiler.transform`'s output, so one reversed
  rewrite step (`iffElim1` on the `modusPonens` rewrite of line 1895) bridges from
  the simplified formula to the original assertion — and stores the result in
  `mAssertionSatProofs` keyed by the asserted term.

Per clause formula, per `ILiteral`, the proof `{¬l, ψ}` is artifact 2 — exactly the
same mechanism as for aux clauses.  Input formulas and aux literals thus share the
record type and the assembly logic; they differ in the key (asserted `Term` vs.
`ILiteral`, see "Registries and the clause record") and in where the record is
built (`AddAsAxiom` join vs. `createDefiningClausesForLiteral`).

### Quantified clauses and free variables (decided 2026-10-06)

**The hypothesis is the universal closure.**  A `QuantClause` with clause
formula `ψ(y⃗)` contributes the closed formula `C = (forall y⃗ ψ(y⃗))`.  That is
what `BuildClause.buildQuantifierProof` already proves on the unsat side (via
`allIntro`), and it is what the input formula needs.  `C` has no free variables,
so it can be a hypothesis as it stands.  Using it splits the obligation into two
independent halves that meet at `C`:

1. **`C` implies the target** (no model needed): the clause's `ClauseSatProof`
   proves `{¬C} ∪ T`.
2. **`C` holds in the model** (the quantifier theory's part, still open): a
   proof of `{C}`.

Resolving the two on `C` gives `T`, exactly as a ground clause's record gives
`T` from its true literal.

**Half 1: from the closure to the target.**  A quantified clause has no true
literal to pick, so its `ClauseSatProof` is used differently from a ground one.
It must prove `(forall y⃗ (or l_1(y⃗) … l_n(y⃗))) ⇒ T`, i.e. the clause
`{¬C} ∪ T`.  For that it keeps, per literal, the proof of `l_i[θ] ⇒ T`, i.e.
`{¬l_i[θ]} ∪ T` (or a single target literal, as for ground clauses), and the
instantiation `θ` of the closure's variables.  The assembler then builds:

1. `forallElim(θ, C)`: `{¬C, (or l_1 … l_n)[θ]}`.  This is valid for *any* `θ`.
   `θ` is aligned with the closure's variables, `clause.getFreeVars()` as used
   by `buildQuantifierProof`.
2. Or-elimination with the dual of the `:or+` steps `buildQuantifierProof` uses:
   `:or-` `{¬(or l_1 … l_n)[θ], l_1[θ], …, l_n[θ]}`.  Skipped for a one-literal
   clause, whose closure body is the literal itself.
3. Resolve each `l_i[θ]` with its literal's proof.  Result: `{¬C} ∪ T`.

The model is never consulted, unlike for a ground clause.

**θ is a global function of the variable, so all records are ground.**

- `convertQuantifiedSubformula` creates fresh variables per quantifier
  occurrence for a positive `forall` or negative `exists`.  The dual that a
  literal's proof needs is `forallIntro` `{(forall x⃗ F), ¬F[c⃗]}` resp.
  `existsElim` `{¬(exists x⃗ F), F[c⃗]}`, which holds only at the choose terms
  `c⃗ = getSkolemVars(x⃗, F, isForall)`.
- So each fresh variable has exactly one binding: the choose term of the
  quantifier it replaced.  If `F` contains variables of an outer drop, those are
  bound first: collection goes outside-in, and so does `AddAsAxiom` for a
  top-level quantifier.  The choose terms are then computed from `F[θ]`, which
  composes nested drops.
- The same quantified formula dropped twice gives two fresh variables with the
  same choose term, which is harmless.

Hence a Clausifier-wide scoped map `fresh variable → choose term`, filled by
`convertQuantifiedSubformula` in its fresh-variable branch, is `θ` for every
clause.

- Every dual and every target is built `θ`-instantiated, so entry proofs prove
  `{¬l_i[θ]} ∪ T[θ]` with no free variables.  This includes the defining clauses
  of a quantified `AUX(y⃗)`, whose target `(= AUX(y⃗) true)` becomes
  `(= AUX(c⃗) true)`, and the body records below a top-level `forall`, which the
  join then uses as they are.
- No proof term needs let/unlet instantiation, and memoization stays per record.
- The `ClauseSatProof` of a quantified clause keeps `θ` restricted to its
  closure's variables, for step 1 and for the pivots `l_i[θ]`.  The entries
  stay keyed by the clause's literals `l_i`, which still contain the variables.
- `CollectLiteral` replaces `poisonSatRecord()` by the dual `forallIntro` /
  `existsElim` on `qf[θ]` (fresh-variable branch).  In the skolemized branch it
  uses `existsIntro(sk⃗)` `{(exists x⃗ F), ¬F[sk⃗]}` resp. `forallElim(sk⃗)`
  `{¬(forall x⃗ F), F[sk⃗]}`, valid for any terms and therefore for the
  `@skolem` terms (whose definitions are the same choose terms); no variable
  appears there.  `AddAsAxiom` does the same for a top-level quantifier, as the
  start of the joining `FormulaSatProof`.

*Implementation status (2026-10-10).*  Half 1 is implemented, including DER:

- `Clausifier.mChooseTerms` is filled by `convertQuantifiedSubformula`.
- The duals use the existing quantifier tautologies with swapped keys
  (`dualQuantifierRule`: `:forall-`↔`:forall+`, `:exists+`↔`:exists-`).
  `ProofSimplifier.convertTautQuantSkolemize` accepts choose terms in place of
  skolem functions.
- The proofs are composed over the variables as before.  The records are
  instantiated when they are sealed: `ClauseSatProof.seal` in
  `BuildClause.perform` instantiates the target and the literal proofs, and
  `Clausifier.formulaSatProof` instantiates every `FormulaSatProof`.  So every
  record is ground once it exists, without instantiating terms in the
  unsat-side code paths.
- `ModelProofBuilder.proveFromClosure` builds `{¬C} ∪ T`.  Until half 2 exists
  it is used only in a test mode that keeps the closures as hypotheses
  (`QuantifiedSatRecordTest`, which checks the assembled clause, the checker's
  clause and the lowered proof, oracle-free).  Otherwise a quantified record
  counts as incomplete.
- DER: `DERSatRecord` derives the DER'd clause's entries (see below).  Only a
  clause that DER makes trivially true still gets an incomplete record; it is
  dropped, so a proof of it would have to be a tautology proof.

**DER stays in half 1.**  `DestructiveEqualityReasoning` turns
`ψ = (x ≠ t) ∨ l_1 ∨ … ∨ l_n` (with `t` free of `x`) into
`ψ'' = (l_1 ∨ … ∨ l_n)[x := t]` over the remaining variables, and the solver
holds the closure `C''` of `ψ''`.  The record of `ψ''` is derived from the
record of `ψ` without the model.  Its instantiation `θ''` is `θ` without `x`.
The DER literal's proof `{¬(x ≠ t)[θ]} ∪ T` is `{(= θx t[θ''])} ∪ T`, and each
`l_i` has `{¬l_i[θ]} ∪ T`.  The proof for the substituted literal is then the
case split on that equality:

1. Congruence: `{¬(= θx t[θ'']), ¬l_i[x := t][θ''], l_i[θ]}`.
2. Resolve with `l_i`'s proof on `l_i[θ]`, giving
   `{¬(= θx t[θ'']), ¬l_i[x := t][θ'']} ∪ T`.
3. Resolve with the DER literal's proof on the equality, giving
   `{¬l_i[x := t][θ'']} ∪ T`.

Half 1 then runs unchanged on `C''` with `θ''`.  The choose term `θx` still
occurs in the proof, but only as a term; nothing evaluates it.  Details:

- **Several variables and chains.**  `σ` is the closure `σ*` of all usable
  `(v ≠ s)` literals, including var-to-var ones (`x ≠ y`, `y ≠ t` give
  `x, y ↦ t`).  The equality `θx = σ*(x)[θ'']` is built by `trans` from the
  equalities those literals' proofs provide.  Each such equality is a case
  hypothesis, discharged by its literal's proof.
- **Simplification is per literal** (`SubstitutionHelper.substituteInClause`).
  Ground literals and literals without substituted variables are kept as they
  are, with their proofs.  Each other literal is substituted, simplified
  (`normalizeAndSimplifyLitTerm`, with a rewrite proof) and turned into a new
  literal, so its proof gets the reversed rewrite as for every other rewrite.
  - A literal that simplifies to `false` is dropped, and its proof is not
    needed.
  - Literals that become equal are merged; any one of their proofs serves.
  - A literal that simplifies to `true` makes the clause trivially true, and the
    clause is dropped.  It is never a hypothesis, so it needs no record.
- **All variables eliminated.**  `ψ''` is a ground DPLL clause.  Its record has
  ordinary per-literal proofs and is used like any ground clause, by its true
  literal.
- **Implementation notes.**
  - The congruence is structural: low-level `cong`/`refl`, memoized per subterm.
    No `@derbody` function is needed, since matches are rewritten to `ite` by
    the TermCompiler and no binder can contain an eliminated variable.
  - DER applies `σ` simultaneously and does not always make it idempotent.
    `{x ↦ y, y ↦ (f z)}` keeps `y` in the DER'd clause.  So the leaf equality
    `(= σ(x)[θ] θx)` comes from a DER literal `(x ≠ s)` either with
    `s = σ(x)` directly, or, if DER composed `σ`, with `s[σ] = σ(x)` via
    congruence on `s` and `trans`.
  - A derived entry concludes the union of several entries' remainders, which
    can be any subclause of the target.  `SatEntry.mRest` records it exactly.
  - `SubstitutionResult` now reports, per original literal, the substituted
    term, its rewrite and the new literal.

**Half 2: proving `{C}` from the model (open).**  Per `QuantClause` that half 1
uses, a proof of its closure `{C}` is needed.  This is the quantifier theory's
part, and it is left open for now.  The expected source is an MBQI-style
argument: in the sat case it checks the clause on all relevant instances and
that the clause lies in the complete fragment, which is exactly the
justification needed here.  Notes for when it is designed:

- **Interface.**  Half 1 only consumes `{C}` for the closure that
  `buildQuantifierProof` builds, so whatever produces it is independent of the
  records.
- After DER, the closure to prove is the one of the DER'd clause, which is what
  the solver holds; DER itself is handled in half 1.
- If a clause has a true ground literal (`QuantClause.hasTrueGroundLits()`),
  `forallIntro(C)` plus the model's proof of that literal suffices.
- The instances half 2 looks at differ from `θ`.  If a quantified `AUX`
  literal must be shown true at such an instance, evaluating its defined `@AUX`
  works when the definition is quantifier-free.  A definition that itself
  contains a quantifier needs that inner closure at that instance, which the
  ground-at-`θ` records do not provide.

## Call-site checklist

Every place that needs new code, from the inventory of existing call sites.

**`convert/Clausifier.java`**

| where | what |
| --- | --- |
| fields, `push`, `pop` (1914ff, 1933ff) | `mLiteralSatProofs`, `mAssertionSatProofs`, `satProofsEnabled()`, `beginScope`/`endScope` |
| `addFormula` (1867) | build the assertion record from the `AddAsAxiom` root, bridge the `modusPonens` rewrite (1895) in reverse, store it |
| `buildClause(Term, SourceAnnotation)` (883) | create the `ClauseSatProof` (ψ = the collected formula), pass it to `BuildClause`, return it to `AddAsAxiom` |
| `buildAuxClause` (829) | takes the target and per-literal proofs from its caller, creates the record, returns it — see "The aux-clause contract" |
| `buildTautology` (874), `buildClause(Annotation, …)` (889), `buildClauseWithTautology` (900) | pass `null` — theory-axiom clauses need no record.  (`buildClauseWithTautology` is only used by `AddAsAxiom`'s `xor`/`ite` splits, whose sat side is the dual tautology in the join, not a clause record.) |
| `createDefiningClausesForLiteral` (979) | **the bulk of the work**: one record proof per branch — `or`, `=>`, `and`, `ite`, `xor`, `QuantEquality` fallback (986–1118), `MatchTerm` (1120ff), default (1179ff) |
| `addAuxAxioms` (922) | store the returned record under `negLit.negate()` |
| `addAuxAxiomsQuant` (950) | records under `T` (from `auxFalseLit`'s clauses) and `¬T` (from `auxTrueLit`'s clauses, plus the `F → ¬T` bridge) — see "Quantified aux literals" |
| `addExcludedMiddleAxiom` (1311) | **no record**; the equality proxy `(= p true/false)` is proved where `ModelProver` needs it, from `p`'s sat proof plus the excluded-middle tautology — see "Quantified aux literals" (ground paragraph) |
| `addMatchAxiom` (1337) / `buildTautology` at 1378 | no record (tautology clauses) |
| `setupCClosure` (1555ff) | direct `BuildClause` use with a hand-built `mCurrentLits` entry — adapt to the map, no record |
| `addStoreAxiom`, `addDiffAxiom`, `addDivideAxioms`, `addModuloAxioms`, `addToIntAxioms`, `addNat2BvAxiom`, `addBv2NatAxioms`, `addBitvectorAxiom` (413–1305) | nothing: all tautology clauses |
| `createAnonLiteral` (1497), `createQuantAuxTerm` (1479), `getLiteralTseitin` (1517) | nothing directly — the records come from `addAuxAxioms*`.  Note `getLiteralTseitin` is also reached from `trackAssignment` (1997/2000) and `createBooleanLit` (2109/2124); those paths add *both* polarities, so both records exist |

**`convert/BuildClause.java`** — constructor takes the `ClauseSatProof`;
`mCurrentLits` becomes a map of `SatEntry`; `collectLiteral` overload with
(disjunct, proof); `descend`/`compose` helpers; `addLiteral(lit, origAtom,
rewriteAtom, positive)` records the reversed rewrite; `perform` fills the record,
including `mReadyMadeProof` for `mIsTrue`; `buildQuantifierProof` gets its dual.

**`convert/CollectLiteral.java`** — `perform`: the `rewriteLiteral` path (71ff),
the `or`/`=>`/`and` inline path (102ff), the `QuantifiedFormula` path (205ff); the
`mCurrentLits.remove` calls move after the `descend`s.  The remaining branches need
nothing beyond `addLiteral`.

**`convert/AddAsAxiom.java`** — a join `Operation` plus, per split, the dual
tautology: `or` negative (99ff), `and` positive (110ff), `=>` negative (119ff),
`xor` (131ff), `ite` (154ff), `QuantifiedFormula` (177ff), and the two
`buildClause` leaves (93, 187).

**`convert/AddTermITEAxiom.java`** — nothing (tautology clauses only).

**`proof/`** — `IProofTracker`/`ProofTracker`/`NoopProofTracker`:
`rewriteToClauseReverse`, the `allIntro` dual, `resolve` exposed on the interface;
`ProofConstants`: the reverse-rewrite annotation; `ProofSimplifier`:
`convertMPReverse`; new `ModelProofBuilder`; `MinimalProofChecker`: factor out
`getProvedClause`.

**`theory/quant/`** — `QuantClause` (record + closure), `QuantifierTheory`
(`createAuxLiteral`/`createAuxFalseLiteral` records, the `{(forall x⃗ ψ)}`
obligation), `DestructiveEqualityReasoning`/`DERResult` (dual proof).

**`model/ModelProver.java`** — `proveAtom` entry point.

**`smtlib2/SMTInterpol.java`** (820ff) + `option/SolverOptions.java` — the `SAT`
branch of `getProof` and the option; plus a new test class.

## Classes to touch

### `proof` package

| Class | Change |
| --- | --- |
| `IProofTracker` | new methods: `rewriteToClauseReverse(Term rhs, Term rewrite)` → `{¬rhs, lhs}`; a dual of `allIntro` (from `(forall x ψ)` derive the body under an eigenvariable, i.e. `forallElim` + `forallIntro`). |
| `ProofTracker` | implement them (`oracle` with a new `:rewrite-rev` annotation, `resolutionRule`, `mProofRules.iffElim1`). |
| `NoopProofTracker` | no-ops / return `null`. |
| `ProofConstants` | `ANNOTKEY_REWRITE_REV` (or a direction flag on `:rewrite`). |
| `ProofSimplifier` | `convertMPReverse` for the new oracle (same as `convertMP` with `iffElim1`); keep the `mAuxDefs`/`defineFun` wrapping usable for model proofs. |
| **new** `ClauseSatProof` | record per clause: the clause formula `ψ`, the literals with their disjunct and optional reversed rewrite proof, the source — or, for a trivially true clause, a ready-made proof of `{ψ}`. |
| **new** `ModelProofBuilder` | assembles the final model proof at sat time (see below). |
| `MinimalProofChecker` | accept `defineFun` for aux symbols inside model proofs; keep `checkModelProof` as the single acceptance criterion.  Factor out the clause-per-node computation (`getProvedClause`) — the assembler and the debug checks need it. |
| `PrintProof` | print the new annotation. |

### `convert` package

| Class | Change |
| --- | --- |
| `Clausifier` | the registries above, plus threading the sat proof through `buildClause`, `buildTautology`, `buildClauseWithTautology`, `buildAuxClause`.  `addAuxAxioms` stores under `negLit.negate()`. `createDefiningClausesForLiteral` supplies, per aux clause, the target and the per-literal `TAUT_*` dual proofs, and builds the record's start proof and pivots — see the table in "The aux-clause contract". |
| `buildAuxClause` | new parameters `Term[] target, Term[] litProofs`; returns the `ClauseSatProof`.  It still adds the aux literal directly (`bc.addLiteral(auxlit)`, no entry) and collects `params[1..]`, now each with its supplied proof.  All callers use it again (no `startAuxClause`, no copied scaffolding). |
| `AddAsAxiom` | the core new construction.  Its splits (`and` positive, `or`/`=>` negative, `xor`, `ite`, quantifier) currently derive children with `resolveBinaryTautology`; the sat direction must *join* the children's proofs back into the parent formula with the dual tautology — for quantifier nodes via `forallIntro`/`existsIntro` and a hyp at an instantiation, see "Quantified clauses and free variables".  Since `AddAsAxiom` pushes children onto `mTodoStack`, this needs a join `Operation` (analogous to how `BuildClause` performs after its literals are collected). |
| `BuildClause` | register `ψ_C` and the per-literal entries in `addLiteral(lit, origAtom, rewriteAtom, positive)` (all information is already there), and hand the proof "this node's formula from `ψ_C`" up to the parent.  Also the two quantifier paths: dual of `buildQuantifierProof`, and the DER path. |
| `CollectLiteral` | duals for each branch, all folded into the collected literal's proof (`ψ_C` stays as created): `or`/`=>`/`and` inlining (one `or+`/`=>+`/`and-` step per inlined literal), the `QuantifiedFormula` branch, the aux-literal branch, the `TermVariable` branch, the `MatchTerm` branch.  No sat proof has to be threaded *into* `collectLiteral`. |
| `AddTermITEAxiom`, `CCTermBuilder`, `EqualityProxy`, `LogicSimplifier`, `TermCompiler`, `SMTAffineTerm` | **no sat tracking.**  Term-level axioms (term-ite, div/mod, store, diff, ...) are tautologies: their clause formula is provable outright and never becomes a hypothesis.  The rewriters only produce equality proofs (see above). |

### `dpll` package

| Class | Change |
| --- | --- |
| `DPLLEngine` | nothing structural; the assembler needs the final assignment, available via `getDecideStatus` on the atoms.  Input clauses live in `mClauses`, but the records are kept clausifier-side, so learned-clause deletion is irrelevant. |
| `NamedAtom` / `ILiteral` | no change needed: the assembler decides "aux record vs. model evaluation" by looking the `ILiteral` up in `mLiteralSatProofs` — a hit *is* the aux-atom test. |

### `theory/quant` package

| Class | Change |
| --- | --- |
| `QuantClause` | a reference to its `ClauseSatProof` (target, per-literal entries, instantiation) and its closure, so the assembler can prove `{¬C} ∪ T` and `{C}`.  See "Quantified clauses and free variables". |
| `QuantifierTheory` | sat proofs for `createAuxLiteral` / `createAuxFalseLiteral`; and, at sat time, prove the closure `{(forall x⃗ ψ)}` per `QuantClause` (half 2, open — see "Quantified clauses and free variables"). |
| `DestructiveEqualityReasoning` (`DERResult`), `SubstitutionHelper` | the DER'd clause's record is derived from the original one, per literal: case split on `θx = t[θ'']` via congruence, discharged by the DER literal's proof, plus the reversed simplification rewrite.  See "DER stays in half 1". |
| `QuantLiteral`, `QuantEquality`, `QuantAuxEquality`, `SubstitutionHelper`, `QuantAnnotation` | carry the reverse intern proofs; mostly mechanical. |
| `InstantiationManager`, `InstClause` | instances are *consequences* of quant clauses, so they are not needed for the sat proof itself — only for the completeness argument (phase 4). |

### `theory/epr` package

Out of scope (the package is outdated and to be subsumed by `QuantifierTheory`).

### `model` package

| Class | Change |
| --- | --- |
| `ModelProver` | expose an atom-level entry point, e.g. `proveAtom(Term atom)` returning a proof of `{atom}` or `{¬atom}`, and keep `buildModelProof` as the fallback path.  The quantifier restriction becomes irrelevant: the new path never feeds it a quantified formula. |
| `Model` | expose whatever the assembler needs for the `refineFun` prefix (already `getDefinedFunctions`/`getFunctionDefinition`). |

### `smtlib2` / options / tests

- `SMTInterpol.getProof()`: in the `SAT` branch, use `ModelProofBuilder` when the
  tracker is a real `ProofTracker` (proof mode `FULL`/`LOWLEVEL`), otherwise keep
  `ModelProver.buildModelProof`.
- `SolverOptions`: option to select the mechanism (`:model-proof-mode`
  `evaluate` | `clauses`), plus a `Config.CHECK_MODEL_PROOF`-style self check.
- New test class (`SMTInterpolTest`) that runs sat benchmarks, calls `get-proof`
  and checks the result with `MinimalProofChecker.checkModelProof`.

## Assembling the proof at sat time

`ModelProofBuilder`, given the registries and the final assignment.  Two mutually
recursive, memoized procedures:

**`proveLiteral(l)`** returns a proof of the unit clause containing `l` as a
signed proof literal (`atom⁺` or `atom⁻`):

1. If `mLiteralSatProofs` has a record for `l` (aux literal), `proveFormula`:
   start with `mStart` (or the first hyp's proof), then resolve each
   `proveClause(mHyps[j])` on `mPivots[j]`.  If a hyp cannot be proved
   structurally (incomplete record), fall back to step 2 for the whole record.
2. Otherwise `l` is a theory or input atom: `ModelProver.proveAtom` for the
   atom's formula, in `l`'s polarity, converted once to the stripped clause
   convention (the only `not`-bridging left on the sat side).

**`proveClause(c)`** takes a `ClauseSatProof` and returns a proof of its target
`c.mTarget` (or of a subclause of it), memoized in `c.mAssembled`:

1. If `c.mReadyMadeProof != null` (trivially true clause), return it.
2. Otherwise pick a literal `l` of `c.mLiterals` that is *true* in the final
   assignment and call `proveLiteral(l)`; for a quantified clause the
   `QuantClause` obligation takes this place.
3. If `l`'s recorded proof is `null`, `l ∈ T` and the proof of `{l}` is the
   result; otherwise resolve it with the recorded `{¬l} ∪ T` on `l`.  No
   `orIntro` or index lookup happens here — the step from `l` to the target is
   part of the recorded proof.

Top level: for each asserted term (from `SMTInterpol.mAssertions`) resolve its
`mAssertionSatProofs` record's hypotheses with `proveClause`, giving `{φ_i⁺}`;
`andIntro` into `{(and φ_1 ... φ_n)}`; then prefix `defineFun` for aux function
symbols and `refineFun` for the model's function definitions — the format
`checkModelProof` expects.

Termination: records follow the subformula DAG, so the mutual recursion
terminates; memoization keeps shared formulas from being proved twice.  Guard
against cycles with a visited set in debug mode.

### No vacuous resolutions by construction

Every resolution the assembler performs has its pivot in both antecedents: a
record genuinely contains `¬ψ_j`, and `proveClause(ψ_j)` genuinely proves `{ψ_j}`.
So there are no `"Could not find pivot"` warnings
(`MinimalProofChecker.walkResolution`, line 391ff) and no cleanup pass is needed —
in contrast to the array/placeholder variant, where substituting the single true
disjunct for a whole clause makes the surrounding steps vacuous.

The flip side is that a record keeps *all* branches of its case split, because it
proves the general lemma rather than the model-specific one: in the example the
`ite+2` branch stays even though `c` is true, since we prove the whole `ψ_2` and
not just `c`.  Nothing is dead — both `¬ψ_j` hypotheses really are resolved away —
so this is a size overhead, bounded by the size of the clause set, not garbage.
If proof size ever becomes a problem, the model-specialized variant (array
placeholders plus a subsumption-aware `res`) is the fallback; it produces smaller
proofs at the cost of the machinery described above.

A `ProofDagCleaner` (bottom-up pass replacing a resolution by the antecedent that
lacks the pivot) is therefore not needed here.  It is still worth having as a
debug assertion ("cleaning changes nothing"), as insurance for proofs coming from
`ModelProver` or the quantifier layer, and for reuse on the `unsat` side of the
Resolute proofs, where nothing comparable exists (`RecyclePivots`/`FixProofDAG`
work on the old `Clause`-based proofs).

## Phases

**Phase 0 — groundwork.**  Audit rewrite-rule directionality; add the reverse
rewrite oracle + `ProofSimplifier` support; add the atom-level `ModelProver`
entry point; add the registries and the option/`getProof` switch; factor the
clause-per-node computation out of `MinimalProofChecker`.  Deliverable: nothing
user visible, but the new proof steps are checkable.

**Phase 1 — propositional core.**  `AddAsAxiom` join operation, `BuildClause`
clause formulas + literal entries, `CollectLiteral` duals, `ModelProofBuilder`.
Deliverable: model proofs for quantifier-free inputs without aux literals.
Test on small sat `QF_UF`/`QF_LIA` benchmarks.

**Phase 2 — Tseitin / aux literals.**  The `createDefiningClausesForLiteral`
companion (one case per function symbol) and the assembler's recursive aux
handling.  The lazy encoding needs no special care: only the polarity that was
actually added is ever used, because the record proves the subformula from its own
aux clause formulas rather than relating a fresh symbol to it.  What *does* need
care: `proveClause` must pick a true literal per aux clause exactly as for input
clauses, and memoization must keep the subformula DAG from being expanded twice.

**Phase 3 — theory atoms.**  Mostly testing: CC, LA, array, datatype and
bitvector atoms only differ in their intern rewrites, which are reused reversed.

**Phase 4 — quantifiers.**  Prerequisite: a model for quantified problems.
Today `Model` throws "Modelproduction for quantifier theory not implemented"
(`Model.java:106`), so `get-proof` is `unsupported` before any record is
used.  Then, following "Quantified clauses and free variables":
- the quantifier duals in `CollectLiteral` (replacing `poisonSatRecord`) and in
  `AddAsAxiom` (replacing the null record);
- the global `fresh variable → choose term` map, with targets and duals built
  instantiated, and `θ` on the quantified `ClauseSatProof`;
- the closure as the hypothesis of a `QuantClause` record (half 1: `forallElim`
  plus all literal entries, model-free), including the DER'd clause's record
  derived from the original one;
- the proof of each closure from the model (half 2, open; MBQI-style);
- the quant aux literals (records done, see "Quantified aux literals"; `@AUX`
  symbols stay in the proof and are expanded to their definition only where
  needed — the existing machinery, see artifact 3).

Half 1 can be built and checked before half 2 exists, with `{C}` as an
explicit hypothesis or oracle.

## Open questions

1. **Clause formula vs. clause array.**  Decided: one formula per clause, entering
   proofs as a negative literal.  See "Why clause formulas and not clause arrays"
   for the rejected alternative and the conditions under which it would win.
2. **Where do sat proofs live?**  (a) a second annotation (`:model-proof`)
   on the same proof-carrying terms, or (b) explicit records keyed by
   clause formula / aux literal / assertion.  Because rewrites are reversible, sat
   proofs are only needed at a few join points, so (b) is much cheaper.
   Recommended: (b).
3. **Scope of the obligation for quantified clauses.**  Decided: the universal
   closure of each `QuantClause` formula, with the quantifier theory responsible
   for it (see "Quantified clauses and free variables").  How the closure is
   proved from the model (half 2) is open; the expected source is an
   MBQI-style argument.
