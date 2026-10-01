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

Every clause `C` gets a **clause formula** `ψ_C`: one formula, the disjunction of
the clause's disjuncts as they were when the clause was created.  All tracked
proofs are ordinary Resolute clause proofs, and a clause formula enters a proof
as a *negative literal* — that is what "assuming the clause formula" means, and
no separate hypothesis or placeholder mechanism is needed.

1. **Per input assertion** (`Clausifier.addFormula`): a proof of
   `{¬ψ_1, ..., ¬ψ_n, φ}`, where `φ` is the asserted formula and `ψ_i` the clause
   formulas of the clauses created from `φ`.
2. **Per clause** (`BuildClause`): the formula `ψ_C`, plus for every literal `l`
   of the clause a proof of `{¬l, ψ_C}` ("this literal implies the clause
   formula").  This decomposes into two parts that are best kept apart:
   - the *reversed* intern/rewrite clause `{¬l, o_i}` from the DPLL literal to the
     disjunct it came from — nothing at all when the literal formula already *is*
     the disjunct;
   - one `orIntro` step from `{¬l, o_i}` to `{¬l, ψ_C}` — needed only for the one
     literal the assembler actually picks, so build it lazily at assembly time and
     record just the disjunct (or its index).

   **`ψ_C` is fixed when the clause is created** and everything the clausifier
   does afterwards (literal rewriting, `or`/`=>`/`and` inlining, interning) is
   absorbed into these per-literal proofs.  That is what lets the consumers of
   `ψ_C` (artifacts 1 and 3) be built at clause-creation time, before the literals
   are collected.  For an inlined disjunct `(or x y)` the entry for literal `x` is
   `{¬x, (or x y)}`, one extra `or+` step.
3. **Per auxiliary literal** (`Clausifier.createAnonLiteral`,
   `createQuantAuxTerm`, `QuantifierTheory.createAuxLiteral`): a proof that the
   aux literal is true — as an SMT-LIB formula, i.e. the subformula `ρ` it stands
   for — if the clause formulas of its aux clauses hold: `{¬ψ_1, ..., ¬ψ_m, ρ}`.

   The clause formula of an aux clause is the clause **without the aux literal**.
   Examples:
   - `ρ = (and a b c)`, aux clauses `{¬l, a}`, `{¬l, b}`, `{¬l, c}` with clause
     formulas `a`, `b`, `c`; the record `{¬a, ¬b, ¬c, (and a b c)}` is exactly the
     `and+` tautology.
   - `ρ = (or a b)`, one aux clause `{¬l, a, b}` with clause formula `(or a b)`,
     which already *is* `ρ`: the record is the identity, and the assembler can use
     the clause's proof of `{ψ}` directly as the proof of `{ρ}`.
   - `ρ = (ite c a b)`: see the worked example below.

   Artifact 2 applies to aux clauses unchanged, for every literal except the aux
   literal itself.

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
4. **Per quantified clause** (`QuantClause`): a proof that the quantified formula
   follows from the universal closure of the clause formulas of its
   `QuantClause`s.

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

Clause formulas (clause minus the aux literal):

| clause | rule | clause formula |
| --- | --- | --- |
| `{¬ρ, ¬c, a}` | `:ite-1` | `ψ_1 = (or (not c) a)` |
| `{¬ρ, c, b}` | `:ite-2` | `ψ_2 = (or c b)` |
| `{¬ρ, a, b}` | `:ite-red` | `ψ_3 = (or a b)` — **not recorded**, see below |
| `{ρ, d}` | input | `ψ_0 = (or (ite c a b) d)` |

- Artifact 3 (aux record for `l`): a proof of `{¬ψ_1, ¬ψ_2, ρ}`.  Note
  `ψ_1 ∧ ψ_2 ≡ (ite c a b)` — the general pattern: the conjunction of the clause
  formulas of one polarity is equivalent to the subformula.
- Artifact 2: `c`, `a`, `b`, `d` are Boolean constants, so no interning happens
  and only the disjunct is recorded per literal; the `or+` step is added at
  assembly for the picked literal.  With `a` replaced by `(<= (+ x 1) y)` the
  recorded part would be the reversed intern clause
  `{¬(<= (+ x (- y) 1) 0), (<= (+ x 1) y)}`.
- Artifact 1 for the assertion: `{¬ψ_0, (or (ite c a b) d)}` — the identity here,
  since the assertion *is* the clause formula.

### Deriving the aux record

**Confirmed correct (2026-09-29), after a detour.** This derivation concludes
`ρ` and is stored under `lit.negate()` — which is exactly right: whichever
occurrence triggers `addAuxAxioms(ρ, positive, …)` also adds `positive ? lit :
lit.negate()` to its own enclosing clause (`CollectLiteral`'s generic branch,
same call, same `positive`), so *that* occurrence needs exactly
`negLit.negate()` proven, not `negLit`. Here `positive=true`, so `negLit =
lit.negate()` and `negLit.negate() = lit` — matching this derivation's own
conclusion `ρ`. A same-session detour briefly "corrected" this to match the
*committed* `Clausifier.addAuxAxioms`, which stores under `negLit` unnegated —
but that is the actual bug (see "The `addAuxAxioms` key bug, and why
`buildAuxClause`'s own `ClauseSatProof` wires in cleanly once it's fixed",
further down), not a discrepancy in this worked example. `ProofTracker.wrapNot`
tracing during the detour was sound; it was checking the derivation against the
wrong (buggy) target, not against what `addAuxAxioms` should actually store.

Needed: the dual tautologies of the rules that built the clauses (`:ite+1`,
`:ite+2`, both already in `ProofConstants` and emittable with
`mTracker.tautology`), and one `orElim` per clause formula.  All pivots are
determined structurally, not by the model:

```
T1 = {ρ, ¬c, ¬a}                 ; ite+1
T2 = {ρ, c, ¬b}                  ; ite+2
E1 = {¬ψ_1, ¬c, a}               ; or-  (orElim on ψ_1)
E2 = {¬ψ_2, c, b}                ; or-  (orElim on ψ_2)

res(a, E1, T1)  =  {ρ, ¬c, ¬ψ_1}
res(b, E2, T2)  =  {ρ, c, ¬ψ_2}
res(c, …, …)    =  {ρ, ¬ψ_1, ¬ψ_2}      ← the aux record
```

No new checker support is required: `ProofSimplifier.convertTautIte1Helper`
(line 580) and `convertTautIte2Helper` already take a polarity flag and handle
`:ite+i` and `:ite-i` alike.

The negative occurrence (`addAuxAxioms(ρ, false, …)`, branch at line 1061) is the
mirror image: clauses `{ρ, ¬c, ¬a}`, `{ρ, c, ¬b}` with clause formulas
`ψ_1' = (or (not c) (not a))` and `ψ_2' = (or c (not b))`, concluding `¬ρ`
(`positive=false` ⟹ `negLit = lit` unnegated ⟹ `negLit.negate() = ¬ρ` — the
mirror image of the positive case above). Same shape as the positive case, not
a different pattern: `E1' = orElim(ψ_1')`/`E2' = orElim(ψ_2')` from *this*
branch's own two `buildAuxClause` clauses, resolved against two *fresh* dual
tautologies `T1' = {¬ρ, ¬c, a}`/`T2' = {¬ρ, c, b}` (`:ite-1`/`:ite-2` as
oracles, built the same way `T1`/`T2` were above — not obtained by reusing the
*other* branch's actual DPLL clauses, even though `T1'`/`T2'` happen to be
structurally identical to that branch's `axiom1`/`axiom2`; each branch is
independently derivable, so neither depends on the other having been
triggered). Case-split on `c` exactly as before, concluding `{¬ρ, ¬ψ_1', ¬ψ_2'}`.

### Signatures and registries

The case distinction on `c` is hard-coded where the clauses are created, and so
are the duals — which are neither per literal nor even per clause:

- `and` for `(and a b c)`: three aux clauses, **one** shared dual `and+`;
- `or` for `(or a b)`: **one** aux clause, **two** duals `or+ 0`, `or+ 1`;
- `ite`: two clauses, two duals, plus a case split belonging to neither.

So the sat-side structure is per *case* and belongs to a companion of
`createDefiningClausesForLiteral`, right where the rule — and hence its dual — is
known. `buildAuxClause` returns the record object for the clause it creates, so
the companion can reference it — **confirmed correct** (a same-session detour
briefly rejected this; see "The `addAuxAxioms` key bug" further down for why
the detour's own premise was the actual bug, not this signature):

```java
/** @return the (still empty) record for this clause, whose formula is the `or` of
 *          params[1..] of the axiom; null if sat proofs are off. */
public ClauseSatProof buildAuxClause(ILiteral auxlit, Term axiom, SourceAnnotation source)
```

and the `ite` branch of the companion reads:

```java
final Term axiom1 = mTracker.tautology(or(litTerm, not(c), a), TAUT_ITE_NEG_1);
final ClauseSatProof cl1 = buildAuxClause(lit, axiom1, source);   // ψ_1 = (or (not c) a)
final Term axiom2 = mTracker.tautology(or(litTerm, c, b), TAUT_ITE_NEG_2);
final ClauseSatProof cl2 = buildAuxClause(lit, axiom2, source);   // ψ_2 = (or c b)
// {¬ψ_1, ¬ψ_2, ρ}
final Term satProof = mTracker.resolve(c,
        mTracker.resolve(b, orElim(cl2.mFormula), mTracker.tautology(or(ρ, c, not(b)), TAUT_ITE_POS_2)),
        mTracker.resolve(a, orElim(cl1.mFormula), mTracker.tautology(or(ρ, not(c), not(a)), TAUT_ITE_POS_1)));
mLiteralSatProofs.put(lit.negate(), new FormulaSatProof(satProof, new ClauseSatProof[] { cl1, cl2 }));
```

`ProofTracker.resolve` already exists and handles the pivot polarity.  The
committed `createIteSatProof` instead derives `¬ρ`, stored under `lit` — because
the committed `addAuxAxioms` stores under `negLit` (= `lit`) instead of
`negLit.negate()`; once that's fixed (see below), `createIteSatProof` should be
rewritten to match this sketch, using `buildAuxClause`'s own returned records
(`cl1`/`cl2`) instead of independently-proven `psi1`/`psi2` placeholders.

The two scoped registries in the `Clausifier`, both `ScopedHashMap` like
`mLiterals` so `push`/`pop` work:

| registry | key → value | written by |
| --- | --- | --- |
| `mLiteralSatProofs` | aux `ILiteral` → proof of `{¬ψ_1..¬ψ_m, lit}` + its clause records | the `createDefiningClausesForLiteral` companion |
| `mAssertionSatProofs` | asserted term `φ` → proof of `{¬ψ_1..¬ψ_n, φ}` + its clause records | `addFormula` |

Keying literal records by `ILiteral` keeps the two polarities of an aux term
apart (`addAuxAxiomsQuant` creates both, `auxTrueLit`/`auxFalseLit`) and, more
fundamentally, keeps negative literals `ρ⁻` distinct from positive `(not ρ)⁺`
terms — see "Registries and the clause record", which also explains why clause
records are reached by reference instead of through a ψ-keyed map.

**Edge case — trivially true clauses.**  `BuildClause.perform` returns early when
`mIsTrue` (a `true` literal, or a complementary pair), so no clause reaches the
engine and no literal of it can be picked from the assignment.  `ψ` is then valid,
so `BuildClause` fills in `mReadyMadeProof` instead of the literal map.  A `false`
literal is the benign direction: dropped from the DPLL clause, still a disjunct of
`ψ`, and never picked.

### Two observations this example makes concrete

1. **The record uses a sufficient subset of the aux clauses.**  `ψ_3` from the
   redundant ite clause is implied by `ψ_1 ∧ ψ_2` and is left out, so the
   assembler never has to prove it.  Redundant/optional clauses must therefore be
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

- `{ψ_1}`: true literal `a` → `res(a, proof_of_a, {¬a, ψ_1})` where the second
  antecedent is `or+ 1` on `ψ_1`;
- `{ψ_2}`: true literal `c` → `res(c, proof_of_c, {¬c, ψ_2})` (`or+ 0`);
- `{ρ}`: resolve the aux record with those two on `ψ_1`, `ψ_2`;
- `{ψ_0}`: true literal `ρ` → `res(ρ, {ρ}, {¬ρ, ψ_0})`;
- `{φ}`: resolve artifact 1 with `{ψ_0}` on `ψ_0` — the identity step here.

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

- **aux literals**: `mLiteralSatProofs.get(l)` proves `{ψ⁻…, atom^±}` with the
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
/** aux literal → proof of {¬ψ_1..¬ψ_m, lit}, lit as a signed proof literal. */
private final ScopedHashMap<ILiteral, FormulaSatProof> mLiteralSatProofs = new ScopedHashMap<>();
/** asserted term φ → proof of {¬ψ_1..¬ψ_n, φ}. */
private final ScopedHashMap<Term, FormulaSatProof> mAssertionSatProofs = new ScopedHashMap<>();

static class FormulaSatProof {
    final Term mProof;             // {¬ψ_1..¬ψ_m, conclusion}; null == identity (m == 1)
    final ClauseSatProof[] mHyps;  // the clauses proving ψ_1..ψ_m, by reference
}
static class ClauseSatProof {
    final Term mFormula;                // ψ — fixed by the consumer up front
    Term mReadyMadeProof;               // != null: proof of {ψ} needing no model input
    Map<ILiteral, SatEntry> mLiterals;  // else: per literal, how to reach ψ
    Term mAssembled;                    // memo for the assembler
}
/** the disjunct of ψ a term/literal descends from, and a proof of {¬it, disjunct}. */
static class SatEntry { final Term mDisjunct; final Term mProof; }
```

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

| created by | ψ | record |
| --- | --- | --- |
| `buildTautology`, `buildClause(rule, …)`, `buildClause(tautologyProof, …)` — theory axioms | — | **none**: these clauses are never a hypothesis of any record (they constrain the model, they do not derive the input), so they need no sat tracking at all |
| `buildAuxClause` | clause minus the aux literal | literal entries; owned by the aux `FormulaSatProof` — see "The `addAuxAxioms` key bug" below for why this only works once that key is fixed |
| `buildClause(term, source)` (via `AddAsAxiom`) | the collected formula | literal entries; owned by an assertion `FormulaSatProof` |

`mReadyMadeProof` covers the `mIsTrue` case, where no clause reaches the engine:
a `true` disjunct gives `res(true, trueIntro, {¬true, o_i})` + `orIntro`, and a
complementary pair `l`/`¬l` gives `res(atom, {¬l, o_i}, {l, o_j})` + two
`orIntro`s — both built from the entries already recorded.

### `buildAuxClause`

Returns the `ClauseSatProof` for the clause it creates, exactly like
`buildClause`. A same-session detour briefly concluded this couldn't be wired
into `createDefiningClausesForLiteral`'s own record and reverted this to `void`
— that conclusion was itself downstream of a real bug in `addAuxAxioms` (see
"The `addAuxAxioms` key bug" below), not a problem with returning the record.
The clause formula is `params[1..]` of the axiom, and the aux literal at
`params[0]` is excluded for free (added directly, `bc.addLiteral(auxlit)`, no
`SatEntry`):

```java
public ClauseSatProof buildAuxClause(final ILiteral auxlit, final Term axiom, final SourceAnnotation source) {
    final ApplicationTerm orTerm = (ApplicationTerm) mTracker.getProvedTerm(axiom);
    assert orTerm.getParameters()[0] == auxlit.getSMTFormula(orTerm.getTheory());
    final Term[] params = orTerm.getParameters();
    final Term clauseFormula = !satProofsEnabled() ? null
            : params.length == 2 ? params[1]
            : mTheory.term("or", Arrays.copyOfRange(params, 1, params.length));
    final ClauseSatProof csp = clauseFormula == null ? null : new ClauseSatProof(clauseFormula);
    final BuildClause bc = new BuildClause(this, axiom, source, csp);
    pushOperation(bc);
    bc.addLiteral(auxlit);          // no SatEntry: excluded by construction
    for (int i = params.length - 1; i >= 1; i--) {
        bc.collectLiteral(params[i]);
    }
    return csp;
}
```

### The `addAuxAxioms` key bug, and why `buildAuxClause`'s own `ClauseSatProof` wires in cleanly once it's fixed

**Root cause found (2026-09-29), after a same-session detour that initially
concluded the opposite.** The detour traced, correctly, that for the committed
`Clausifier.addAuxAxioms` — which computes `negLit = positive ? negLit.negate()
: negLit` and stores `mLiteralSatProofs.put(negLit, satProof)` — a branch's own
aux clauses always prove the *opposite* polarity of what gets stored under
`negLit`. That trace was right. The conclusion drawn from it — "so
`buildAuxClause`'s own `ClauseSatProof` can't be wired in" — was wrong, because
`negLit` is the **wrong key**: `addAuxAxioms` should store under
`negLit.negate()` instead, and once it does, the branch's own aux clauses prove
*exactly* that.

**Why `negLit.negate()` is the right key.** Whichever occurrence triggers
`addAuxAxioms(term, positive, source)` also adds `positive ? lit : lit.negate()`
to its own enclosing clause — same call, same `positive`, in
`CollectLiteral`'s generic branch (`mClauseBuilder.addLiteral(positive ? lit :
lit.negate(), idx, rewrite, positive)`, right after the `addAuxAxioms` call).
So *that* occurrence is the one that will eventually need this literal proven,
and `negLit.negate()` equals exactly that literal in both cases:
- `positive=true`: `negLit = lit.negate()`, so `negLit.negate() = lit` — matches.
- `positive=false`: `negLit = lit` (unchanged), so `negLit.negate() = lit.negate()` — matches.

`negLit` itself, the key the committed code actually uses, is what the *other*
polarity's occurrence would need — but that occurrence, if it exists at all, is
served by its *own*, separate `addAuxAxioms` call (see below), not by this one.

**Once the key is fixed, each branch's own aux clauses are exactly what its
record needs — self-contained, no cross-polarity reuse, no model-dependent
search.** Two shapes, symmetric across `or`/`and`/`=>` (and a third, related
shape for `ite`/`xor`/`match`):

1. **A single aux clause whose own `ψ` already is the target.** `or` negative
   (`ρ = (or l1..ln)`, clause `{¬ρ,l1,..,ln}`, fires when `ρ` occurs positively)
   is this shape: `ψ` — the clause's own disjuncts, excluding the aux literal —
   is *syntactically* `ρ` itself, since the Tseitin clause's other literals *are*
   the term's own params. The record is the pure identity:
   `new FormulaSatProof(null, new ClauseSatProof[] { buildAuxClause(...) })`. This
   is exactly the shape in the user's own `(or l1..ln)` example, and exactly what
   the pre-existing artifact-3 example above (`ρ = (or a b)`) already said.
   `createExcludedMiddleSatProof`'s (`QuantEquality`) two branches are this shape
   too — its 2-literal clauses' own `ψ` (a single bare literal) already is the
   target, for the same reason.

   **`and` positive and `=>` negative *do* get this treatment too — a same-session
   detour briefly concluded otherwise, and that detour was wrong.** The detour's
   mistake was assuming these clauses had to go through `buildAuxClause`'s
   *generic* collection convention (`ψ` = the "or" of the collected literals,
   via the uniform `collectLiteral(term)` one-arg overload) — which does force
   `ψ = (or ¬l1..¬ln)` for `and` positive's clause `{ρ,¬l1,..,¬ln}`, only
   De-Morgan-equivalent to `¬ρ`, with no model-independent term-to-term rewrite
   between the two. But `BuildClause`/`CollectLiteral`'s `SatEntry` mechanism
   (see "`BuildClause` and `CollectLiteral`" below) was *already* built, earlier
   this same session, to support exactly this situation: `collectLiteral(term,
   disjunct, satProof)` lets each collected literal descend from an *arbitrary*
   disjunct via an arbitrary bridging proof, not only from itself via `or`-intro.

   So `and` positive's clause does not have to use the generic collection at
   all: build it with `ClauseSatProof(mFormula = ¬ρ)` directly, and collect each
   `¬l_i` via `collectLiteral(¬l_i, ¬ρ, andElim(i, ρ))` instead of the generic
   `collectLiteral(¬l_i)` — `andElim(i, ρ) = {¬ρ, +l_i}` is *exactly* a proof of
   `{¬(¬l_i), ¬ρ}`, the shape `SatEntry` wants, for every `i`, with no dependency
   on which one the model actually picks: `proveFromLiterals` still just asks
   "which literal of this clause is set true", and whichever one it is already
   carries the right disjunct (`¬ρ`) and the right bridge (`andElim` at that same
   `i`) attached at construction time. No search, no `ModelProver`. `=>` negative
   is the mirror: `{¬ρ,¬t1,..,¬t(n-1),tn}`, each `¬t_i` (`i<n`) collected via
   `collectLiteral(¬t_i, ρ, impIntro(i, ρ))`, `tn` via `collectLiteral(tn, ρ,
   impIntro(last, ρ))` — same shape, same elimination of the search. This closes
   the gap left by the detour: **all six branches (`or`/`and`/`=>` × 2
   polarities) are search-free**; `Clausifier.NWayKind` and
   `ModelProofBuilder.proveNWay` have been deleted entirely (not retargeted).

   **Implemented and verified (2026-10-01).** One sign/convention detail the
   derivation above glosses over, confirmed only by actually running it (same
   pitfall class as the `ite`/`xor` `wrapNot` issues found earlier): `andElim`/
   `impIntro` use their literal **opaquely** (`andElim(i,ρ)`'s `+l_i` is the raw
   term `l_i` with a sign annotation, not `l_i`'s "not"-stripped core at a
   tracked sign), but `collectLiteral`'s `SatEntry` — and everything
   `ModelProofBuilder.proveFromLiterals` later does with it — expects the
   **stripped** convention (the literal's core atom, with its leading "not"s
   peeled off and folded into the sign). Passing `andElim`/`impIntro`'s result
   straight through as `satProof` produces a proof that looks right but fails
   `checkModelProof` with "could not find pivot" the moment the collected
   literal (`l_i`/`t_i`) itself happens to already be a "not"-headed term (e.g.
   compiled from `>`) — exactly the inputs the regression tests
   (`testAndNWayNegative`, `testImpliesNWayPositive`) were written to exercise.
   The fix is one `stripNot` call per literal before attaching it:
   `tracker.stripNot(l_i, true, tracker.andElim(i, ρ))` for `and` positive (sign
   always `true`, matching `andE`'s checker), `tracker.stripNot(t_i, i < n-1,
   tracker.impIntro(i, ρ))` for `=>` negative (sign `true` for premises, `false`
   for the last/conclusion index, matching `impI`'s checker exactly —
   `CoreRules.andE`/`impI` are worth reading directly rather than trusting a
   remembered signature). `stripNot` is a no-op when the literal has no leading
   "not" of its own, so this one call is correct uniformly, not just a special
   case.

2. **`N` separate small clauses, combined by a conjunction-style checked axiom
   needing all `N`.** `and` negative (`{¬ρ,l_i}` per `i`, fires when `ρ` occurs
   positively) is exactly the pre-existing artifact-3 `(and a b c)` example: each
   clause trivially proves `l_i` (`ψ_i = l_i`, the identity — "if that literal
   happens to be `l_i`, its `ClauseSatProof` is empty"), and `andIntro(ρ)`
   resolved against all `n` of them, all built by *this same* `addAuxAxioms`
   call, concludes `ρ` — no search, no `ModelProver`, no dependency on the other
   polarity ever having been triggered. `or` positive is the dual (`orElim(ρ)`
   against all `n` clauses' own `¬p_i`, concluding `¬ρ`). `=>` positive is the
   same pattern with mixed signs (`t_i` for `i<n`, `¬t_last`, via `impElim`).

   This *replaces* the old `NWayKind`/`ModelProver.evaluateBoolean`-driven search
   for these three cases: there is no "which of the `N` clauses applies"
   question to defer to assembly time, because *all* `N` are hypotheses, not
   alternatives. (`and` positive and `=>` negative are single-clause, not
   `N`-separate-clauses, so this specific shape doesn't apply to them — but
   point 1 above covers them too, via a custom per-literal disjunct instead of
   the generic one, with the same "no search" result.)

3. **`ite`/`xor`/`match`: two (or more) clauses, a case split belonging to
   neither.** Implemented and confirmed correct end-to-end: `buildAuxClause`'s
   own two (or more) clauses per polarity (`E1`/`E2`/`E_i` — read via `orElim`,
   opaque, no stripping) are resolved against two (or more) *fresh*,
   independently-derivable dual-tautology oracles (`T1`/`T2`/`T_i` — built via
   `tautology()`, which strips internally, so each of *their* literals needs
   `wrapNot` back to opaque form) — not obtained from the other polarity's
   clauses, even where structurally identical. Self-contained in the same sense
   as shape 2, just with an extra case-split step instead of a flat conjunction.
   `match` generalizes the binary case split to `N` datatype constructors via
   `dtExhaust` (or the default case's own clause, which already has the
   completeness fact built in) exactly as originally planned.

**Sign conventions, confirmed by implementation, not just derivation.**
`wrapNot` must be called with the *exact* target literal each subsequent
`resolveAtom` needs — e.g. `wrapNot(thenTerm, false, t1)` directly, not
`wrapNot((not thenTerm), true, t1)` then a second bridging step — both are
individually valid (per `wrapNot`'s own not-counting-parity contract) but only
the direct form composes correctly with `orElim`'s opaque output without an
extra `notElim` round-trip *for the literal that fully cancels within one
branch*. The one literal that survives into the outer case-split (`cond` for
`ite`, `p1` for `xor`, `isTerm_i` for `match`) does need that extra
`resolveAtom(x, ., tracker.notElim(x))` bridge, because it has to unify with
the *other* branch's independently-built proof, which uses the bare form. This
was found by running the actual proof checker against real (deliberately
`>`-compiled, i.e. already-"not"-headed) test terms and reading its "could not
find pivot" diagnostics — not derivable with confidence from the API docs
alone, matching this codebase's established pattern for this class of bug.

**Why the aux literal itself never appears in `mLiterals`.** `ψ` is the clause
*without* the aux literal (`params[1..]` only) by construction, so the aux
literal's own truth plays no part in proving `ψ`: the clause is `{litTerm, o_1,
.., o_k}` with `litTerm` at whatever sign `lit` has, and `litTerm`'s own value is
exactly what the *record* (built from this clause plus, where needed, others)
establishes — not something this one clause could re-derive about itself.
Excluding it (`bc.addLiteral(auxlit)`, no `SatEntry`) is what lets the same
`ClauseSatProof` be read cleanly as "`ψ` from the other literals," with `litTerm`
folded in only via the surrounding `FormulaSatProof`.

### `createDefiningClausesForLiteral` and `addAuxAxioms`

`createDefiningClausesForLiteral` already switches on the function symbol, so each
branch just builds its record proof and the method returns it — no separate
companion class needed, and (per the previous section) no `NWayKind`/search
mechanism either: every branch is self-contained from its own `buildAuxClause`
calls plus, for `ite`/`xor`/`match`, oracle-derivable case-split facts.

```java
private FormulaSatProof createDefiningClausesForLiteral(ILiteral lit, Term term, boolean negative,
        SourceAnnotation source) {
    ...
    } else if (at.getFunction() == t.mOr) {
        if (negative) {
            // one clause {litTerm, l1..ln}, ψ == "or"(l1..ln) == ρ: the identity
            final Term axiom = mTracker.tautology(t.term("or", litTerm, l1, .., ln), TAUT_OR_NEG);
            final ClauseSatProof csp = buildAuxClause(lit, axiom, source);
            return satProofsEnabled() ? new FormulaSatProof(null, new ClauseSatProof[] { csp }) : null;
        } else {
            // N clauses {litTerm, ~p_i}; each trivially proves ~p_i; orElim(term)
            // = {~term,+p_1,..,+p_n} wrapped per i (wrapNot(not(p_i), false, ..))
            // to match each hyp, combined lazily by proveFormula -- no search.
            final ClauseSatProof[] hyps = new ClauseSatProof[params.length];
            for (int i = 0; i < params.length; i++) {
                final Term axiom = t.term("or", litTerm, t.term("not", params[i]));
                final Term axiomProof = mTracker.tautology(axiom, TAUT_OR_POS);
                hyps[i] = buildAuxClause(lit, axiomProof, source);   // ψ_i == (not params[i])
            }
            if (!satProofsEnabled()) { return null; }
            Term proof = tracker.orElim(term);   // {~term, +p_1, .., +p_n}
            for (final Term p : params) {
                proof = tracker.wrapNot(t.term("not", p), false, proof);
            }
            return new FormulaSatProof(proof, hyps);
        }
    } else if (at.getFunction() == t.mAnd) {
        if (negative) {
            // N clauses {litTerm, t_i}; each trivially proves t_i (Example: "if
            // that literal happens to be li, its ClauseSatProof is empty");
            // andIntro(ρ) = {+ρ,~t_1,..,~t_n} already matches each hyp directly
            // (no wrapNot needed here) -- no search.
            final ClauseSatProof[] hyps = new ClauseSatProof[params.length];
            for (int i = 0; i < params.length; i++) {
                final Term axiom = mTracker.tautology(t.term("or", litTerm, params[i]), TAUT_AND_NEG);
                hyps[i] = buildAuxClause(lit, axiom, source);   // ψ_i == params[i]
            }
            if (!satProofsEnabled()) { return null; }
            final Term andIntroProof = tracker.andIntro(term);   // {+ρ, ~t_1, .., ~t_n}
            return new FormulaSatProof(andIntroProof, hyps);
        } else {
            // one clause {ρ, ~l1..~ln}: NOT the generic collection (which would
            // force ψ = "or"(~l1..~ln), only De-Morgan-equal to ~ρ) -- instead,
            // build the clause with ψ == ~ρ directly and collect each ~l_i with
            // its own custom disjunct/proof via the SatEntry mechanism, exactly
            // as andElim(i,ρ) = {~ρ,+l_i} already proves {~(~l_i), ~ρ}. Search-free:
            // whichever ~l_i the model sets true already carries the right
            // disjunct and bridge, attached at construction time, not looked up.
            final Term notRho = t.term("not", term);
            final ClauseSatProof csp = !satProofsEnabled() ? null : new ClauseSatProof(notRho);
            final Term axiom = mTracker.tautology(t.term("or", litTerm, not_l1, .., not_ln), TAUT_AND_POS);
            final BuildClause bc = new BuildClause(this, axiom, source, csp);
            pushOperation(bc);
            bc.addLiteral(lit);   // no SatEntry: excluded by construction, as in buildAuxClause
            for (int i = params.length - 1; i >= 0; i--) {
                // andElim(i,term) uses params[i] opaquely ({~term,+l_i}); collectLiteral's
                // SatEntry wants it stripped to its core atom at the flipped sign --
                // stripNot does that (and is a no-op when params[i] has no leading "not").
                final Term andElimProof = satProofsEnabled()
                        ? tracker.stripNot(params[i], true, tracker.andElim(i, term)) : null;
                bc.collectLiteral(t.term("not", params[i]), notRho, andElimProof);
            }
            return satProofsEnabled() ? new FormulaSatProof(null, new ClauseSatProof[] { csp }) : null;
        }
    } else if (at.getFunction().getName().equals("ite")) {
        if (negative) {
            final Term psi1 = t.term("or", t.term("not", cond), thenTerm);
            final Term psi2 = t.term("or", cond, elseTerm);
            final Term axiom1 = mTracker.tautology(t.term("or", litTerm, not(cond), thenTerm), TAUT_ITE_NEG_1);
            final ClauseSatProof cl1 = buildAuxClause(lit, axiom1, source);   // ψ_1
            final Term axiom2 = mTracker.tautology(t.term("or", litTerm, cond, elseTerm), TAUT_ITE_NEG_2);
            final ClauseSatProof cl2 = buildAuxClause(lit, axiom2, source);   // ψ_2
            if (!satProofsEnabled()) { return null; }
            final Term t1 = mTracker.tautology(or(ρ, not(cond), not(thenTerm)), TAUT_ITE_POS_1);   // fresh oracle
            final Term t2 = mTracker.tautology(or(ρ, cond, not(elseTerm)), TAUT_ITE_POS_2);         // fresh oracle
            return new FormulaSatProof(
                    resolve(cond, resolve(elseTerm, orElim(cl2.mFormula), t2),
                            resolve(thenTerm, orElim(cl1.mFormula), t1)),
                    new ClauseSatProof[] { cl1, cl2 });     // the redundant clause is not a hypothesis
        }
        ...   // negative=false: mirror image, its own two clauses + fresh :ite-1/:ite-2 oracles
    }
```

Every branch, both polarities, follows one of the two self-contained shapes from
the previous section — `identity`, `identity + one bridge`, or `N hyps + one
conjunction/case-split proof` — built entirely from `buildAuxClause`'s own
return values for *this* call's own clauses.

**`addAuxAxioms` stores under `negLit.negate()`, not `negLit`** — the bug found
above. The committed code has this backwards
(`Clausifier.java:1085`, `mLiteralSatProofs.put(negLit, satProof)`); fixing it is
the one-line change that makes every branch above valid:

```java
 public void addAuxAxioms(final Term term, final boolean positive, final SourceAnnotation source) {
     ...
     ILiteral negLit = getILiteral(term);
     negLit = positive ? negLit.negate() : negLit;
     final FormulaSatProof satProof = createDefiningClausesForLiteral(negLit, term, positive, source);
     if (satProof != null) {
-        mLiteralSatProofs.put(negLit, satProof);
+        mLiteralSatProofs.put(negLit.negate(), satProof);
     }
 }
```

`addAuxAxiomsQuant` does the same twice, for `auxFalseLit` and `auxTrueLit`.

### `BuildClause` and `CollectLiteral`

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

The `orIntro` from `{¬lit, disjunct}` to `{¬lit, ψ}` is *not* built here — the
assembler adds it for the one literal it picks.

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

### Quantified clause formulas

A `QuantClause`'s clause formula `ψ(x⃗)` has free variables, so it is not a
sentence and cannot be a hypothesis as it stands.  The hypothesis recorded in the
parent is its **universal closure** `(forall x⃗ ψ(x⃗))`; `BuildClause.buildQuantifierProof`
already builds that same closure for the unsat side (via `allIntro`), so the term
is at hand.

The per-`ILiteral` proofs `{¬l(x⃗), ψ(x⃗)}` are built exactly as in the ground case
— one `orIntro` on the disjunct — and simply contain free variables.  That is
sound to record as a *schema*: proof terms with free variables can be instantiated
with `theory.let(vars, terms, proof)` followed by `FormulaUnLet`, which is what
`ProofTracker.allIntro` (line 332ff) already does for skolem terms.  So one
recorded schema serves every instantiation.

Proving the hypothesis at assembly time:

```
forallIntro((forall x⃗ ψ))  =  {¬ψ[sk⃗/x⃗], (forall x⃗ ψ)}      ; sk⃗ = the choose terms
```

so what is needed is a proof of `{ψ[sk⃗/x⃗]}` — the clause formula at the choose
terms.  Two cases:

1. **A ground literal is true** (`QuantClause.hasTrueGroundLits()`): its schema is
   unaffected by the substitution, so instantiate `{¬l, ψ}` at `sk⃗`, resolve with
   `ModelProver`'s proof of `{l}`, and resolve into `forallIntro`.  No case
   distinction at all.  This is precisely the case for which
   `QuantifierTheory.checkCompleteness` (line 874) does *not* demand the
   almost-uninterpreted property.
2. **Otherwise, a case distinction over the choose terms.**  For variable `x_i`
   the candidate values are `QuantClause.getInterestingTerms()[i]` — always
   non-empty, and containing the lambda term for "any other value"
   (`QuantifierTheory.getLambda`, cf. the assertion at
   `InstantiationManager:1209`); `computeAllSubstitutions` (line 1199) already
   enumerates the combinations.  For each substitution σ the instance is satisfied
   and the instantiation manager knows which literal makes it true, so
   `{ψ[σ]}` follows from that literal's schema at σ plus the model proof of
   `{l[σ]}`.  Lifting from σ to `sk⃗` uses the case hypothesis `sk_i = t_i`
   (congruence on ψ).  The result is a case-split proof of `{ψ[sk⃗]}`, one branch
   per σ.

What case 2 additionally needs, and what is *not* obtainable from the model, is
**exhaustiveness**: the clause
`{sk_i = t_1, …, sk_i = t_m, <lambda case>}` for each variable.  That is the
almost-uninterpreted-fragment argument behind `checkCompleteness`, i.e. the real
research content of phase 4 — hence the staging: emit it as a `:quant-model`
oracle first so that everything around it is checkable, then replace it.

Note the difference from the ground case that forces all this: for a ground clause
*one* literal is true and that settles it; for a quantified clause "true" is a
property of each *instance*, so the witness literal varies with the instantiation.

### Quantified input formulas — dual tracking

The unsat side already tracks the whole quantifier pipeline; every step has a
checkable dual in `CoreRules` (line 483ff, 599ff), so the sat side is tracked
*in parallel*, step by step, and concludes the input formula **with its original
quantifier** from the closures of its `QuantClause`s:

| unsat step | rule | sat dual | rule |
| --- | --- | --- | --- |
| drop positive `forall` (fresh vars `y⃗`), `convertQuantifiedSubformula` | `:forall-` | rebuild it at the canonical choose terms | `forallIntro`, `{(forall x⃗ φ), ¬φ[sk⃗]}` |
| skolemize positive `exists` with `@skolem` terms | `:exists-` | `existsIntro` at those same `@skolem` terms | `{(exists x⃗ φ), ¬φ[t⃗]}`, any witnesses |
| `allIntro`: clause with free vars → closure (`buildQuantifierProof`) | `:forall+` | `forallElim`: closure → any instance | `{¬(forall y⃗ ψ), ψ[t⃗]}` |
| compile rewrite of the substituted body (`mCompiler.transform`) | `modusPonens` | the same rewrite reversed (`iffElim1`), as a schema in `y⃗` | |
| DER | `getTautForallNeg` + DER proof | case split on `x = t` (DERResult dual) | |

The join in `AddAsAxiom` for a positive-`forall` node then works like the other
splits, with instantiation instead of plain resolution.  The child record is a
schema in the fresh variables `y⃗`:
`{¬ψ_1(y⃗), ..., ¬ψ_n(y⃗), φ'(y⃗)}` (ground hypotheses unaffected).

1. Instantiate the whole child record at `sk⃗`, the canonical choose terms of
   `(forall x⃗ φ)` — `theory.let(y⃗, sk⃗, proof)` + `FormulaUnLet`, the same
   mechanism `ProofTracker.allIntro` (line 332ff) already uses.
2. Resolve with the reversed compile rewrite at `sk⃗`, giving `φ[sk⃗/x⃗]`.
3. Resolve with `forallIntro` — conclusion `(forall x⃗ φ)`.
4. Replace each instantiated quantified hypothesis `ψ_i[sk⃗]` by its closure via
   `forallElim(sk⃗)`: `{¬(forall y⃗ ψ_i), ψ_i[sk⃗]}`.

Result: `{¬(forall y⃗ ψ_1), ..., ¬(forall y⃗ ψ_n), (forall x⃗ φ)}` — the
assertion-side record with the closures as hypotheses.  The positive-`exists`
node is simpler: the child works on the skolemized body, which contains the
`@skolem` terms as ordinary ground terms, so no schema instantiation is needed —
one `existsIntro` with the `@skolem` terms as witnesses joins the child record
directly.  Negative occurrences mirror the two cases.  The nested-quantifier
branch of `CollectLiteral` (line 205ff) folds the same duals into the literal's
`SatEntry` descent instead.

The closures are exactly where the two halves meet: this record consumes
`{(forall y⃗ ψ_i)}`, and "Quantified clause formulas" above describes how the
quantifier theory proves it.  Two details to keep straight:

- **Variable plumbing.**  The closure stored by `buildQuantifierProof` quantifies
  over `clause.getFreeVars()`, which may be a subset of `y⃗` (DER may eliminate
  variables) and in an unrelated order; the `forallElim` substitution in step 4
  must map accordingly.  With DER the hypothesis is the closure of the *final*
  clause, and the DER dual is composed into the record before step 4.
- **Schema hygiene.**  Instantiating a proof schema via let/unlet substitutes in
  tautology parameters too, which is exactly right — but it means recorded
  schemas must never share `TermVariable`s across records.
  `convertQuantifiedSubformula` already creates fresh variables per occurrence,
  so this holds; worth an assertion.

## Call-site checklist

Every place that needs new code, from the inventory of existing call sites.

**`convert/Clausifier.java`**

| where | what |
| --- | --- |
| fields, `push`, `pop` (1914ff, 1933ff) | `mLiteralSatProofs`, `mAssertionSatProofs`, `satProofsEnabled()`, `beginScope`/`endScope` |
| `addFormula` (1867) | build the assertion record from the `AddAsAxiom` root, bridge the `modusPonens` rewrite (1895) in reverse, store it |
| `buildClause(Term, SourceAnnotation)` (883) | create the `ClauseSatProof` (ψ = the collected formula), pass it to `BuildClause`, return it to `AddAsAxiom` |
| `buildAuxClause` (829) | create the record with ψ = `or(params[1..])`, return it; every `createDefiningClausesForLiteral` branch uses it as one of its own hyps — see "The `addAuxAxioms` key bug" |
| `buildTautology` (874), `buildClause(Annotation, …)` (889), `buildClauseWithTautology` (900) | pass `null` — theory-axiom clauses need no record.  (`buildClauseWithTautology` is only used by `AddAsAxiom`'s `xor`/`ite` splits, whose sat side is the dual tautology in the join, not a clause record.) |
| `createDefiningClausesForLiteral` (979) | **the bulk of the work**: one record proof per branch — `or`, `=>`, `and`, `ite`, `xor`, `QuantEquality` fallback (986–1118), `MatchTerm` (1120ff), default (1179ff) |
| `addAuxAxioms` (922) | store the returned record under `negLit.negate()` |
| `addAuxAxiomsQuant` (950) | same, for both `auxTrueLit` and `auxFalseLit` |
| `addExcludedMiddleAxiom` (1311) | **no record** — it calls `buildAuxClause` but its clauses are tautologies that no record depends on; pass `null` |
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
| `Clausifier` | the registries above, plus threading the sat proof through `buildClause`, `buildTautology`, `buildClauseWithTautology`, `buildAuxClause`.  `addAuxAxioms` stores under `negLit.negate()`, not `negLit` (the key bug — see "The `addAuxAxioms` key bug"). `addAuxAxioms` / `addAuxAxiomsQuant` / `createDefiningClausesForLiteral` need the per-case companion (one branch per function symbol, mirroring its own structure) that builds the record from `buildAuxClause`'s own returned per-clause records plus, for `ite`/`xor`/`match`, fresh case-split oracles — see the `ite` example. |
| `buildAuxClause` | signature changes from `void` to `ClauseSatProof` (a same-session detour briefly reverted this to `void`, based on the `addAuxAxioms`-key bug above — see "The `addAuxAxioms` key bug" for why that conclusion doesn't hold once the key is fixed).  It already asserts `orTerm.getParameters()[0] == auxlit.getSMTFormula(...)` and adds the aux literal directly (`bc.addLiteral(auxlit)`), so `ψ` is the `or` of `params[1..]` and the aux literal is excluded from the literal proofs by construction; it now also builds the `ClauseSatProof`, passes it into `BuildClause`, and returns it. |
| `AddAsAxiom` | the core new construction.  Its splits (`and` positive, `or`/`=>` negative, `xor`, `ite`, quantifier) currently derive children with `resolveBinaryTautology`; the sat direction must *join* the children's proofs back into the parent formula with the dual tautology — for quantifier nodes via schema instantiation + `forallIntro`/`existsIntro`, see "Quantified input formulas — dual tracking".  Since `AddAsAxiom` pushes children onto `mTodoStack`, this needs a join `Operation` (analogous to how `BuildClause` performs after its literals are collected). |
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
| `QuantClause` | second proof field next to `mClauseWithProof`: the clause formula `ψ(x⃗)` with its per-`ILiteral` schemas, and the universal closure that the parent uses as hypothesis.  See "Quantified clause formulas". |
| `QuantifierTheory` | sat proofs for `createAuxLiteral` / `createAuxFalseLiteral`; and, at sat time, prove `{(forall x⃗ ψ)}` per `QuantClause` — via `hasTrueGroundLits()` where possible, else the case distinction over the choose terms using `getInterestingTerms()`, `getLambda` and `InstantiationManager.computeAllSubstitutions`.  Exhaustiveness of that case distinction is the almost-uninterpreted-fragment argument behind `checkCompleteness()` (line 871ff) — see phase 4. |
| `DestructiveEqualityReasoning` (`DERResult`) | DER is an equivalence on the universal closure (`∀x. x≠t ∨ φ(x)` ↔ `φ(t)`), so a dual proof exists: `forallIntro` plus a case split on `x = t`.  Needs a second proof field. |
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

1. If `mLiteralSatProofs` has a record for `l` (aux literal), resolve its
   hypotheses `¬ψ_j` with `proveClause(record.mHyps[j])` and return the result —
   for the identity record, just `proveClause(mHyps[0])`.
2. Otherwise `l` is a theory or input atom: `ModelProver.proveAtom` for the
   atom's formula, in `l`'s polarity.

**`proveClause(c)`** takes a `ClauseSatProof` and returns a proof of the unit
clause `{c.mFormula⁺}`, memoized in `c.mAssembled`:

1. If `c.mReadyMadeProof != null` (trivially true clause), return it.
2. Otherwise pick a literal `l` of `c.mLiterals` that is *true* in the final
   assignment and call `proveLiteral(l)`; for a quantified clause the
   `QuantClause` obligation takes this place.
3. Resolve the result with `{¬l, ψ}` — the recorded reversed rewrite clause
   followed by the `orIntro` step for `l`'s disjunct (a `notIntro` resolution in
   between when the disjunct is a negated term, cf. `CoreRules.java:100ff`) —
   giving `{ψ⁺}`.

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

**Phase 4 — quantifiers.**  `QuantClause` clause formula and per-literal schemas,
the DER dual, quant aux literals (`@AUX` symbols stay in the proof and are expanded
to their definition only where needed — the existing machinery, see artifact 3),
and `{(forall x⃗ ψ)}`.  Staging within the phase: (a) `forallIntro` plus the
`hasTrueGroundLits()` shortcut, which needs no case distinction at all; (b) the
case distinction over the choose terms with a `:quant-model` oracle for its
exhaustiveness, so everything around it is checkable; (c) replace that oracle by
the almost-uninterpreted-fragment argument of `checkCompleteness()`.

## Open questions

1. **Clause formula vs. clause array.**  Decided: one formula per clause, entering
   proofs as a negative literal.  See "Why clause formulas and not clause arrays"
   for the rejected alternative and the conditions under which it would win.
2. **Where do sat proofs live?**  (a) a second annotation (`:model-proof`)
   on the same proof-carrying terms, or (b) explicit records keyed by
   clause formula / aux literal / assertion.  Because rewrites are reversible, sat
   proofs are only needed at a few join points, so (b) is much cheaper.
   Recommended: (b).
3. **Scope of the obligation for quantified clauses** — is the intended
   statement "the universal closure of each `QuantClause` formula holds", with
   the quantifier theory responsible for it, or should the proof also justify
   *why* the finitely many instances suffice?
