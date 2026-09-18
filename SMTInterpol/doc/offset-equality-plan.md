# Offset Equalities in Congruence Closure

Standard congruence closure (CC) maintains equality classes: all members of a class
are equal.  With offset equalities a class becomes an *affine class*: every member
`t` has a known rational offset to the representative, `t = rep + t.mOffsetToRep`.
Plain equality is the special case offset `0`.

The motivation is tighter integration with linear arithmetic (LA).  Instead of LA
posting only zero-offset equalities to CC through the Nelson-Oppen shared-term
mechanism, LA can post `a = b + k` for any rational `k`, so CC merges the two terms
and fires the congruences immediately.  A numeric term is then represented by the
CCTerm of its *offset-free part* with the constant carried at the use site, which
also makes `f(x+5)` a first-class congruence argument.

This document describes the resulting design and its invariants.  The branch history
carries the incremental log (`git log --grep 'CC offset equalities'`); it is not
repeated here.

## The option

`:offset-equalities` (default `true`) switches the feature on and off; off restores
plain congruence closure, where every offset is `0` and a numeric term keeps its
constant.  The flag lives in `Clausifier` — the component that builds the terms — and
everybody else asks it:

```java
Clausifier.createOffsetEqualities()  ==  mOffsetEqualities && getCClosure() != null
CClosure.createOffsetEqualities()    ==  mClausifier.createOffsetEqualities()
```

Without a congruence closure there is no CCTerm that could carry an offset, hence the
second conjunct.  The option is not modifiable after `set-logic`, since it decides how
the very first term is represented.

Only two places *create* non-zero offsets: `CCTermBuilder`/`Clausifier` (split a
numeric term into offset-free part plus constant) and the `CCEquality` creation sites
(offset from the difference of the two sides' constants).  Everything else — union
find, pair hash, signatures, arrays, proofs, interpolation — is offset-uniform, so
with the option off the whole plumbing degenerates and the existing test suite keeps
exercising it in its trivial case.

## Representation

### CCTerm: weighted union-find

```java
Rational mOffsetToRep;   // this == mRepStar + mOffsetToRep
```

`mRepStar` points directly at the representative (no path compression — merges update
all `mRepStar` pointers), so `mOffsetToRep` is always exact, and a representative has
offset `ZERO` (asserted in `invariant()`).

Merging `lhs` into `this` with reason `r`:

```
diff  = value(lhs) − value(this)              // reasonDiff(r, lhs, this); 0 for a congruence
delta = diff − lhs.mOffsetToRep + this.mOffsetToRep      // value(srcRep) − value(destRep)
```

Every member of the source class gets `mOffsetToRep += delta`; `undoMerge` recovers
`delta` as `src.mOffsetToRep` (the source representative had offset `ZERO` before the
merge) and subtracts it again.  Signatures are rehashed *before* the offsets are
updated (and before they are restored), so `SignatureTrigger.recomputeHashCode` still
sees the old effective offset and shifts it by `delta`.

If the two terms are already in one class, the merge is consistent only if the
existing offset difference equals the reason's; a mismatch is a conflict (see
*Conflicts*).

### CCEquality

```java
Rational mOffset;        // getLhs() == getRhs() + mOffset
```

`getSMTFormula` renders `(= lhs (+ rhs offset))`, using a *flattened* sum: a nested
`(+ rhs offset)` where `rhs` is itself a sum would be re-parsed by the non-recursive
`Polynomial` as one opaque monomial, which was unsound (`bv/test04`).  All producers of
offsetted terms therefore go through `CCParameter.addConstant` /
`Clausifier.addConstantToTerm`.

`mDiseqReason` gained a companion `mDiseqOrientation`, recorded when the reason is set
(while the two sides are still in distinct classes): once they are merged,
`getRepresentative()` can no longer tell which side of the reason belongs to which side
of the equality.

### Function arguments: `CCParameter`

An argument of the shape `ccterm + constant` is *not* reified as its own CCTerm.  Doing
so (the rejected "option A") would require asserting the definitional tautology
`(+ x 5) = x + 5` and the proof machinery would have to discharge it as a leaf.
Instead the offset is intrinsic to the application:

```java
interface CCParameter {            // value == getCCTerm() + getOffset()
    CCTerm   getCCTerm();
    Rational getOffset();          // structural offset; ZERO for a bare CCTerm
    default CCTerm   getRepresentative();
    default Rational getOffsetToRep();          // getCCTerm().getOffsetToRep() + getOffset()
    default boolean  sameValueAs(CCParameter o);  // same rep AND same offsetToRep
    default CCParameter getValueKey();            // of(getRepresentative(), getOffsetToRep())
}
```

`CCTerm implements CCParameter` with offset `ZERO`, so the offset-free case allocates
nothing; `CCParameter.of(t, off)` returns the bare `t` for `off == 0`, making the
representation canonical (there is no `OffsettedCCTerm(t, 0)`).  `CCAppTerm.mArgs` is a
`CCParameter[]`, and `getArgParam(i)` is the only argument accessor — a caller that
wants the offset-free node must say `getArgParam(i).getCCTerm()`.

Only `ccterm + constant` benefits.  A genuine linear combination (`f(x+y)`, `f(2x+1)`)
still needs a shared CCTerm and gets its relationship through real LA propagation.

Two identities must not be confused:

- **value identity** `(getRepresentative(), getOffsetToRep())` — `sameValueAs`,
  `getValueKey()`.  It *changes on merge*, so it may only key a map that is rebuilt
  after merges (see *Arrays*).
- **structural identity** `(getCCTerm(), getOffset())` — `OffsettedCCTerm.equals`.
  Stable; this is what proof/interpolation keys use.

### SignatureTrigger

`f(a) = f(b)` needs `a = b + 0`, i.e. same representative *and* same effective offset
`getOffsetToRep()`.  Hash and equality therefore include the offset, with disjoint
salts (`2i` for the representative, `2i+1` for the offset) so the two contributions
cannot cancel.  `CongruenceTrigger` inherits this; `ReverseTriggerTrigger` keys the
watched argument value the same way, which is why the reverse-trigger machinery is
value-keyed for free.

### CCTermPairHash

An `Info` represents one relationship `value(A) == value(B) + mOffset`, so several
infos with the same endpoints but different offsets coexist (`a == b` and `a == b + 5`
are different facts).  `mOffset` is final and part of the key.

The hash must satisfy `hash(A,B,off) == hash(B,A,−off)` (same fact) while keeping
`(A,B,off)` and `(A,B,−off)` apart — cuckoo hashing degrades badly on structured
collisions.  `offsetHash` therefore orients the offset by comparing the two endpoints'
`hashCode()`s (not identity hashes, for determinism) and falls back to
`offset.abs().hashCode()` when they are equal.  `equals` tries both orientations.

On a merge of `srcRep` into `destRep` at `delta`, each entry `(srcRep, other, k)`
migrates to `(destRep, other, k − delta)`.  Entries between the two merged classes are
resolved directly: equalities at exactly `delta` are propagated *true*, all others are
propagated *false* — the latter with `mDiseqReason == null`, because no separating
literal is involved and the explanation is the path itself.

## CC ↔ LA

### Offset-free sharing

When offsets are on, the `LASharedTerm` of a numeric term shares the **offset-free**
value, 1:1 and value-consistent with the offset-free CCTerm.  Terms differing only by a
constant (`2x+4y+1`, `2x+4y+5`) collapse onto one shared entity; their distinctness
lives in the term layer and surfaces as the structural offset at a use site.  The
factor stays in the CC term, so `2x+4y` and `x+2y` are distinct CCTerms — factors are
LA's concern.

A full-value `LASharedTerm` was tried and reverted: the shared object and its CCTerm
must denote the *same* value for the Nelson-Oppen shared-term equality to be sound, and
every LA→CC step then had to un-bend the mismatch with `getTermConstant` (that bridging
is where the bugs were).  Full-value had only been adopted because MBTC grouped whole
terms by LA value; the real fix was to change what MBTC iterates over (below).

`Clausifier.addTermAxioms` is only ever called on offset-free terms (asserted), so the
`LASharedTerm`s and the `mCCTerms` keys are offset-free throughout, and a term with a
constant has no entry of its own — its value is produced at build time as the
`CCParameter` of the offset-free part plus the constant.  `Clausifier.share` guards
against sharing one CCTerm with CC twice (`ccTerm.getSharedTerm() != ccTerm`), since
several terms map onto the same offset-free CCTerm.

### LA → CC, entailed (checkpoint)

`fingerprintSharedVar` drops the constant part (the `null` key, holding the offset and
any fixed-variable contributions), so two shared terms collide when their *non-constant*
parts agree, i.e. they are provably equal up to a constant.  `propagateSharedEqualities`
recovers that constant from the (model-independent) value difference and propagates the
offset equality.  Notes:

- The guard is offset-aware: same class *and* matching offset means already known.  The
  `propagated` set dedups per representative pair, so the inconsistent
  same-class/different-offset case raises the offset conflict exactly once.
- An Int-sorted pair with a non-integral offset is refuted directly (the term
  `rhs + offset` cannot even be built), by inserting `lhs − rhs` into the tableau and
  letting bound propagation do the rest.
- The shared-term loop iterates a snapshot: propagating an offset equality synthesizes
  and shares `rhs + offset`, appending to `mSharedVars`.
- `pivotEqualities()` is enabled (it was dead code), driven by the `mDirtyEqualities`
  set that `setBound` fills when a basic variable becomes fixed, so fixed variables
  become nonbasic and their contribution collapses into the constant part.

### MBTC over clash slots

The equalities CC needs are not between whole numeric terms but between the argument
`CCParameter`s sitting at congruence and trigger positions — those carry their constant
structurally, so comparing *them* by value is correct even though the shared terms are
offset-free.  `CClosure.getNumericClashSlots()` therefore enumerates, on demand in
`finalCheck` (no persistent index, no backtracking lifecycle):

- **congruence source** — every numeric `(FunctionSymbol, argPosition)`, members
  `app.getArgParam(pos)` over all applications.  Necessary: plain congruence runs
  through `CongruenceTrigger`, never a reverse trigger, so a bare `f(a)`/`f(b)` clash
  has no other source.
- **reverse-trigger source** — the watched value of every installed reverse trigger with
  `getArgPosition() != -1` (a find trigger uses `-1` and is not a clash position).  This
  covers e-matching and is self-maintaining.
- **array element values** — one group per array sort, holding the select applications
  of `mSelects` and the values of `const` arrays.  `ArrayTheory` reads distinct classes
  as distinct values (weakeq-ext fingerprints, weakeq propagation), so two element
  classes that end up with the same model value would silently satisfy an array
  disequality.  Const and select values must be comparable to each other
  (read-const-weakeq), hence one group rather than per-(symbol, position) slots.  Store
  values need no entry: `addStoreAxiom` always asserts `(= (select (store a i v) i) v)`.

Members whose class has no shared term are dropped: such a class is free to receive a
non-clashing value at model construction.  A member is then replaced by its class's
shared term, offsetted to denote the same value (`clashSharedTerm`), *before* anything
else happens with it — relating the member terms instead would share them with LA as a
side effect of building the equality atom, and a fresh unconstrained LinVar can win
`CCTerm.share`'s merge-time comparison and become the class's shared term mid-check.

Two members of one slot with equal value in distinct affine classes get the offset
equality between them proposed (propagated if implied, suggested otherwise).  Both
"cannot happen" branches — a refuted `LAEquality`, a trivially false equality — throw
rather than dropping the proposal, which would let `finalCheck` report sat while the two
theories disagree.

MBTC sends equalities only; "not provably equal" is read as disequal by the other
theories.  The residual obligation is at model construction.

### Model construction

Distinct classes must keep distinct values, and with offsets a class is used at a whole
*range* of values (`value(rep) + offsetToRep` over its members and argument positions):

- `LinArSolve.choose`/`mutate` de-collide the offset-shifted clash-slot member values
  (`clashModelPoints`) in addition to the raw shared-term values.
- `ModelBuilder` collects the minimal and maximal use-site offset per numeric class.  A
  fresh value is shifted by the minimum, so the *smallest* use-site value is the fresh
  one, and `setModelValue` registers the largest.  Since `extendFresh` hands out values
  strictly above everything registered, the whole range stays clear.
- `getModelValue(CCParameter)` is the only accessor; the former
  `getModelValue(CCTerm)` silently returned the representative's value and dropped a
  member's offset.

`EqualityProxy.createAtom` eagerly creates and links the `LAEquality` for numeric
equalities when offsets are on: clash-slot MBTC only creates `LAEquality`s for terms at
argument positions, so a numeric disequality between other shared terms (two selector or
`div` results) would otherwise never reach LA, and model construction could violate it.

## Conflicts and proofs

### One explainer

Every offset cycle goes through `CongruencePath.computeMergeConflictCycle(lhs, rhs,
offset, equality, lhsDiseq, rhsDiseq, diseq, produceProofs)`, a bridge edge
`lhs = rhs + offset` plus the class paths that contradict a known disequality.  Three
knobs span all cases:

| knob | meaning |
|---|---|
| `lhsDiseq == rhsDiseq` | same-class (anti-cycle); otherwise cross-class |
| `equality == null` | congruence bridge (justified by the argument equalities); otherwise a literal |
| `diseq == null` | trivial/shared disequality (EQ/LA discharged); otherwise a literal carried positively |

`computeCycle` stays separate: there the two sides are already connected at exactly the
equality's offset, so no bridge is needed and the clause is the equality against the
path — a conflict when the equality is asserted false, the unit clause when it is
propagated true.  The wrappers in `CClosure` are
`computeAntiCycle`, `computeCongruenceAntiCycle`, `computeMergeDiseqCycle` and
`computeSharedConflictCycle`.

Two properties make this work:

- **Conflicts are reported before the graph is mutated.**  `CCTerm.merge` detects a
  forbidding disequality or a shared-term clash and returns *before* the equal edge,
  `mOldRep` and `mReasonLiteral` are set, so no add-then-undo dance and the union-find
  is pristine while the conflict is built.  Note that a `CCTermPairHash.Info` also holds
  equality literals and compare triggers, so the guard must test `mDiseq != null`, not
  just `info != null`.
- **Each half is built inside one class.**  `mOffsetToRep` is relative to a node's *own*
  representative, so a path spanning two classes mixes reference frames and yields
  garbage offsets.  This was behind every early cross-class offset bug.

### `SubPath.getParams(anchor)`

A `SubPath` stores offset-free CCTerms; `getParams(anchor)` renders them as
`CCParameter`s so that every node denotes the same value as the anchor.  The relative
offsets are intrinsic (`getOffsetToRep` differences), so the anchor only fixes the
absolute base.  Two rules:

- The anchor is the intended *start* and must be one of the two endpoints: `mVisited`
  keys paths by an undirected `SymmetricPair`, so the stored list may run either way and
  is reversed when the anchor is the stored last node.
- It asserts that the anchor shares the representative of every *numeric* node.  The
  legitimate cross-class paths (weak-array paths over distinct strong classes) are
  non-numeric and can never carry an offset, so they are exempt.

### Path collection order

`CCAnnotation` requires that later paths explain congruences on earlier ones.
`drainTodo` gets this from a re-enqueue discipline: a freshly seen pair is pushed back
*behind* the dependencies that `computePathNonRecursive` pushes to the front, so it is
collected after them.  Two consequences:

- The dedup set `mCollected` is a field, not per drain: `WeakCongruencePath` drains once
  per weak/main path and `computeCongruence` re-enqueues argument pairs unconditionally,
  so a subpath can resurface in a later drain and must not be appended twice.
- A path that is *inlined* into a weak path (or stitched by hand into a main path) is
  built with `computePathNonRecursive`, which returns it without caching it in
  `mVisited` and without adding it to `mAllPaths`.  Not caching it is deliberate: a later
  standalone request for the same edge then rebuilds it through the drain instead of
  short-circuiting to the already-collected branch ahead of its dependencies.

### Annotations and proof keys

`CCAnnotation` carries `CCParameter[][]` paths (a node renders as `x+2`), a
`CCParameter` diseq pair, and — for a weak path — the *select/const edge* that
justifies its single weak-congruence step (see below).  `CCProofGenerator` keys its
maps on `OffsetPair`, the *structural* offset between two CCTerms, which is the fact
itself rather than the offsets a particular rendering uses; a shifted argument equality
therefore has the same key and needs no bridging lemma.  `equals` tries both
orientations, which matters for a degenerate key (both sides the same term, as in a
same-class offset conflict) where `(t, t, off)` and `(t, t, −off)` are one fact.
`addAuxEquality` normalizes such a key's sign, so `1 != 0` and `1 != 2` share one clause
literal.  A congruence lemma itself is always offset-free: `f(a) = f(b)` holds at the
same offset on both sides, and carrying an offset would make the step one over `+`
rather than over `f`.

### Select/const edges in weakeq-ext

A weak-i path may contain one step that holds because a select equality
`select(a1,j1) = select(a2,j2)` (or `select(a,j) = v` for a `const v` array) does.  The
edge used to be re-derived by three consumers, each searching the clause equalities —
ambiguous once the justifying equality is offset-rendered.  It is now recorded by
`WeakCongruencePath.computeWeakCongruencePath` (the one place it is known) into
`CCAnnotation.mSelectEdges` and emitted as an optional third element of `:weakpath`.

Two shapes need care.  A select is always offset-free, so a select/select edge has
offset zero; only a **const value** can bring an offset in, and then the mixed variable
of the justifying literal denotes the value at *literal* level — the interpolant must
shift it to the edge (`OffsetLitInfo.getMixedBoundary`), or it is off by the offset
(`interpolation/arrayoffset010`).  And the edge is **trivial** when the const's value
*is* the select the other side holds (`(const (select b j))` next to `b`): then there is
no equality literal at all, the step is justified by the const axiom alone, and its
availability is that of the select term itself (`interpolation/constarr015`).

## Interpolation

`OffsetTerm` splits a term syntactically: a trailing constant summand of a `+`
application is the offset, and a wholly constant term splits into the base `0` plus its
value.  This is the exact inverse of term construction —
`TermCompiler.unifyPolynomial` canonicalizes a constant-carrying polynomial as
`addConstant(unifyPolynomial(constantFreePart), constant)` — so canonic compiler terms,
`addConstantToTerm` results and annotation flat terms are byte-identical per value, with
the constant last.  A producer that bypasses the unifier breaks this: `BvToIntUtils`
emitted `(+ x 255 (* -256 (div …)))` with the constant mid-sum and made
`resolveNeededEqualities` miss its clause literal, so all its polynomial exits now go
through the unifier.

`OffsetEqKey` is the resulting lookup key: the two offset-free parts plus the constant
between them, so `(= (+ x 5) (+ y 7))` matches the clause literal `(= x (+ y 2))`.  The
two parts are kept *separate* rather than subtracted into one difference polynomial, so
that unrelated edges whose differences coincide up to sign do not collide.  Splitting is
gated by the option and the consumers create keys through one helper each
(`ProofSimplifier.key`, `Interpolator.key`), so no call site can forget it: with offsets
off nothing is split, and `0 = 1` and `1 = 2` are two facts, exactly as the terms and the
proof generator see them.

`OffsetLitInfo` pairs a literal's `LitInfo` with the shift and orientation between the
literal and the instance in which it is used, and provides the two operations that need
them: `getMixedBoundary()` (the mixed variable lifted to instance level) and
`buildEQ(sharedTerm)` (the `EQ` placeholder, shifting the shared term back down).

## Arrays

Index handling is uniformly value-keyed: every index is read as a `CCParameter`
(`getIndexFromSelect`/`getIndexFromStore`) and every index-keyed map or set (`mSelects`,
`seenStores`, `nodeMapping`, `storeIndices`, `seenIndices`, `mArrayModels`, the
weakeq-ext `inverse` map) keys on `getValueKey()`.  That key changes on merge, which is
sound here only because `cleanCaches()` drops `mCongRoots` on every `setLiteral` of a
`CCEquality` and on every `backtrackLiteral`, so the weak-equivalence structures are
rebuilt after anything that can move a representative or an offset — within one rebuild
the keys are a fixed snapshot.

Value handling has three offset-sensitive spots:

- **Propagation guards** compare with `sameValueAs`, not by representative: two selects
  (or a select and a const value) in the same class at *different* offsets are not
  already equal — that is precisely the conflict, and dropping the lemma lost it
  (`array/trivdiseq001`).
- **The weakeq-ext fingerprint** stores element *value identities*.  With bare
  representatives, two arrays whose elements agree only up to a constant collided and
  extensionality propagated a spurious `a = b` — unsound, witnessed by
  `(not (= (store c i y) (store c i (+ y 1))))`.
- **Model values** pass `CCParameter`s to `getModelValue`, so a stored element is the
  true value and not the representative's.

An index disequality between two indices that share a CCTerm but differ by a constant is
unsatisfiable, so the disjunct is dropped from the lemma instead of building a
degenerate equality.

## Datatypes

Constructor arguments and selector results are read as `CCParameter`s, so
`dt-project`/`dt-injective` propagate the offset equality of a numeric field
(`cons(y+5) = cons(z)` gives `y+5 = z`).  A propagated equality whose two sides share a
CCTerm but differ by a constant is turned into a conflict directly.

`DataTypeTheory.checkpoint`/`finalCheck` run their rule passes to completion: a freshly
installed master reverse trigger only *queues* the activation on existing applications,
so a pass that concludes something from an empty application list must let CC catch up
and repeat.  Master reverse triggers are unified per engine (not globally), since
solver instances share the theory and its function symbols but need their own find
trigger registration, and the per-application `ReverseTriggerTrigger`s are remembered on
the app term so they are removed with it on pop.

## Quantifiers

The e-matching register holds *values*: `ICode.execute(CCParameter[], int)`,
`SubstitutionInfo` and the trigger registers are `CCParameter`-based, and `GetArgCode`
keeps the argument's offset (dropping it was the recorded unsoundness — matching `a(x)`
against `a(l+1)` and instantiating `x := l`).

- **Compare triggers** are keyed on the base-term pair plus the structural offset
  `δ = o2 − o1`, which is stable.  `insertCompareTrigger`/`removeCompareTrigger` mirror
  the `insertEqualityEntry` walk: negate `δ` on the merge-time swap, re-base when
  stepping to `t1.mRep`, and match `pentry.getOffsetToOther()`.  Merge-time activation is
  already offset-selective, and a trigger for a same-class/different-offset pair parks in
  the merge-boundary info and goes live again on unmerge.  `CompareCode` proceeds on
  `sameValueAs`, and drops the continuation when the two values share a base term at
  different offsets (they can never become equal).
- **Canonicalization** must keep offsets: `getRepresentativeTerm` returns the canonical
  *value* term (`getValueKey().getFlatTerm()`), otherwise `a` and `a+1` in one class
  would collapse to one substitution key.
- **Ground lookups** on possibly-offsetted terms go through
  `Clausifier.getCCParameter` / `CClosure.getCCParamRep`.  Equality evaluation is value
  based: `isEqSet` is `sameValueAs`, and `isDiseqSet` also holds for a same-class pair at
  different offsets (provably distinct by a non-zero constant), so the same-class case is
  fully decided between the two.

## Known gaps

1. **Datatype numeric-field MBTC feed.**  The speculative counterpart of the
   `DT_PROJECT` loop — clashing `sel_i(d)` against the i-th argument of a `cons` — has no
   clash slot, because `DataTypeTheory` installs its reverse triggers on the
   datatype-typed argument, which the numeric filter discards.  The hookup would register
   a reverse trigger at the constructor's numeric argument position `(cons, i)`.  No known
   soundness impact: the propagation itself fires once `d` is known equal to a `cons`, and
   model construction keeps distinct classes distinct.
2. **Offset patterns in e-matching** (the actual quantifier payoff).  With offsets, a
   pattern argument `x + k` is matchable — `GetArgCode` yields the value `v`, the binding
   is `x := v − k` — which would widen the almost-uninterpreted fragment
   (`isEssentiallyUninterpreted`, `containsArithmeticOnQuantOnlyAtTopLevel`) to constant
   offsets under function symbols.  Needs `PatternCompiler` support for affine arguments,
   a shift on the GetArg/Compare codes, and `QuantClause.addVarArgInfo` positions that
   record the shift.  Non-constant coefficients stay out.
3. **Invariants that are only asserted.**  `ProofSimplifier.resolveNeededEqualities`
   dereferences the clause disequality it asserts to exist, and
   `proveSelectOverPathStep` dereferences the annotated select edge; a violation is an
   NPE rather than a message.  Deliberate — both are internal invariants of the proof
   generator, and an NPE is a clear enough signal.

## Supporting changes

Three changes on this branch are not about offsets themselves but are needed by them,
and are worth knowing about because they affect all logics:

- **`TermCompiler.unifyPolynomial` canonicalizes a constant-carrying polynomial as
  offset-free part plus trailing constant.**  This is what makes the syntactic split in
  `OffsetTerm` exact (see *Interpolation*), and it changes the shape of every printed
  sum.  `BvToIntUtils` was the one producer bypassing the unifier and now goes through
  it.
- **Every binary equality literal is routed through `convertBinaryEq`**
  (`Clausifier.rewriteLiteral` from `CollectLiteral`), so an axiom built from terms
  rather than from converted input works for a Boolean or store-sorted equality too.
  `addStoreAxiom` no longer rewrites its own literal.  Tested by
  `array/diffbool00{1,2}` and `datatype/matchbool001`, where the diff and match axioms
  have a Boolean-sorted equality as their literal.
- **`DataTypeTheory` runs its rule passes to completion** (see *Datatypes*), tested by
  `datatype/selectortrigger001`: only once the rules have created the constructor terms
  are the field values arguments of a constructor application, which is what puts them
  into a clash slot.

`LinArSolve.pivotEqualities()` being enabled belongs in the same list; it is described
under *LA → CC, entailed*.

## Tests

- `array/{extmbtc001,extmbtc002}` — extensionality against the array element-value
  clash group; `array/trivdiseq001` — a read-over-weakeq lemma whose two trivial index
  disequalities are one fact and share a clause literal, so the proof of the other one
  multiplies it by −1; `array/trivdiseq002` — the same problem with
  `:offset-equalities false`, where they are *two* facts, which is what pins the proof
  and interpolant keys to the way the terms were built.
- `datatype/offset_lemmas` — dt-project and dt-injective over a numeric field.
- `interpolation/arrayoffset001..011`, `interpolation/trivdiseq004`,
  `interpolation/constarr015`, `interpolation/datatype/dt_{project,injective}_offset001`
  — offset interpolation, including the offsetted const select edge (010/011, both
  literal orientations) and the trivial const/select edge (constarr015).
- `lia/offset-equality-parity-conflict` — the LA→CC offset conflict.
- `model/{offset_lia,offset_datatype,offset_fresh001..003}` — model construction,
  fresh values against offsetted use sites.
- `quantified/offsetmatch001..003` — offset binding, `a`/`a+1` dedup distinctness,
  spurious-unsat guard.

`SystemTest` runs the whole corpus with `:proof-check-mode`, `:model-check-mode` and
`:interpolant-check-mode`, so every proof, model and interpolant above is machine
checked.  The corpus also passes with `:offset-equalities false`, which is what keeps
the classic mode honest.
