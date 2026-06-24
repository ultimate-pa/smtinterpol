# Offset Equality Extension for Congruence Closure

## Overview

Standard congruence closure (CC) maintains equality classes: all members of a
class are equal.  With offset equalities, a class becomes an *affine class*:
every member `t` has a known rational offset from the representative, meaning
`t = rep + t.mOffsetToRep`.  Plain equality is the special case offset = 0.

The main motivation is tighter integration with linear arithmetic (LA): instead
of LA posting only zero-offset equalities to CC via the Nelson-Oppen shared-term
mechanism, LA can post `a = b + k` for any rational `k`, allowing CC to merge
the two terms and potentially fire new congruences immediately.

---

## CCTerm — weighted union-find

Add one field:

```java
Rational mOffsetToRep;   // this == mRepStar + mOffsetToRep
```

`mRepStar` continues to point directly to the representative; no path
compression is used (merges already update all `mRepStar` pointers), so
`mOffsetToRep` is always exact.

### Merge with offset k  (`a = b + k`)

```
repA = a.mRepStar,  offsetA = a.mOffsetToRep   →  a = repA + offsetA
repB = b.mRepStar,  offsetB = b.mOffsetToRep   →  b = repB + offsetB

a = b + k  ⟹  repA + offsetA = repB + offsetB + k
           ⟹  repA = repB + (offsetB + k − offsetA)
```

Let `delta = offsetB + k − offsetA`.  When merging the smaller class (say
`srcRep = repA`) into the larger (`destRep = repB`), all members of `srcRep`'s
class get their `mOffsetToRep` shifted:

```java
Rational delta = offsetB.add(k).sub(offsetA);
for (CCTerm t : src.mMembers) {
    t.mRepStar      = destRep;
    t.mOffsetToRep  = t.mOffsetToRep.add(delta);
}
```

`undoMerge` restores both `mRepStar` and `mOffsetToRep` for all moved members,
which it already iterates over — no structural change needed there.

### Consistency check (already same class)

If `repA == repB`, require `offsetA == offsetB + k`; otherwise it is an
arithmetic conflict and a conflict clause must be generated.

### invertEqualEdges

Must accumulate and negate offsets as it reverses the equality-edge chain.

### Proof trail — no mEqualEdgeOffset needed

`mEqualEdge` from term `t` already points to one of the two specific CCTerms in
`mReasonLiteral` (either `getLhs()` or `getRhs()`).  Path reconstruction can
recover the edge offset without any extra field:

- If `t == eq.getLhs()`: `t = mEqualEdge + eq.mOffset`, contributing `+mOffset`
- If `t == eq.getRhs()`: `mEqualEdge = t + eq.mOffset`, contributing `−mOffset`

A pointer comparison against `eq.getLhs()` determines the direction at
reconstruction time.  `CongruencePath` therefore only needs to accumulate these
signed offsets as it walks the chain.

---

## CCEquality — offset equality atoms

Add one field:

```java
Rational mOffset;   // lhs == rhs + mOffset  (currently always 0)
```

All existing code that constructs `CCEquality` passes offset 0 and is
unaffected.  LA creates `CCEquality` objects with non-zero offsets when it
derives `a = b + k`.

---

## Offset arguments to function applications

For an argument of the shape `ccterm + constant`, e.g. `f(x+5)`, there are two
ways to represent the `+5`.

### Option A — reify a CCTerm for `x+5` (rejected)

Create a CCTerm for `x+5` and place it in `x`'s affine class at offset 5.
`CCAppTerm` and `SignatureTrigger` stay structurally unchanged; the argument is
an ordinary CCTerm whose `mOffsetToRep` happens to be 5.

The problem: to put `x+5` into `x`'s class, CC must assert the offset equality
`(+ x 5) = x + 5`.  This is a definitional **tautology**, and the proof
generator has to justify it as a leaf ("by definition of +").  Every
offset-shaped argument then costs one extra CCTerm **and** one tautological
offset equality that the proof machinery must discharge.

(Note: a *standalone* `(= y (+ x 5))` is not affected — it is simply the offset
equality `y = x + 5`, a genuine asserted fact, and creates no `x+5` CCTerm.)

### Option B — offset inside CCAppTerm (chosen)

Add a parallel offset array to `CCAppTerm`:

```java
Rational[] mArgOffsets;   // arg i represents mArgs[i] + mArgOffsets[i]; null if all zero
```

No CCTerm is created for `x+5`.  The effective offset of argument `i` for
signature purposes is `mArgs[i].mOffsetToRep + mArgOffsets[i]`.  Keeping the
field `null` when every offset is zero means the common (plain-CC) case costs
nothing.

The `+5` is now **intrinsic** to the term: the proof checker sees `f(x+5)` and
the offset is part of what the term is — there is no tautology to discharge.

`SignatureTrigger` carries the same structural offsets.  They are constants
fixed at term-creation time (they never change), so they need no backref
tracking; only `mArgs[i].mOffsetToRep` varies, so `recomputeHashCode`'s delta
logic is unchanged.

`CongruenceTrigger` handles both forms transparently.

### Scope

Option B only helps arguments of the shape `ccterm + constant`.  A genuine
linear-combination argument such as `f(x+y)` or `f(2x+1)` still needs a shared
CCTerm and obtains its offset relationship through real LA propagation — an
honest fact, not a tautology.

## SignatureTrigger — congruence detection

For uninterpreted functions, `f(a) = f(b)` only holds when `a = b + 0`, i.e.
same representative **and** same offset.  The signature hash and equality check
must therefore include the effective offset of each argument — that is
`mArgs[i].mOffsetToRep` plus the structural `mArgOffsets[i]` from the app term
(see Option B above).

Only `SignatureTrigger.computeHashCode()` and `equals()` need to change.
`CongruenceTrigger` extends `SignatureTrigger` and inherits both methods without
overriding them, so it picks up the fix for free.  `ReverseTrigger` is
independent (extends `SimpleListable`, not `SignatureTrigger`) and is
unaffected.

### computeHashCode

```java
public int computeHashCode() {
    int h = mId.hashCode();
    for (int i = 0; i < mTerms.length; i++) {
        CCTerm t = mTerms[i];
        h ^= HashUtils.hashJenkins(i, t.getRepresentative());
        h ^= HashUtils.hashJenkins(i, t.mOffsetToRep);   // add offset
    }
    return h;
}
```

`recomputeHashCode` needs a corresponding update to XOR out the old offset
contribution and XOR in the new one when a representative (and therefore its
offset assignment) changes.

### equals

```java
for (int i = 0; i < mTerms.length; i++) {
    CCTerm a = mTerms[i], b = other.mTerms[i];
    if (a.getRepresentative() != b.getRepresentative()) return false;
    if (!a.mOffsetToRep.equals(b.mOffsetToRep))         return false;
}
```

---

## CCTermPairHash — keyed by (lhs, rhs, offset)

### Design

Instead of a `Map<Rational, CCEquality>` inside `Info`, change the *key* of the
hash table to include the offset.  Each `Info` entry now represents one specific
relationship `lhs = rhs + offset`.  `mDiseq` and `mEqlits` remain a single
disequality and a flat list of equalities, all pertaining to that one offset.

The symmetry condition

```
hash(lhs, rhs, offset) == hash(rhs, lhs, −offset)
```

reflects that `lhs = rhs + k` and `rhs = lhs + (−k)` are the same fact.

### Canonicalization

Normalize at `Info` construction time: if
`System.identityHashCode(lhs) > System.identityHashCode(rhs)`, swap lhs↔rhs and
negate the offset.  The stored triple `(lhs, rhs, offset)` is then always in
canonical form, so `hashCode` is a straightforward function of the three fields
and `equals` is a direct comparison (no need to check both orientations at query
time).

`Info` gains one field:

```java
Rational mOffset;   // lhs == rhs + mOffset  (canonical form)
```

`getInfo(lhs, rhs)` becomes `getInfo(lhs, rhs, offset)`.

### Merge rehashing

When `srcRep` merges into `destRep` with offset `delta` (`srcRep = destRep + delta`),
each pair-info entry `(srcRep, other, k)` migrates to `(destRep, other, k − delta)`:

```
srcRep = other + k,  srcRep = destRep + delta
  →  destRep = other + (k − delta)
```

If an entry `(destRep, other, k − delta)` already exists, the equality and
disequality lists are joined and any conflict is checked — exactly the same
logic as today, just with the adjusted offset in the key.  Conflict detection
remains O(1): `getInfo(srcRep, destRep, k)` directly returns the relevant entry.

The zero-offset case is unchanged (offset = 0 throughout).

---

## CongruencePath / proof reconstruction

Walking the `mEqualEdge` chain accumulates signed offsets (see CCTerm section
above).  The final proof term asserts `a = b + Σoffsets` rather than `a = b`.
For the hyperresolution intermediate representation, offset-equality steps need
an offset parameter added to the existing equality step type (or a new step
type).

---

## LA interface

When LA derives an equality `a − b = k`, it currently posts to CC only if
`k = 0`.  With offset CC, LA can post it as a `CCEquality` with `mOffset = k`
for any `k`, allowing CC to merge the two terms immediately and fire congruences
that Nelson-Oppen would only discover through an additional round-trip.

The existing `share()` mechanism propagates to LA when two shared terms end up
in the same affine class with offset `k`: LA should be told `a − b = k` rather
than the bare equality `a = b`.

---

## Implementation strategy: one engine, one flag

Rather than maintaining a separate "no offset" code path, the engine carries
offsets **unconditionally**.  A single flag (`mCreateOffsetEqualities` on
`CClosure`) gates only the two places where non-zero offsets are *created*:

- `CCTermBuilder` / `addTermAxioms` — flag on: build the offset-free CCTerm
  (`factor·affine`) and remember the constant offset; flag off: build the
  whole-term CCTerm as today (offset 0).
- `createCCEquality` — flag on: `mOffset = o_b − o_a` from the `LASharedTerm`
  offsets; flag off: `mOffset = 0`.

Everywhere else (union-find, pair hash, signatures, proofs) is offset-uniform.
With every offset `ZERO` the arithmetic degenerates exactly to plain congruence
closure, so the existing test suite continuously exercises the offset plumbing
in its degenerate case.  The flag also doubles as the proof guard: default it
**off when proof generation is enabled** until offset-aware proof production
lands, then flip.

### CC↔LA sharing of offset-free terms

When offset equalities are enabled, a numeric term `t = affine + c` is
represented by the offset-free CCTerm for `affine`, and the **`LASharedTerm` for
`t` has offset zero** (it represents `affine`, not `t`). Only this offset-free
CCTerm is `share()`d with the offset-free `LASharedTerm`, so the CC↔LA
shared-term equality has equal values on both sides and stays sound. The full
term `t` gets no separate CC↔LA share — the constant `c` (recomputed from the
polynomial on demand) bridges CC (`affine + c`) and LA (`affine + c`), both
anchored on the shared `affine`. When the feature is off, `LASharedTerm` keeps
the constant as its offset and the whole term is shared, exactly as before.

### Entry pathway via LASharedTerm

The offset machinery already exists in `LASharedTerm` (it stores summands and a
`Rational` offset).  For `2x+4y+1` the normalized form is `factor·affine +
offset` with factor 2, affine `x+2y`, offset 1.  The CCTerm represents the
offset-free `factor·affine` (`2x+4y`, shared with an `LASharedTerm` of offset
0); the factor stays in CC's term (so `2x+4y` and `x+2y` are *distinct*
CCTerms — the factor is LA's concern, not CC's).  A `CCEquality` between two
LA-shared terms gets its offset from the difference of their `LASharedTerm`
offsets.

## Increment plan

1. **Weighted union-find foundation (done).** Added `CCTerm.mOffsetToRep`,
   `CCEquality.mOffset`, `CCAppTerm.mArgOffsets`; threaded the offset delta
   through `merge`/`mergeInternal`/`undoMerge` and added the same-class offset
   consistency check. Behavior-preserving (all offsets `ZERO`); no creation site
   emits non-zero offsets yet.
2. **Signatures + pair hash structure.**
   - **2a (done).** Offset in `SignatureTrigger` hash/equals/recompute (the
     effective offset is the term's offset to its representative plus the
     structural `CCAppTerm.mArgOffsets`); the offset delta is threaded through
     `rehashSignatures` and the merge/undo callers.
   - **2b (done).** `CCTermPairHash.Info` carries an offset; the cuckoo-hash key
     and `equals`/`getInfo` are offset-aware (offset hash invariant under
     negation, so `(A,B,off)` mirrors `(B,A,-off)`). Zero-defaulting overloads
     keep every existing call site querying offset 0, so it is behavior-
     preserving. The actual offset-threading through the call sites is deferred
     to increment 3, where it is testable.
3. **Creation sites + flag + call-site offset threading.** Implement the two
   flag-gated creation sites (offset-free CCTerms from `LASharedTerm`;
   `CCEquality.mOffset` from the offset difference) and, in the same increment,
   thread the context-derived offsets through `insertEqualityEntry`,
   `isDiseqSet`, `separate`/`undoSep`, `createCCEquality`, `backtrackComplete`,
   `removeCCEquality`, the merge-time propagation in `CCTerm.mergeInternal`/
   `undoMerge` (propagate the matching-offset eqlits as true, the others as
   negated), and `CompareTrigger.getOffset`. Then turn the flag on (off under
   proof generation). This is the first end-to-end testable increment.
4. **Proof production.** Offset-aware `CongruencePath` / `CCProofGenerator`
   (and proof checker), and the offset-conflict explanation stubbed in
   increment 1; then enable offsets under proof generation.

## Summary of files to change

| File | Change |
|---|---|
| `CCTerm.java` | Add `mOffsetToRep`; update `merge()`, `invertEqualEdges()`, `undoMerge()` |
| `CCAppTerm.java` | Add `mArgOffsets: Rational[]` (null when all zero) for offset-shaped arguments |
| `CCEquality.java` | Add `mOffset: Rational` |
| `CCTermPairHash.java` | Add `mOffset` to `Info`; canonicalize key; update `getInfo()` and merge rehashing |
| `SignatureTrigger.java` | Include `mOffsetToRep` in `computeHashCode()`, `recomputeHashCode()`, `equals()` |
| `CongruencePath.java` | Accumulate signed offsets along equality-edge chain |
| `CCProofGenerator.java` | Emit offset-equality proof steps |
| `CClosure.java` | Update `addEquality()` entry point; update `share()` to propagate offset to LA |
| `LinArSolve.java` | Post offset equalities (`k ≠ 0`) to CC, not only zero-offset equalities |

## Resume point

Branch `offsetequality`. Done and committed: increments 1, 2a, 2b, 3; the
deterministic pair-hash offset; the shared-term polynomial-flattening fix
(`test04`); the quantifier gate (`quanttest001`); the `CCParameter` /
`OffsettedCCTerm` abstraction with `getValueKey()`; and the `checkCongruence`
migration. **Also done (this session, gap 1, the array migration):**
`ArrayTheory` and `WeakCongruencePath` are now offset-aware — every array index
is read as a `CCParameter` (`getIndexParamFromSelect`/`getIndexParamFromStore`)
and all index-keyed maps/sets (`mSelects`, `seenStores`, `nodeMapping`,
`storeIndices`, `seenIndices`, `mArrayModels`, the weakeq-ext `inverse` map) key
on the value identity `getValueKey()` instead of the bare representative; index
comparisons use `sameValueAs`/`.equals(valueKey)`; index disequality literals in
array lemmas are offset-aware (`createIndexEquality` / `computeIndexDiseq` via
`createEquality(t1, t2, offset, …)`, dropping the always-false disjunct when the
two indices share a CCTerm but differ by a constant); and `ModelBuilder` gained a
`getModelValue(CCParameter)` overload so array models store at the true index
value (rep value + offset), not the representative's value. This relies on the
array theory rebuilding from scratch each `buildWeakEq`/`computeWeakeqExt` pass,
so value keys are a stable snapshot. `WeakCongruencePath` navigates by value key;
its `computePath` calls only collect reason atoms (sound clause) — the net offset
matters only for the proof object, which is disabled while offsets are on.
`WeakSubPath.mIdx` stays a bare CCTerm for the (offset-disabled) proof annotation.

Results: `array/difftest004` now SAT with a **correct** model (previously a wrong
model — the index offset was dropped); `nia/divaxiom2` and `abv/ext02` no longer
crash (`ext02` correctly UNSAT). All `array/` benchmarks pass; no crashes in
`abv/`,`bv/`.

**Done (commit `858013d5`):** gaps 2 and 3 — LA→CC offset-equality propagation,
eager offset (dis)equality propagation at merge time, and the offset-aware
conflict explanation (`computeAntiCycle`/`CongruencePath.computeAntiCycle`,
`setLiteral` polarity, eager disequality explanation in `getPropagatedLiteral`,
`checkPending`/`separate` allowances). `bv/test01` fixed; `abv/ext01` no longer
crashes.

**Done (commit `0c94d305`) — the CC↔LA sharing redesign:** the `LASharedTerm` now
carries the term's **full value** (its constant), instead of being offset-free.
The offset-free design handed LA the wrong value (`(a+255) mod 256` shared as
`−255` not `0`), so `mbtc` (which groups shared terms by value) never matched it —
the fingerprint bucketing was papering over this and over-collided. Sound because
the offset-free CCTerm and full `LASharedTerm` share the same LinVars (constant
only affects the `LAEquality` bound), and the CC-level offset equality still comes
from `EqualityProxy`'s term constants. `share()` decoupled so each distinct
full-value `LASharedTerm` reaches LA while the offset-free CCTerm is shared with
CC once. The non-constant fingerprint bucketing is **removed**; `mbtc`/
`propagateSharedEqualities` are value-based again. **Fixes `abv/indexInRange01`
and `ufbv/ufbv01`.**

**SystemTest: 6 → 1.** The lone remaining failure `model/buggy001` is a
pre-existing array-model assertion (`assert mArrayModels != null` in
`ArrayTheory.fillInModel`), unrelated to offsets. All other unit tests green.
`array/difftest004`, `abv/ext01/02`, `bv/test01`, `nia/divaxiom2`,
`abv/indexInRange01`, `ufbv/ufbv01` all fixed this round.

**Next:** (1) the still-open *completeness* item from the design discussion —
share **every** numeric `CCAppTerm` argument with LA (a plain variable used only
as a function argument never enters LA today; create a LinVar for it), so an
argument that becomes CC-equal to a shared term can't be missed. No current
benchmark exercises it, but it's the textbook-complete shape. (2) **DONE — offset-less
checkpoint propagation.** `fingerprintSharedVar` now drops the constant (the `null`
key, holding the offset and any fixed-variable contributions) when
`createOffsetEqualities()`, so two shared terms collide when their *non-constant*
parts agree, i.e. they are provably equal up to a constant. `propagateSharedEqualities`
recovers the exact offset from the (model-independent) value difference and calls the
4-arg `propagateSharedEquality`, which now propagates implied **offset** equalities to
CC at checkpoint (the LA→CC dual of `CCTerm.mSharedTerm`), not just zero-offset ones.
The early-out guard is offset-aware: same affine class *and* matching offset → already
known (skip); otherwise the `propagated` hash dedups (the same-class/different-offset
self-pair `(rep, rep)` lets CC raise the offset conflict exactly once). The shared-var
loops iterate a snapshot, because propagating an offset equality synthesizes and shares
a `rhs + offset` term (appends to `mSharedVars`); it is offset-free-equivalent to an
existing term and the guard recognizes it as known on the next call. No-op when offsets
are disabled (full-value fingerprint, every offset 0). SystemTest unchanged at 1
failure (`model/buggy001`, pre-existing). (3) the offset-aware **proof
object** to enable offsets under proofs; offset-aware e-matching; deferred
`DataTypeTheory` numeric-field handling. (4) consider removing the
`CCEquality`↔`LAEquality` linkage (bigger; has proof-generation consequences).

**Remaining system-benchmark failures** (with proofs/interpolants disabled so
offsets are exercised): `bv/test01`, `abv/indexInRange01` (both unsat → **sat**,
*unsound*, but pre-existing before the array migration — they stem from gap 2,
LA knowing e.g. `k mod 256 = 1` but never telling CC). These are the motivation
for gap 2 and should be the next target.

**Temporary working-tree change (uncommitted):**
`SMTInterpolTest/src/system/SystemTest.java` has `:proof-check-mode`,
`:proof-level` and `:interpolant-check-mode` commented out so the system
benchmarks exercise offsets (offsets are forced off under proof generation).
Revert this before merging.

## Status after increment 3

Increments 1, 2a, 2b and 3 are implemented and committed; offsets are live for
quantifier-free, non-proof problems and the full unit suite passes. Two further
fixes landed:
- the shared-term equality must use a *flattened* polynomial term
  (`Clausifier.addConstantToTerm`), otherwise a nested `(+ t offset)` is
  re-parsed with the inner sum collapsed to one monomial (was unsound, e.g.
  `bv/test04`);
- offsets are disabled in the presence of quantifiers (`mQuantTheory != null`),
  because e-matching binds variables to offset-free CCTerms and would lose the
  offset (was unsound, e.g. `quanttest001`).

Running the system benchmarks with proofs/interpolants disabled (so offsets are
exercised) leaves these failures, all in offset-heavy machinery and **none of
them unsound** (crashes or incompleteness): `array/difftest004` (crash),
`nia/divaxiom2` (crash), `bv/test01`, `abv/indexInRange01`, `abv/ext02`
(unsat → unknown). They stem from the gaps below.

## Remaining gaps

1. **Every `CCAppTerm` consumer must treat argument `i` as `getArgument(i) +
   getArgOffset(i)`** (the most important gap). Consumers that currently drop the
   offset: `ArrayTheory` (select/store indices and array arguments),
   `DataTypeTheory`, `CClosure.getCCTermRep`/`getAllFuncApps`/`checkCongruence`,
   and the e-matching (`GetArgCode`/`EMReverseTrigger`, currently moot because
   offsets are off under quantifiers). Already fixed: `ModelBuilder.addApp`. This
   is behind the array crash and the BV/ABV incompleteness.
2. **LA → CC offset-equality propagation (DONE, commit `858013d5`).** In
   `LinArSolve.propagateSharedEqualities`, when `createOffsetEqualities()` the
   shared-term fingerprint is keyed on its *non-constant* part (the `null` entry
   holds the constant from `addToFingerprint`/`fpr.add(shared.getOffset())`), and a
   collision propagates `value(a) == value(b) + k` (`k` = constant difference) via a
   generalized `propagateSharedEquality(lhs, rhs, offset, …)` that builds `rhs + k`
   with `addConstantToTerm` and reuses `EqualityProxy.createCCEquality` (which
   derives the CCEquality offset from the term constants and links the
   `LAEquality`). A true-proxy guard skips the tautology between two distinct
   constant terms. Off when offsets are off (constant stays in the key). Fixed
   `bv/test01`.
3. **Eager offset (dis)equality propagation + offset-aware conflict explanation
   (DONE, commit `858013d5`).** `CCTerm.mergeInternal` now propagates the
   *disequality* for eqlits whose offset differs from the merge offset (mirroring
   the existing matching-offset *true* propagation). The conflict/explanation side
   is offset-aware: `CClosure.computeAntiCycle` + `CongruencePath.computeAntiCycle`
   explain an offset disequality whose two sides are in the *same* class at a
   different offset via the path between them (`{¬eq, ¬path}`), since the offset-0
   temporary-merge trick cannot work once the classes are merged; `setLiteral`'s
   same-class conflict uses the same form; and — the key fix — `getPropagatedLiteral`
   computes a propagated disequality's explanation **eagerly** (offsets only),
   while the congruence graph still matches the trail, storing it on the atom so
   `DPLLEngine` does not recompute it later from a state where a subsequent offset
   merge (undone only at decision-level backtrack) has joined the two sides.
   `checkPending`/`separate` allow the new same-class / decided-false cases. Fixed
   `abv/ext01` (was crashing) and `abv/ext02`. **SystemTest 5 → 4 failures, no new
   failures, all other unit tests green.**

   *Insight (Jochen):* the offset-differs disequality propagation is not the
   problem — the old `mDiseqReason` anti-cycle is, because you cannot temporarily
   insert the equal-edge when the classes are already equal at a different offset;
   computing the explanation eagerly at propagation time sidesteps it. `CongruencePath`
   itself needs **no** offset tracking for the clause: it only collects the path
   edges; δ vs k lives in `CClosure`. (Net offsets are only needed for the eventual
   *proof object*, still deferred and moot while offsets are off under proofs.)

## CCParameter: a value `CCTerm + Rational`

To stop every consumer from re-deriving `getArgument(i) + getArgOffset(i)` /
`mOffsetToRep` arithmetic, introduce a small abstraction for "a value up to a
constant" (array index, congruence argument, shared-term comparison):

```java
public interface CCParameter {            // value == getCCTerm() + getOffset()
    CCTerm   getCCTerm();
    Rational getOffset();                 // structural offset; ZERO for a bare CCTerm
    default CCTerm   getRepresentative() { return getCCTerm().getRepresentative(); }
    default Rational getOffsetToRep()    { return getCCTerm().getOffsetToRep().add(getOffset()); }
}
```

- It must be an **interface** (not a base class): `CCTerm` already
  `extends SimpleListable`, so it `implements CCParameter` with `getCCTerm() =
  this`, `getOffset() = ZERO` — no extra object for the common offset-0 case.
- `OffsettedCCTerm implements CCParameter` is an immutable `(mTerm, mOffset)` with
  `mOffset != ZERO`. Factory `CCParameter.of(t, off)` returns the bare `t` when
  `off` is zero, so an offset-0 value is *always* a bare `CCTerm` (canonical
  representation; no ambiguous `OffsettedCCTerm(t, 0)`).
- `SignatureTrigger` can use `CCParameter[]` instead of the parallel
  `CCTerm[] mTerms` + `Rational[] mArgOffsets`, with the rehash-on-rep-change it
  already performs.

**Array index keys.** A `CCParameter`'s value identity
`(getRepresentative(), getOffsetToRep())` *changes on merge* (rep and offset both
shift), so it cannot be a naive persistent `HashMap` key. However, `ArrayTheory`
does **not** keep persistent index-keyed maps across merges: it **rebuilds its
weak-equivalence structures from scratch on every index merge** (the class shape,
primary/secondary store edges can change completely — e.g. when a secondary-edge
index becomes equal to the primary-edge index a different secondary edge must be
chosen). So **no rehashing is needed**: within one rebuild the representatives and
offsets are a fixed snapshot, making a value-identity key stable for that rebuild.

The adaptation is therefore: where the array theory keys an index on
`index.getRepresentative()` today, key it on the value identity
`(getRepresentative(), getOffsetToRep())` instead — a small value-identity key
wrapper built fresh during the rebuild. The index value itself is read as
`CCParameter.of(app.getArgument(idxPos), app.getArgOffset(idxPos))`, which
supplies those accessors uniformly (a bare `CCTerm` when the index has no
offset). Note this composite key cannot be the bare `CCParameter`/`CCTerm`
directly, because `CCTerm`'s `hashCode`/`equals` are object identity, not the
value identity `(rep, offsetToRep)` the array theory needs.

## Gap-fix order

1. `CCParameter` + `OffsettedCCTerm`; wire the `CClosure` consumers
   (`getCCTermRep`, `getAllFuncApps`, `checkCongruence`). **(done)** —
   `DataTypeTheory` still deferred (only matters for numeric datatype fields).
2. `ArrayTheory` offset-aware index handling (gap 1, the substantial one).
   **(done — incl. `WeakCongruencePath` and `ModelBuilder.getModelValue`.)**
3. LA → CC offset-equality propagation (gap 2) + eager offset (dis)equality
   propagation (gap 3) + offset-aware conflict explanation. **(done, commit
   `858013d5`; SystemTest 5 → 4 failures.)**
4. Eager negated-equality propagation (gap 3).
5. Proof production (increment 4) and offset-aware e-matching (re-enable offsets
   under quantifiers) — both deferred to the quantifier-theory rework.

---

# Redesign: offset-free sharing + clash-slot MBTC (planned)

This redesign supersedes the full-value `LASharedTerm` approach (commit `0c94d305`,
documented under *Resume point*). It returns to **offset-free** CC↔LA sharing —
which is the sound Nelson-Oppen shape — and fixes the reason full-value was
adopted in the first place by changing *what* model-based theory combination
(MBTC) iterates over.

## Why full-value sharing is the wrong lever

The shared object and its CCTerm must denote the **same value** for the
Nelson-Oppen shared-term equality to be sound. Full-value `LASharedTerm` violates
that: the shared CCTerm is offset-free (value `2x+4y`) while the `LASharedTerm`
carries the constant (value `2x+4y+1`). Every LA→CC step then has to un-bend the
mismatch with `getTermConstant`, and that bridging is where bugs live (e.g. the
"already known" guard in `LinArSolve.propagateSharedEquality` compares an
offset-free CC offset against a full-value LA offset — mismatched units).

Full-value was adopted only because MBTC groups *whole shared terms by their LA
value* (`getSharedCongruences`), and offset-free whole terms carry the wrong
canonical value (`(a+255) mod 256` shows up as `−255`, not `0`), so the value
buckets never matched. The real defect is that **MBTC is asking the wrong
question**: the equalities CC needs are not between whole numeric terms, they are
between the argument `CCParameter`s that sit at congruence (and reverse-trigger)
positions. Those carry their constant in the structural offset, so comparing
*them* by value is correct even when the shared terms are offset-free.

## The three sharing jobs, and where offsets land

- **CC → LA (merge propagation).** Unchanged. `CCTerm.mSharedTerm` +
  `CCTerm.propagateSharedEquality` already work entirely in offset-free space
  (the `LAEquality` is built from offset-free flat terms and the `mOffsetToRep`
  difference). Sound and untouched.
- **LA → CC, entailed (checkpoint).** `propagateSharedEqualities` over
  offset-free `LASharedTerm`s. It computes the exact value difference from the
  model after a fingerprint collision, so it never relied on a (wrong) canonical
  value; with offset-free shares it is correct *by construction*, and the
  unit-mismatch guard disappears (no constant to bridge).
- **LA → CC, model-based (MBTC).** Redesigned to iterate over **numeric clash
  slots** (see below) instead of whole `LASharedTerm`s. Equalities only.

## `LASharedTerm` becomes offset-free

When offset equalities are on, the `LASharedTerm` for a numeric term shares the
**offset-free** value (constant dropped), 1:1 with the offset-free CCTerm and
value-consistent with it. Terms that differ only by a constant (`2x+4y+1`,
`2x+4y+5`) collapse to the same offset-free shared entity; their distinctness
lives only in the SMT term layer and surfaces as the structural offset of a
`CCParameter` at the use site (a function argument). So `LASharedTerm`'s role
narrows to the offset-free value handle that the checkpoint propagation reads.

## The clash slots (enumerated on demand, not a persistent index)

A *clash slot* is a key `(FunctionSymbol, argPosition)`; its members are the
numeric `CCParameter`s occupying that argument position. Two members in the same
slot whose values coincide but whose CC classes differ are exactly the equalities
MBTC should propose — merging them is what fires the trigger CC cares about
(congruence, or a reverse trigger).

**No persistent `Map<ClashKey, List<CCParameter>>` is maintained.** MBTC runs
only in `finalCheck` (`LinArSolve.finalCheck`, after bounds / integrality /
`mutate`), which is rare, so the slots are **enumerated on demand** at that point.
This dissolves the earlier "how/when slots are added and undone on
merge/backtrack" question entirely — there is no lifecycle to mirror. The two
sources:

- **Congruence source (covers EUF / QF_UFLIA).** Each numeric argument position
  `(sym, pos)` is a slot; its members are `app.getArgParam(pos)` over
  `getAllFuncApps(sym)`, restricted to numeric argument sorts. Two arguments at
  the same `(sym, pos)` with equal value may make their applications congruent.
  This source is **necessary**: plain congruence runs through `CongruenceTrigger`
  (a `SignatureTrigger`) and the per-app `FindTriggerTrigger`, never a
  `ReverseTrigger`, so the reverse-trigger source below yields *nothing* for a
  pure `f(a)`/`f(b)` numeric clash. The old whole-term `mbtc` handled QF_UFLIA, so
  dropping these positions would regress completeness. Enumerated on demand from
  `getAllFuncApps`.
- **Reverse-trigger source (covers e-matching, and datatypes via a feed).**
  Reverse triggers already carry `getFunctionSymbol()` and `getArgPosition()`, and
  the `MasterReverseTrigger` / `ReverseTriggerTrigger` machinery already groups the
  n-th argument of every application of that symbol at that key — so this source
  is **self-maintaining and free**. The `-1` convention is the discriminator:
  - A *find* trigger (watches the whole symbol for new apps) returns
    `getArgPosition() == -1` — `MasterReverseTrigger.getArgPosition()` returns
    `-1` by contract; e-matching installs these via `insertFindTrigger(func, …)`
    with `argPos = -1`. **LA ignores these** — they are not clash positions.
  - A *real* reverse trigger returns `getArgPosition() != -1` (e.g.
    `EMReverseTrigger → mArgPos`, installed via `insertReverseTrigger(func, arg,
    argPos, …)`). This **induces a clash slot** keyed `(getFunctionSymbol(),
    getArgPosition())`. Restrict to **numeric** argument sorts on top of this.

So clash slots =
`{(sym,pos) : reverse trigger with pos != -1 and numeric arg}` ∪
`{numeric arg positions via getAllFuncApps(sym)}`.

### Datatypes: a numeric-position reverse-trigger feed

The datatype "result-vs-argument" clash — `sel_i(d)` against the i-th argument of
`cons(x)`, the speculative complement of the existing DT_PROJECT loop in
`DataTypeTheory` that only fires once `d` is already known equal to a `cons` — does
**not** fall out of the existing reverse triggers. `DataTypeTheory` installs its
reverse triggers at `(selectorFunc, 0)` / `(isFunc, 0)`, i.e. on the
**datatype-typed** argument, which the numeric-sort filter discards. The numeric
clash is between the *selector result* `sel_i(d)` and the *constructor argument*
`cons(x).getArgParam(i)`.

`DataTypeTheory` already computes the selector↔(constructor, position `i`)
correspondence (it walks `constructor.getSelectors()` and reads
`consTerm.getArgParam(i)` in the DT_PROJECT path). The hookup is therefore a
**light, dedicated feed**: register a reverse trigger at the constructor's numeric
argument position `(cons, i)` (or equivalently inject the offset-free selector
result into that slot). Expressed in the reverse-trigger vocabulary it becomes
uniform — the `(cons, i)` slot then holds both the constructor arguments and the
selector results, and the standard clash machinery proposes `sel_i(d) = x_i`. This
is the still-deferred "numeric datatype field" handling; until it lands, datatype
numeric fields are simply not clashed (no soundness impact). **Also decide**
whether `ArrayTheory` needs to contribute slots for numeric `select` results /
`store` values, or already covers those value equalities through
weak-equivalence.

## MBTC over clash slots

For each slot:

1. **Filter to shared reps.** Keep only members whose
   `getRepresentative().mSharedTerm != null` — their class has an LA value. A
   member whose class is LA-free cannot be forced to clash (model construction
   gives it a non-clashing value), so it is ignored. This removes the
   "force a LinVar on every numeric argument" prerequisite entirely.
2. **Value each member.** The class's LA value is carried by `rep.mSharedTerm`,
   which need not *be* the rep and has its own `getOffsetToRep()`. So the member
   value is **not** simply `value(rep) + param.getOffsetToRep()`; it is

   ```
   value(param) = sharedTermValue(rep.mSharedTerm)   // LA value of the offset-free shared term
                − rep.mSharedTerm.getOffsetToRep()     // shift back to the rep
                + param.getOffsetToRep()               // shift out to the member
   ```

   (sign convention from `CCParameter.sameValueAs`: `value(p) = value(rep) +
   p.getOffsetToRep()`). `rep.mSharedTerm` is a `CCTerm` and already carries
   `getOffsetToRep()`, so **no new field is needed** — just fold the lookup in.
3. **Propose offset equalities** for members that are equal-valued but in
   distinct CC classes: `u = v + (c_v − c_u)`. For a reverse-trigger slot this
   merge then activates the existing trigger (e.g. the datatype propagation).

**Equalities only.** LA never sends CC a disequality literal; the other theories
read "not provably equal" as disequal. The only residual obligation is implicit:
at model construction, shared `CCParameter`s in *distinct* CC classes must get
*distinct* values. The existing `sharedPoints` / `choose` / `hasSharing`
collision-avoidance handles this, but it must become **offset-aware**: today it
de-collides *raw* `LASharedTerm` values, whereas a clash-slot member's value is
`repValue + offset`, so the quantity kept distinct must be the offset-shifted
member value, not the raw shared value.

## Model construction consequence

LA-free numeric CC classes (those whose rep has no shared term) get no value from
LA. This is **already supported**: `ModelBuilder.fillInTermValues` routes a numeric
representative with `getSharedTerm() == null` into a `delayed` set and assigns it a
fresh value via `mModel.extendFresh(...)` after all LA-derived values are placed.
So "the bit of extra model-construction work" is mostly pre-existing. **Confirm**
only that `extendFresh` avoids colliding with the LA-assigned values, so distinct
classes (one LA-valued, one LA-free) stay distinct.

## Net effect

The value-mismatch bug class is removed by construction (shares are
value-consistent; MBTC computes correct per-argument values), offsets become
intrinsic to the argument positions where they matter, and the clash slots unify
the congruence and reverse-trigger sources behind one `(sym, pos)` key — with no
persistent structure to maintain.

## Open items to settle in code

1. **Datatype numeric-field feed.** Implement the constructor-numeric-position
   reverse-trigger feed described above; confirm it produces exactly the
   `sel_i(d)` vs `cons` i-th-argument clash. Decide array `select`/`store` value
   contributions (or confirm weak-equivalence already covers them).
2. **Offset-aware collision avoidance.** Make `sharedPoints` / `choose` /
   `hasSharing` de-collide offset-shifted clash-slot member values; confirm
   `extendFresh` for LA-free classes avoids the LA-assigned values.
3. **Per-position completeness** is complete for SAT/UNSAT congruence; it drops
   equalities between shared terms sharing no signature position, which are
   irrelevant to solving.
   - *Interpolation* is only used in the UNSAT case and is **not** affected by
     MBTC (MBTC only feeds the SAT/model search). The single obligation is that an
     MBTC equality which is *propagated* (not merely suggested) and lands in an
     UNSAT core be proof-producible — that is exactly the deferred offset-aware
     proof-object work, not a separate interpolation concern. Defer.
4. **Flag interaction.** When offsets are off, `LASharedTerm` stays full-value and
   MBTC stays whole-term, exactly as today.

## Status: implementable slice DONE (uncommitted)

Steps 1–4 below are implemented (`Clausifier`, `CClosure`, `LinArSolve`, plus an
`EqualityProxy` fix) and validated under the temp proof-gate (SystemTest 22→21).
One additional fix was required beyond the four steps: a numeric disequality whose
`CCEquality` had no linked `LAEquality` never reached linear arithmetic, so model
construction could build an invalid model (e.g. `lia/divdiv5`). Whole-term mbtc
created that `LAEquality` as a side effect; clash-slot MBTC does not (the terms are
not function arguments). Fix: `EqualityProxy.createAtom` eagerly creates and links
the `LAEquality` for numeric equalities when `createOffsetEqualities()`.

Two SystemTest regressions remained, both in the offset proof/interpolation track:
- `abv/ext01`: a clash-MBTC offset equality reached, via congruence, the stub
  `CCTerm.merge` "offset equality conflict explanation not yet implemented" (the
  congruence-merge analogue of the `computeAntiCycle` case `setLiteral` already
  handles). **FIXED** — see *Congruence-merge offset conflict* below; `ext01`/`ext02`
  now solve `unsat` and proof-check.
- `interpolation/uflratest004`: the eager `LAEquality` changes the proof so the
  offset-unaware interpolant checker rejects the interpolant. The eager `LAEquality`
  is kept (needed for SAT model soundness); offset interpolation is deferred.

## Congruence-merge offset conflict (the `CCTerm.merge` stub) — DONE (uncommitted)

The stub `CCTerm.merge` threw `UnsupportedOperationException("offset equality
conflict explanation not yet implemented")` in the `src == dest` branch (the two
merged terms are already in one class) when the merge offset disagreed with the
offset they already have. It is reachable **only** from `buildCongruence`
(`lhs.merge(this, rhs, null)`, `reason == null`): two congruent `CCAppTerm`s
`f(x)`, `f(y)` — congruence implies value difference `0` — are already in the same
class at a non-zero offset `existingDiff` (e.g. the class already records
`f(x) = f(y) + k`). `setLiteral` is the only other `merge` caller and it guards
`src != dest`, so the `reason != null` case never reaches this branch (asserted).

Why `computeAntiCycle` could not be reused directly: it is keyed on a real
`CCEquality eq` — it negates `eq` in the clause and reads `eq.getOffset()` as the
deviating offset, and in the proof its prepended leading edge is discharged by
resolving against the `eq` literal. The congruence merge has `reason == null`:
there is no literal to negate, the deviating "edge" is a congruence justified by
the *argument* equalities (so the clause carries `{¬argEq…, ¬path}` with no positive
literal, like `computeCycle(const, const)`), and the leading proof edge must be
discharged by a congruence sub-proof, not a literal.

Implementation: `CClosure.computeCongruenceAntiCycle(CCAppTerm, CCAppTerm)` →
`CongruencePath.computeCongruenceAntiCycle`.
- **Clause:** collect `mAllLiterals` from `computePath(second@0, first@0)` (the
  existing class path, establishing `existingDiff`) plus `computePath` over each
  argument pair `getArgParam(i)` (justifying the congruence); negate all. The
  contradiction is intrinsic to arithmetic (`0 != existingDiff`), so no positive
  literal is needed.
- **Proof object** (mirrors `computeAntiCycle`'s leading-node trick — a `SubPath`
  cannot carry one CCTerm at two offsets): explicit
  `mainPath = [first@0, second@0, …, first@existingDiff]` via the
  `CCAnnotation(diseq, mainPath, otherPaths, CONG)` constructor (the one
  `computeAntiCycleDiffClass` uses). The leading step `first@0 → second@0` has no
  clause literal and is not a registered subpath, so
  `CCProofGenerator.collectEquality → findCongruencePaths` auto-resolves it from the
  argument subpaths in `otherPaths` (= `mAllPaths` minus the inlined existing path,
  retrieved via `mVisited.get(SymmetricPair(second, first))`). The two endpoints are
  the same term `first` at offsets `0` and `existingDiff` — a trivially-false offset
  disequality discharged by an EQ lemma.

Validated (clean build, assertions on): `abv/ext01`, `abv/ext02` now `unsat` (were
`unsupported`); `BitvectorTest` 89/89 with FULL proofs + `proof-check-mode` (the
proof object verifies); `test/proof` 97/98 (only the pre-existing
`trivialdiseqarray` array+offset blocker, identical at baseline);
`CongruentAddTest`/`PairHashTest`/`ProofSimplifierTest`/`ProofUtilsTest`/`RPITest`
green. The change is gated only by the structural shape of the merge, not by
`createOffsetEqualities()` directly, but it is dead code when offsets are off (every
offset is then `0`, so `existingDiff` is always `0`). Files: `CCTerm.java`,
`CClosure.java`, `CongruencePath.java`.

Still-deferred gate-flip blockers (confirmed pre-existing, identical at baseline):
`ProofSimplifier.checkProof` on offset lowlevel proofs (e.g. `bv/bvand0*`) and
`QuantClause.collectVarInfos` on quantified datatype matching (e.g.
`datatype/quantified/match_test`).

## Shared-term clash during a merge (the `computeCycle` constant case) — DONE (uncommitted)

`uflira/uflira_001.smt2` (`to_real a = f a`, `f b = 1/2`, `a = b`) was `unsat`
correctly but the **proof object** failed: `Cannot explain term pair
((f b)+-1/2,(f a))`. Same root cause as `computeAntiCycleDiffClass`: an equal edge
was added to the CC graph but the nodes were not yet really merged.

Mechanism: asserting `a = b` makes `f a ≡ f b` by congruence. `CCTerm.mergeInternal`
tries to merge `f a`'s class (shared term `to_real a`) with `f b`'s class (shared
term `0.0`, with `f b` at offset `-1/2`). The merged shared-term equality
`to_real a == 0.0 + (-1/2)` is integer-impossible (`a` is `Int`), so
`createEquality` returns the false proxy → `sharedTermConflict`, and the conflict was
built by `computeCycle(0.0, (to_real a)+(-1/2))`. But the conflict is detected
**before** the union-find update: the equal edge `f a — f b` is set while
`mOffsetToRep` is still relative to each node's own representative. `computePath`
walks across the bridge fine for the *clause*, but `SubPath.getParams()` reads the
congruence bridge step as `(f b)+(-1/2) → (f a)+0` (two reference frames) instead of
offset-free → the proof generator cannot explain it.

Fix: new `CClosure.computeSharedConflictCycle` →
`CongruencePath.computeSharedConflictCycle(lshared, rshared, lhs, rhsTerm, reason,
bridgeOff, …)`, a hybrid of `computeAntiCycleDiffClass` (two single-class halves
stitched by hand) and `computeCongruenceAntiCycle` (the bridge may be a congruence,
`reason == null`):
- **Clause:** `computePath(lshared@0, lhs@0)` (source half) + `computePath(rhsTerm@0,
  rshared@0)` (dest half), each single-class and offset-correct. The bridge edge
  `lhs — rhsTerm` is justified by the merge `reason` (added as a literal) when
  `reason != null`, or — for a congruence merge — by `computePath` over each argument
  pair `getArgParam(i)` (which also builds the subpaths the proof needs). Negate all;
  no positive literal (the contradiction is the trivially distinct shared values).
- **Proof object:** build an explicit `mainPath = paramsSrc ++ paramsDest` via the
  `CCAnnotation(diseq, mainPath, otherPaths, CONG)` constructor. The destination half
  is computed **already shifted** into the source frame: instead of anchoring at
  `rhsTerm@0` and shifting every node afterwards, the dest `computePath` is anchored at
  `rhsTerm@shift` with `shift = (lshared.mOffsetToRep − lhs.mOffsetToRep) + bridgeOff`
  (`bridgeOff = reasonDiff(reason, lhs, rhsTerm)`, `0` for a congruence). Since
  `SubPath.getParams()` offsets every node by the anchor's `mStartOffset`, the dest
  params come out in the source frame and `mainPath` is a plain two-`arraycopy`
  concatenation — no post-hoc per-node shift. For a congruence bridge the step
  `lhs → rhsTerm` (offset 0) is auto-resolved from the argument subpaths in
  `otherPaths`, exactly like `computeCongruenceAntiCycle`'s leading edge; for a
  real-equality bridge the step matches the `reason` literal. The diseq is taken from
  the stitched path endpoints (`mainPath[0]`, `mainPath[last]`), so its offset is the
  true value difference `value(lshared) − value(rshared)` (= `sharedOffset`), fixing a
  latent bug where the old call passed `delta` instead — these coincide only when both
  shared terms are their class reps. Discharged by an EQ/LA lemma.

`reason == null` is the key complication the user flagged: there is no separating
disequality literal to resolve the bridge on. It is handled exactly as in
`computeCongruenceAntiCycle` (argument subpaths discharge the congruence step), so the
hybrid covers both bridge kinds uniformly.

**CongruencePath refactor (same change).** Three cleanups landed alongside the fix:
1. `computeCCPath` renamed to **`computeCongruence`** (it pairs the arguments of two
   congruent app terms); both cross-class builders (`computeCongruenceAntiCycle`,
   `computeSharedConflictCycle`) now call it instead of hand-rolling the argument loop.
2. **`computePath` no longer drains** the work list — it only enqueues. Each top-level
   `compute*Cycle`/`computeDTLemma`/`computeDecideLevel` calls the extracted
   `drainTodo()` **once** after all `computePath`/`computeCongruence` calls are queued,
   so a single shared drain builds them (and dedups subpaths shared between several
   queued ends). `WeakCongruencePath` consumes single paths synchronously
   (`computePath(...); mAllPaths.removeFirst()`), so it drains per call — `drainTodo()`
   is `protected` and called explicitly at each of its six `computePath` sites
   (reproducing the old per-call drain; without this the array proofs in
   `test/proof/auxaxioms/*` throw `NoSuchElementException`).
3. **`computeAntiCycleDiffClass` gets the same pre-shift simplification** as
   `computeSharedConflictCycle`: its right half is anchored at `right@shift`
   (`shift = dLeft.mOffsetToRep − left.mOffsetToRep + eq.getOffset()`), so `getParams()`
   returns it already in the left frame and `mainPath` is a plain concatenation. The
   `assert mainPath[last].getOffset() == dOff` still holds.

Validated (clean build, `-ea`): `uflira_001` proof now `unsat` with
`proof-check-mode` (was `Cannot explain term pair`); `test/proof` 97/98 (only the
pre-existing `trivialdiseqarray`, confirmed identical at baseline; `match_rewrite`
re-checks its full cross-class anti-cycle proof);
`test/uflira` 5/5, `test/lia` 32/32, `test/abv` 4/4 clean; `BitvectorTest` 89/89
(FULL proof + proof-check), `ProofSimplifierTest` 14/14, `ProofUtilsTest` 4/4,
`CongruentAddTest` 5/5, `PairHashTest` 1/1. Pre-existing deferred crashes unchanged
(`datatype/quantified/*match*` = `QuantClause.collectVarInfos`). Files:
`CCTerm.java`, `CClosure.java`, `CongruencePath.java`, `WeakCongruencePath.java`.

## `SubPath.getParams(anchor)` + the cross-class guard, and the merge-conflict-diseq stitch — DONE (uncommitted)

A `SubPath` is a list of offset-free CCTerms; `getParams` renders them as offsetted
`CCParameter`s. It used to store the anchor (`mStart`/`mStartOffset`) on the SubPath.
Now `getParams(CCParameter anchor)` takes the anchor at render time (the relative
offsets are intrinsic — `getOffsetToRep` differences — so the anchor only fixes the
absolute base). `mStart`/`mStartOffset` are gone; the no-arg `getParams()` self-anchors
at the path's first node. This also subsumes the per-element "pre-shift" in
`computeAntiCycleDiffClass`/`computeMergeConflictCycle`: the destination half is rendered
with `getParams(rhsTerm@shift)`, so the main path is a plain concatenation.

**Direction fix (Jochen caught it).** `mVisited` keys paths by an undirected
`SymmetricPair`, so a retrieved `SubPath`'s stored term list may run either way; the
stitch builders assumed `[start … end]`. `getParams(anchor)` now treats the anchor as the
intended <em>start</em> (it must be one of the two endpoints) and renders the term list in
reverse when the anchor is the stored last node, so callers always get `[anchor … other]`.
The three stitch sites anchor explicitly at their start endpoint
(`segSrc.getParams(srcEnd)`, `segB.getParams(right@shift)`,
`existing.getParams(second@0)`) rather than self-anchoring, and assert the main path runs
`srcEnd … destEnd` (comparing `getCCTerm()`, not the offsetted parameter). Validated by
temporarily reversing the build order of both halves: `abv/ext01` still proof-checks
`unsat`.

**The cross-class assertion (Jochen's idea).** `getParams` asserts the anchor shares the
representative of every *numeric* node. `getOffsetToRep` is class-relative, so a path that
spans two classes mixes reference frames and yields garbage offsets — the bug behind every
cross-class offset conflict. Non-numeric terms can never carry an offset, so the legitimate
cross-class paths (weak-array paths over distinct strong classes) are exempt.

**The lingering bug the assertion found.** With the strict guard, `computeCycle(diseq)`
called from `CCTerm.mergeInternal` (the `diseq != null` branch: a disequality forbids a
merge at exactly the merge offset) fired the assertion — it walks a single path across the
freshly added, not-yet-united merge bridge, exactly like the shared-term clash. It is the
eager-conflict twin of the lazy `computeAntiCycle → computeAntiCycleDiffClass` path, and was
never converted; it was silently wrong in the proof object whenever the bridge offset is
non-zero (the clause is always sound, so only proof-checking catches it). Fix: generalize
`computeSharedConflictCycle` into `computeMergeConflictCycle`, which takes an optional
concrete `diseqLit` (the shared-term clash passes `null`; the merge-conflict passes the
disequality, which becomes the cycle's positive literal). `CClosure.computeMergeDiseqCycle`
wraps it; `mergeInternal` orients the diseq's two sides into the source/destination class
(via pre-merge `mRepStar`) and calls it. Now both clash kinds build the two halves
separately — no cross-class numeric `getParams` remains.

**Real trigger:** `abv/ext01.smt2` hits `computeMergeDiseqCycle` with `bridgeOff = -1` on
`(ubv_to_int (select d (@diff d e))) == (ubv_to_int (@diff d d))` — the abv/ext case where
this was first suspected. It now proof-checks `unsat`.

Also removed dead code orphaned by the shared-term-clash change: `SubPath.getTerms()`, the
`CCTerm[]` `prepend` overload and the unused `terms`/`mainTerms` locals in `CCAnnotation`,
and the two-arg `computeCycle(CCParameter,CCParameter)` (CongruencePath impl + CClosure
wrapper).

Validated (clean build, `-ea`; note `ant clean` is required after a stash/`cp` restore — a
stale `.class` newer than the restored `.java` is not rebuilt): `test/proof` 97/98,
`test/abv` 4/4, `test/bv` 35/35, `test/regression` 53/55, `test/uflira` 5/5, `test/lia`
32/32 — only the two documented pre-existing failures (`trivialdiseqarray` array+offset;
`Script_simple` `CCInterpolator occur==null` offset interpolation). `BitvectorTest` 89/89,
`ProofSimplifierTest` 14/14, `ProofUtilsTest` 4/4, `CongruentAddTest` 5/5, `PairHashTest`
1/1. Files: `CongruencePath.java`, `CCAnnotation.java`, `CClosure.java`, `CCTerm.java`.

## All offset-cycle explainers consolidated into `computeMergeConflictCycle` — DONE (uncommitted)

Jochen's observation: the three anti-cycle builders are all special cases of
`computeMergeConflictCycle`. The same-class ones are the degenerate case where the two
endpoints coincide (`srcEnd == destEnd == lhs`): the source half is empty and the
destination half is the existing class path from `rhsTerm` back to `lhs`, so the trivial
diseq `(lhs@0, lhs@(bridgeOff − pathOffset))` falls out of the same two-half stitch. The
three knobs span every case:

- `srcEnd == destEnd` ⇒ same-class (anti-cycle), else cross-class (merge / diff-class).
- `reason == null` ⇒ congruence bridge (justified by argument equalities), else an equality
  literal bridge.
- `diseqLit == null` ⇒ trivial/shared diseq (EQ/LA discharged), else a concrete disequality
  literal carried positively in the clause.

Mapping (all now `CClosure` → `CongruencePath.computeMergeConflictCycle`):
- `computeAntiCycle` same-class: `(eq.lhs, eq.lhs, eq.lhs, eq.rhs, eq, eq.getOffset(), null)`.
- `computeAntiCycle` diff-class: `(dLeft, dRight, eq.lhs, eq.rhs, eq, eq.getOffset(), diseq)`
  with `dLeft`/`dRight` oriented via `eq.mDiseqOrientation` at the call site.
- `computeCongruenceAntiCycle`: `(first, first, first, second, null, ZERO, null)`.
- `computeMergeDiseqCycle` / `computeSharedConflictCycle` unchanged (eager merge conflict).

Deleted `CongruencePath.computeAntiCycle`, `computeAntiCycleDiffClass`,
`computeCongruenceAntiCycle` (5 explainers → 1 + `computeCycle`, the bridgeless
positive-eq cycle which stays separate). `CClosure.setLiteral`'s same-class assert-true
case routes through a new `computeSameClassAntiCycle` helper (must force the same-class
shape — `eq` can carry a stale `mDiseqReason`). Cosmetic: the unified same-class anti-cycle
anchors its trivial diseq on `lhs` (`(lhs@0, lhs@dev)`) instead of the old `rhs` anchoring —
both are valid EQ-discharged trivial diseqs, proof-check unaffected. `CongruencePath`
−170 lines net.

Validated (clean build, `-ea`): `test/proof` 97/98, `test/abv` 4/4, `test/bv` 35/35,
`test/regression` 54/55, `test/uflira` 5/5, `test/lia` 32/32, `test/datatype` non-quantified
clean — only the documented pre-existing failures (`trivialdiseqarray`, `Script_simple`,
`datatype/quantified/*match*` = `QuantClause.collectVarInfos`). `BitvectorTest` 89/89,
`ProofSimplifierTest` 14/14, `ProofUtilsTest` 4/4, `CongruentAddTest` 5/5, `PairHashTest`
1/1. Files: `CongruencePath.java`, `CClosure.java`, `CCAnnotation.java`.

## Implementable slice (ready to start)

1. `LASharedTerm` becomes offset-free under `createOffsetEqualities()` (revert the
   full-value part of `0c94d305`; the checkpoint path is already offset-aware).
2. On-demand clash-slot enumeration in `finalCheck`: congruence positions via
   `getAllFuncApps` (numeric arg sorts) ∪ reverse-trigger positions
   (`getArgPosition() != -1`, numeric arg sorts).
3. MBTC over slots with the corrected value formula (step 2 above).
4. Offset-aware `hasSharing` / `choose`.

Datatype numeric-field feed, array contributions, proof object (and thus offsets
under proofs/interpolation) remain deferred.
