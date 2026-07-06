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
   queued ends). `WeakCongruencePath` drains once per weak/main path; the strong paths
   it inlines into a weak path are built via `computePathNonRecursive` (see the
   *drainTodo / mAllPaths cleanup* section below — the original `computePath(...);
   mAllPaths.removeFirst()` per-call-drain idiom is superseded).
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

## Merge conflicts reported before mutating the graph — DONE (uncommitted)

Since the conflict explainers build each half within its own class and never walk the
merge bridge, `CCTerm.mergeInternal` no longer needs the equal edge for a conflict. It now
detects the conflict (disequality forbidding the merge, or shared-term clash) and returns it
<em>before</em> `invertEqualEdges`/`mEqualEdge`/`mOldRep`/`mReasonLiteral` are set — dropping
the old add-the-edge-then-undo-it dance, so the conflict path mutates nothing. The diseq
orientation (`diseq.getLhs().mRepStar == src`) now reads a pristine union-find. **Bug fixed
while reviewing:** the first cut treated any non-null `diseqInfo` as a disequality conflict,
but a `CCTermPairHash.Info` also holds equality literals / compare triggers, so
`diseqInfo.mDiseq` can be null — the guard must be `diseqInfo != null && diseqInfo.mDiseq !=
null` (otherwise `diseq.getLhs()` NPEs on essentially every benchmark). Validated: test/proof
97/98, abv 4/4, bv 35/35, uflira/lia/datatype-nonquant clean (only the pre-existing failures);
unit suites green. File: `CCTerm.java`.

## `drainTodo` / `mAllPaths` cleanup — DONE (uncommitted)

`mAllPaths` was overloaded: it is the final, topologically-ordered annotation output
(the producer must emit paths so that *later paths explain congruences on earlier* — see
`CCAnnotation.mParamPaths` and `CCProofGenerator.collectStrongEqualities`, which walks the
array backwards), **and** it was abused as a return channel — `WeakCongruencePath` read
`mAllPaths.removeFirst()` to retrieve the strong path it had just asked `computePath` to build
so it could inline it (`addSubPath`) into a weak path. That coupling caused two problems:

- **Per-call dedup set.** `drainTodo`'s `added` set was local, while `mVisited` is a field. A
  subpath built in one drain and re-enqueued in a later drain (`computeWeakeqExt` loops over
  store indices; `computeCongruence` re-enqueues argument pairs unconditionally) was found in
  `mVisited` but missing from the fresh `added` set → **re-appended to `mAllPaths` (duplicate)**.
- **`removeFirst` ordering reliance.** The graft assumed `mAllPaths`'s front was exactly the
  path for the last `computePath` — fragile, since the shared drain also drains other pending
  pairs (the index/select equalities), and it only stayed correct *because* the broken per-call
  dedup kept re-adding already-built paths.

**Fix (three changes):**
1. **Persistent dedup.** `drainTodo`'s local `added` set is promoted to the field `mCollected`,
   so a subpath enters `mAllPaths` at most once across all drains of a lemma. (Per-conflict
   instances are fresh from the constructor, so no clearing is needed.)
2. **Inline via `computePathNonRecursive`.** The two graft sites in `WeakCongruencePath`
   (`collectPathOnePrimary`, `collectPathPrimary`) call `computePathNonRecursive(left, right)`
   directly and `addSubPath` the returned `SubPath`. `computePathNonRecursive` returns the path
   (cached or freshly built), enqueues its congruence dependencies on `mTodo`, and — crucially —
   **never adds it to `mAllPaths`** (correct: an inlined path is not a standalone annotation
   path). The dependencies are collected by the enclosing lemma's drain. This removes both the
   `removeFirst` call and its ordering assumption; you get the right `SubPath` by return value
   regardless of what else is pending in `mTodo`. Strong paths that *are* standalone annotation
   subpaths (the index/select equalities in `computeWeakCongruencePath`) keep using `computePath`.
3. **Explicit drain in `computeConstOverWeakEQ`.** It was the one lemma method with no
   `drainTodo()` of its own — it worked only because `collectPathPrimary` drained internally.
   With the internal graft-drains gone, it now calls `drainTodo()` before `mAllPaths.addFirst(path)`
   (the drain must precede the prepend so the main path lands ahead of its dependencies). The
   other lemma methods already drain at the right spot before each manual `addFirst`.
4. **`computeMergeConflictCycle` builds its two halves the same way.** It used to
   `computePath(srcEnd, lhs)` / `computePath(rhsTerm, destEnd)`, drain, then re-fetch the halves via
   `mVisited.get(SymmetricPair(...))` and filter them back out of `mAllPaths`
   (`for (p : mAllPaths) if (p != segSrc && p != segDest)`). Now it calls
   `computePathNonRecursive` for each half directly: the `SubPath`s come back by return value (no
   `mVisited` lookup), they never enter `mAllPaths` (no filter), and only their congruence
   dependencies plus the bridge's argument subpaths are drained — so `mAllPaths` *is* the
   other-paths list and is passed straight to the `CCAnnotation` constructor (which only iterates
   it, so no copy). The two halves must be built before the drain regardless of `produceProofs`,
   since that is where their literals reach `mAllLiterals` for the clause.

Validated (clean build, `-ea`): `test/proof` **97/98** (only the pre-existing
`trivialdiseqarray`, identical to baseline); `array/` + interpolation `.smt2` under
`proof-check-mode` have an **identical pass/fail set** to a reverted baseline (the
`constarr00{4,5,11,12,14}` interpolation failures are pre-existing in the deferred
offset-interpolation track); `BitvectorTest`, `ProofSimplifierTest`, `ProofUtilsTest`,
`RPITest`, `CongruentAddTest` green (117 tests); `abv`/`uflira`/`lia` sweeps clean.
Files: `CongruencePath.java`, `WeakCongruencePath.java`.

## Offset-aware array weak-eq propagation (the `trivialdiseqarray` blocker) — DONE (uncommitted)

`trivialdiseqarray` (`a = (store (const ((select a j) + 1)) i 1)`, `i != j`) returned **sat**
for an unsat problem — the lone remaining `test/proof` failure. The unsat reasoning is: with
`i != j`, `a` and the const array agree at `j`, so `select(a, j) = const value = (select a j) +
1`, i.e. `x = x + 1`, a (same-class, different-offset) offset conflict. Two array-side spots
dropped the offset and suppressed it (an instance of gap 1, the `ArrayTheory` part):

1. **Offset-blind propagation guards** (`ArrayTheory`, four sites: `READ_OVER_WEAKEQ` /
   `READ_CONST_WEAKEQ` in both the primary-merge `mergeWith` path and the secondary-edge path).
   They skipped propagation with `select.getRepresentative() != other.getRepresentative()`. Two
   selects (or a select and a const value) in the *same* class but at *different* offsets are
   **not** already equal — that is exactly the conflict — so the guard threw the conflicting
   lemma away. Fixed to the offset-aware `!select.sameValueAs(other)`
   (`(getRepresentative(), getOffsetToRep())` identity). The sibling `CONST_WEAKEQ` guard already
   compared offsets; these four now match it. With offsets off, `sameValueAs` reduces to a
   representative comparison, so behaviour is unchanged in the classic mode.
2. **Offset dropped building the lemma equality** (`WeakCongruencePath.generateClause`): it called
   `createEquality(diseq.getFirst().getCCTerm(), diseq.getSecond().getCCTerm(), …)`, stripping to
   bare `CCTerm`s → the degenerate `select(a,j) = select(a,j)` (which trips the `createEquality`
   `t1 != t2 || offset != 0` assertion once the guard above fires). Fixed to pass the
   `CCParameter`s to the offset-aware overload, which builds `select(a,j) = select(a,j)+1`,
   recognizes the false proxy (`eq == null`, already handled), and lets the lemma become the
   conflict clause over its premises.

`trivialdiseqarray` is now **unsat**, with a low-level proof that proof-checks (`read-const-weakeq`
derives `select(a,j) = select(a,j)+1`; an `EQ`/farkas lemma refutes it).

*Debug-output note:* the LA `Shared Vars` / `Assignments` dump (`LinArSolve.getSharedCongruences`)
prints `sharedTermValue`, the **offset-free** LA value with no structural constant, so e.g.
`(+ (select a j) 1)` printed `= 2` alongside `(select a j) = 2` (the `+1` is a CC offset, not in
the LA value) — misleading when reading a model, but not the cause of the bug. The
equivalence-class dump (`CClosure.dumpModel`) does print offsets (`[+k]`).

Validated (clean build, `-ea`): `test/proof` **98/98** (`trivialdiseqarray` fixed, no
regressions); array-relevant sweep (93 benchmarks under `proof-check`) has **0 status mismatches**
and only pre-existing errors (`constarr00{4,5,11,12,14}` offset-interpolation, `Script_simple`);
`BitvectorTest`/`ProofSimplifierTest`/`ProofUtilsTest`/`RPITest`/`CongruentAddTest` green (117
tests). Files: `ArrayTheory.java`, `WeakCongruencePath.java`.

## Offset-aware array extensionality fingerprint + model values — DONE (uncommitted)

An audit of `ArrayTheory` for offset correctness found index handling solid (everything keys on
`CCParameter.getValueKey()` = `(representative, offsetToRep)`) and the value-propagation guards
fixed by the previous increment, but **two value spots still dropped the offset** — the more
serious one a soundness bug in extensionality:

1. **`computeWeakeqExt` model fingerprint (soundness).** The per-array `nodeMapping` that drives
   `weakeq-ext` stored element values as bare representatives (`getRepresentative()`), so two arrays
   whose elements agree only **up to a constant offset** got the same fingerprint, collided in the
   `inverse` map, and `weakeq-ext` propagated a spurious `a = b`. Minimal witness (genuinely sat):
   `(not (= (store c i y) (store c i (+ y 1))))` was reported **unsat** (the spurious `a = b`
   conflicts with the asserted disequality). Fixed to store value identities
   (`getValueKey()`) and compare with `equals()` (offset value-keys are fresh `OffsettedCCTerm`
   objects, so the old `!=` reference test would not even match equal offset values); `constRep` and
   the `defaultValue` cache become `CCParameter`. Precision only improves — two arrays still match
   iff they agree at every index *including* offsets, so no valid extensionality is lost. The
   witness is now **sat**.
2. **`fillInModel` element values (wrong models).** The const value (`getValueFromConst(..)
   .getRepresentative()`), the per-index select values (`.getRepresentative()`), the finite-elem
   default (read back from `mArrayModels`), and the secondary-edge select (`getModelValue(ccValue)`)
   all fed a bare representative to `getModelValue`, dropping `offsetToRep`. The fix passes
   `CCParameter`s (`getValueFromConst(..)` directly, or `getValueKey()` for selects). Verified
   with `model-check-mode`: `a = (store (const (+ y 3)) i (+ y 1))`, `i != 0` yields a consistent
   model (`y=-2`, `select(a,i)=-1`, `select(a,0)=1`).

Follow-up: the error-prone `getModelValue(CCTerm)` accessor (returns the representative's value,
silently dropping a member's offset) was **removed** in favour of the single offset-aware
`getModelValue(CCParameter)` — a bare `CCTerm` is an offset-free parameter, so all former callers
(array/datatype/boolean terms, all non-numeric or representatives) bind to it with identical
behaviour, while any numeric member now necessarily goes through the offset-shifting path. Removing
the overload is binary-incompatible, so callers in other files (e.g. `DataTypeTheory`) must be
recompiled — a clean build is required (an incremental rebuild leaves a stale `.class` referencing
the deleted method and throws `NoSuchMethodError`).

Validated (clean build, `-ea`): `test/proof` **98/98**; the extensionality witness is `sat` (was
`unsat` on the pre-fix build, confirming the soundness bug); array-relevant sweep (93 benchmarks,
`proof-check`) **0 status mismatches**, only the pre-existing errors; `datatype`/`model` dirs 30/30;
117 JUnit tests green. Files: `ArrayTheory.java`, `ModelBuilder.java`.

## Explicit select/const edge in weakeq-ext annotations — DONE (uncommitted)

Preparation for offsets under proofs. In a `weakeq-ext` lemma, each weak-i path may
contain one *select/const edge*: the step where two arrays are weakly-i-equivalent
not by a store or a strong equality but because a select equality
`select(a1,j1) = select(a2,j2)` (or `select(a1,j1) = v` for `a2 = (const v)`) holds
with `j1, j2` equal to the path index. Until now the edge was *not* recorded — three
consumers (`CCProofGenerator.findSelectPath`, `ProofSimplifier.proveSelectPath`, and
`ArrayInterpolator`) each re-derived it by iterating the clause equalities. With
offset equalities this search becomes ambiguous: the justifying equality is
offset-rendered (`EqualityProxy.getLiteral` builds `(= mLhs (+ mRhs off))`, and the
`CCTermPairHash` identity-hash canonicalization can move the constant onto the
*select* side, e.g. `(= core (+ (select a1 j1) off))`), so neither atom side is the
bare select the searcher matches on, and among several candidates only one is right.

Fix: record the edge in the annotation and let the consumers read it.

- **`WeakCongruencePath.WeakSubPath`** gains `mSelectLeft`/`mSelectRight`
  (`CCParameter`, with offset), set by `computeWeakCongruencePath` — the one place
  the edge is known (`select1`/`select2`), ordered `path[0]`-side then
  `path[last]`-side. Plain weak paths leave it null; it is *always* null for
  read-over-weakeq / read-const-weakeq (their weak paths have no select step).
- **`CCAnnotation`** carries a parallel `mSelectEdges[i]` (`{left, right}` or null)
  populated from the `WeakSubPath`, with a getter.
- **Term format:** the `:weakpath` value stays `{index, subs}` when there is no edge
  and becomes `{index, subs, {leftTerm, rightTerm}}` when there is one
  (`CCProofGenerator.buildLemma`). Backward-tolerant: `ArrayInterpolator.ProofPath`
  reads only `[0]`/`[1]` and ignores the third element.
- **`CCProofGenerator.collectWeakPath`** uses the annotated edge (oriented against the
  step's two arrays via `isSelect`/`isConst` in the new `orientSelectEdge`); it only
  falls back to `findSelectPath` if no edge is present.
- **`ProofSimplifier`** parses the edge from `:weakpath[2]` and threads it through
  `proveSelectOverPath` → `proveSelectOverPathStep`, feeding the edge's
  `getFlatTerm()` (a bare select, or the const's full stored value) directly to
  `proveSelectConst`. This sidesteps the affine-extraction problem: those terms match
  `proveSelectConst` as-is, and the offset-rendered clause equality is bridged by
  `resolveNeededEqualities` (`OffsetEqKey` + `proveEqWithMultiplier`). Match is decided
  by `proveSelectConst` succeeding on both sides, *not* by the returned proof —
  `proveSelectPathTrans` legitimately returns `null` for a trivial step (the edge
  selects coincide with the path-end selects), which must not be read as "no match".
  `proveSelectPath` is kept only as a fallback for an absent edge.

The change is validated with offsets *off* (the format machinery is exercised;
select edges are offset-0): the array + interpolation `proof-check-mode` +
`proof-level lowlevel` sweep is unchanged versus baseline (only the pre-existing
deferred offset-interpolation and datatype failures remain — `CCInterpolator` throws
on offset lemmas). Instrumentation on `constarr014` (68 select edges) confirms the
annotated edge is used for every select step and the search fallback is never hit in
any passing test. Files: `WeakCongruencePath.java`, `CCAnnotation.java`,
`CCProofGenerator.java`, `ProofSimplifier.java`.

**Still open (the reason this is preparation):** `proveSelectConst` does not yet
handle a select/const edge whose select sits at an LA/offset-equal index, or a const
value carrying a non-zero offset — i.e. offsets *under proofs*. The edge is now
delivered explicitly (bare select + full const value), so this handling no longer has
to contend with the search ambiguity; it is the natural next step.

## Syntactic `OffsetEqKey` (constant-last canonic sums) — DONE (uncommitted)

`ProofSimplifier.OffsetEqKey` no longer parses its sides with `Polynomial` into
summand hashmaps; a new `OffsetTerm` splits a side purely syntactically — a trailing
constant summand of a `+` application is the offset, dropping it yields the
offset-free part (a plain `Term`, compared by identity). A side that is entirely
constant splits into the base `0` term and its value as offset, mirroring the `0`
base CCTerm of a plain-numeral parameter; correspondingly `CCParameter.addConstant`
folds a constant base into a plain constant (`5`, not `(+ 0 5)`), agreeing with the
canonic term of that value (and with `Clausifier.addConstantToTerm`). Constants in
any *other* position stay inside the offset-free part (harmless when offsets are
off, since keys then only compare identical flat terms).

This is sound because the split is now the exact inverse of term construction:
`TermCompiler.unifyPolynomial` canonicalizes a constant-carrying polynomial as
`CCParameter.addConstant(unifyPolynomial(constantFreePart), constant)`, so canonic
compiler terms, `Clausifier.addConstantToTerm` results and annotation flat terms
(`CCParameter.getFlatTerm`/`addConstant`) are all byte-identical per value, with the
constant last. `BvToIntUtils` was the one producer bypassing the unifier (direct
`Polynomial.toTerm`, e.g. `normalizeMod` emitted `(+ x 255 (* -256 (div …)))` with
the constant mid-sum, which made `resolveNeededEqualities` miss the clause literal
and emit an invalid trichotomy farkas on `abv/indexInRange01`, `ufbv/ufbv01`); all
its polynomial-term exits now go through `mPolyUnifier`. Full unit suite matches the
baseline (only the known pre-existing SystemTest failures). Files:
`ProofSimplifier.java`, `TermCompiler.java`, `BvToIntUtils.java`, `CCParameter.java`.

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

---

# Quantifier support (offset-aware e-matching) — planned

Offsets are currently disabled whenever a `QuantifierTheory` exists
(`Clausifier.createOffsetEqualities()` requires `mQuantTheory == null`), because
e-matching binds variables to offset-free CCTerms and loses the constant (the
recorded unsoundness in `quanttest001`: match `a(x)` against `a(l+1)` but
instantiate `x := l`). This section maps every CC touch point in `theory/quant`
and plans the migration. The EPR theory is ignored (slated for deletion).

## Inventory: where the quantifier theory touches CC values

**A. The e-matching register is `CCTerm[]`** — the core representation gap.
`ICode.execute(CCTerm[], int)`, `EMatching.mTodoStack`/`mClauseCodes`/`addCode`,
`PatternCompiler.compile()` (builds the initial register; note
`TermInfo.mGroundTerm` is `(CCTerm) clausifier.createCCTerm(...)` — that cast
throws for a ground pattern subterm like `(+ a 2)` once offsets are on),
`EMReverseTrigger.mRegister`, `EMCompareTrigger.mRegister`. A register slot
holds a *value* (candidate for a pattern subterm or a variable binding), and
values are `CCParameter`s now. Whole-pattern candidates are always `CCAppTerm`s
(offset 0); only argument values / variable bindings carry offsets.

**B. `GetArgCode` strips the offset** (`getArgParam(pos).getCCTerm()`, with an
explicit "offsets are off under quantifiers" comment). This is *the* unsound
line: binding a variable from `f(a+2)`'s argument must yield the value `a+2`.

**C. Compare triggers — SETTLED, almost trivial (Jochen).** The trigger is keyed
on the base-term pair plus the *structural* offset δ = o2 − o1 (from
value(t1)+o1 == value(t2)+o2, i.e. value(base1) = value(base2) + δ; stable, so
`EMCompareTrigger` can store the two `CCParameter`s and recompute δ at remove
time). Verified against the code, nearly everything is already in place:
- **Merge-time activation is already offset-selective.**
  `CCTerm.mergeInternal` fires `info.mCompareTriggers` only in the
  `offFromSrc.equals(delta)` branch; the conflicting-offset branch leaves them
  untouched — they ride along dormant in the removed Info and come back on
  unmerge. Since there is no "definitely distinct" event in the machinery,
  nothing needs to happen on a conflicting-offset merge, and nothing does.
- **`insertCompareTrigger`/`removeCompareTrigger` copy the
  `insertEqualityEntry` walk** (CClosure.java:730): negate δ on the merge-time
  swap, re-base when stepping `t1 = t1.mRep` (`offset − t1.offsetToRep +
  t1.mRep.offsetToRep`), and match `pentry.getOffsetToOther()` when scanning
  `mPairInfos`. Just a few CCTerm→CCParameter/offset changes.
- **Same rep, wrong offset at install time:** the trigger can never fire in the
  current subtree, so per Jochen it need not be installed (drop the
  continuation). Note the `insertEqualityEntry` walk would park it for free —
  it has no different-reps assert; the walk terminates via `isLast = t1.mRep ==
  t2` and leaves the entry in the merge-boundary Info, which goes live again on
  unmerge — which matters only when the conflicting merge is *younger* than the
  register data (data at level 0, merge at level 3: backtrack to 1 keeps the
  trigger, a later matching merge fires it; dropping misses that instance).
  Either way it is the same walk; pick during implementation.
`CompareCode` itself becomes: `sameValueAs` → proceed; otherwise install (or
drop in the same-rep case, per the previous point).

**D. Reverse triggers.** `ReverseCode` reads the arg from the register (now a
`CCParameter`) and `CClosure.insertReverseTrigger(sym, CCTerm arg, pos, trig)`
takes a bare CCTerm. The underlying machinery is already value-keyed
(`ReverseTrigger.getArgument()` returns `CCParameter`;
`ReverseTriggerTrigger`/`MasterReverseTrigger`/`SignatureTrigger` key on
`getOffsetToRep`), so this is mostly signature plumbing: make
`EMReverseTrigger.mArg` a `CCParameter` and let `insertReverseTrigger` accept
it. `EMReverseTrigger.activate` compares `mArg` with
`appTerm.getArgParam(pos)`: the *decide level* path
(`getDecideLevelForPath`) stays on the offset-free `getCCTerm()`s (the merge
path is the same for all offsets); the value match is guaranteed by the
signature.

**E. Yield / SubstitutionInfo.** `SubstitutionInfo.mVarSubs` is
`List<CCTerm>`, `mEquivalentCCTerms` is `Map<Term, CCTerm>`; both become
`CCParameter`. Dawg keys come from `varSubs.get(i).getFlatTerm()` —
`CCParameter.getFlatTerm()` already renders the flattened `(+ a 2)`, so the
Term-keyed dawg layer is unaffected once the values are right.

**F. Canonicalization drops offsets.**
`QuantifierTheory.getRepresentativeTerm(term)` does
`getCCTerm(term).getRepresentative().getFlatTerm()`. Two problems: (i)
`Clausifier.getCCTerm` now *asserts* its argument is offset-free, and
interesting terms / substitutions are value terms like `(+ a 2)`; (ii) the rep
flat term drops the offset — the values `a` and `a+1` in one class would
canonicalize to the same key, conflating *different* substitutions in
`addAllInteresting` and `getRepresentativeSubsDawg` (the dedup dual of the
`quanttest001` unsoundness). Fix: split via
`getOffsetFreeTerm`/`getTermConstant`, then return
`CCParameter.addConstant(rep.getFlatTerm(), k + offsetToRep)` — the canonical
*value* term.

**G. Ground-side CC lookups on possibly-offsetted terms** (all hit the
`getCCTerm` assert or silently miss): `InstantiationManager.getTermAge`,
`evaluateCCEquality`/`evaluateCCEqualityKnownShared` (ground lhs/rhs of a
`QuantEquality` can carry a constant, e.g. `x = t+3`),
`evaluateLitForPartialEMatchingSubsInfo` (`getCCTerm(clauseVarSubs.get(i))`),
`QuantifierTheory.addGroundCCTerms` (recurses into ground subterms like
`(+ a 1)`). Each needs the offset-free-part + constant split. The equality
evaluation itself needs value semantics: `isEqSet` → `sameValueAs` on
`CCParameter`s; `isDiseqSet` is already offset-aware internally but needs a
`CCParameter` entry point. Same-rep-different-offset evaluates to **FALSE**
(new case — today same rep means TRUE).

**H. `CClosure.getCCTermRep(Term)`** (used by
`InstantiationManager.TermFinder` to find an existing congruent term for an
instance term) recurses with offset-free `CCTerm[]` argReps and an offset-free
`SignatureTrigger`. It must become `CCParameter`-based: parse each argument's
constant, build the signature on value keys, and return a `CCParameter`
(rep + offset) so `FindSharedAppTerm`/`FindSharedAffine` record the true value
term, not the rep's offset-free flat term.

**I. `QuantClause`.** `updateInterestingTermsForFuncArgs` drops offsets:
`appTerm.getArgParam(i).getCCTerm().getFlatTerm()` → `getArgParam(i)
.getFlatTerm()`; same for the select-index branch (existing `TODO: add offset`
at the `ArrayTheory.getIndexFromSelect` site). Dedup via
`getRepresentativeTerm` is fixed by F. The `collectVarInfos:338` crash
(`datatype/quantified/*match*`, 4 tests) turned out to be **pre-existing with
offsets off and unrelated to this work**: the quantified equality has a
`MatchTerm` side (`(match l1 ...)` with free variables) and the assert
`rhs instanceof ApplicationTerm` rejects it — a missing quantified-`match`
feature in the quantifier theory, out of scope here (earlier notes
miscategorized it as an offset blocker because it was observed during
gate-flip validation).

**J. Unaffected (checked):** `SubstitutionHelper`, `DestructiveEqualityReasoning`,
`QuantAuxEquality` (Term-level only); `Dawg` (Term-keyed);
`evaluateLAEquality*`/`evaluateBoundConstraint*` (Polynomial-level);
`checkCompleteness` (lambdas are fresh offset-free constants);
`getDecideLevelForPath` (paths are offset-free).

**K. Follow-ups enabled/required by the flip:**
- The **reverse-trigger clash-slot source** in
  `CClosure.getNumericClashSlots()` (documented deferred: e-matching reverse
  triggers with `getArgPosition() != -1` and numeric arg sort) becomes *live*
  once quantifiers run with offsets — MBTC must see e-matching positions.
- Proofs: instantiation lemmas substitute real SMT terms, and `(+ a 2)` is one;
  the `:inst` rule should be term-level clean, but validate with
  `proof-check-mode` once both gates (quantifier and proof) are open.

## What offsets *buy* e-matching (the extension, separate step)

Today the fragment forbids arithmetic below uninterpreted functions
(`QuantUtil.containsArithmeticOnQuantOnlyAtTopLevel`,
`isEssentiallyUninterpreted` rejects `f(x+3)`). With offset CC, a pattern
argument `x + k` (variable-plus-constant, and more generally `t + k`) is
matchable for free: `GetArgCode` yields the value `v`, the binding is
`x := v − k` (constant shift on a `CCParameter`); `CompareCode` compares
shifted values. That extends the almost-uninterpreted fragment with constant
offsets under function symbols (`f(x+3) = g(y)` etc.) — the actual quantifier
payoff of the offset project. Requires: `PatternCompiler` support for affine
arguments (constant part only), a shift field on GetArg/Compare codes, fragment
checks widened (`isEssentiallyUninterpreted`,
`containsArithmeticOnQuantOnlyAtTopLevel`, `containsAppTermsForEachVar`), and
`QuantClause.addVarArgInfo`/`VarInfo` positions that record the shift so
interesting-term collection proposes `groundArg − k`. Non-constant coefficients
and multi-variable arguments stay out.

## Increments

- **Q1 — `CCParameter` register. (DONE, uncommitted.)** Mechanical
  thread-through of A/B/E: register `CCTerm[]` → `CCParameter[]` everywhere in
  `ematching/`, `GetArgCode` keeps the offset, `SubstitutionInfo` holds
  `CCParameter`s, `PatternCompiler` ground slots stop casting. Type change
  propagates into `InstantiationManager` (equivalent-CCTerm maps, var subs;
  asserts use `sameValueAs`). `CompareCode`: `sameValueAs` → proceed; same base
  term at different structural offsets → drop (can never become equal);
  otherwise install. Offset-free behavior verified byte-identical
  (`test/quantified` + `test/datatype/quantified` outputs diff-identical to
  baseline under `-ea`; full `ant runtests` 723/723).
- **Q2 — CClosure API. (DONE except `getCCParamRep`, uncommitted.)**
  `insertCompareTrigger(CCParameter, CCParameter, trigger)` /
  `removeCompareTrigger` mirror the `insertEqualityEntry` offset walk
  (including the same-class park-at-boundary case — chosen over dropping since
  it is the same walk anyway); merge-time activation was already
  offset-selective; `insertReverseTrigger(CCParameter)`; `isEqSet`/`isDiseqSet`
  on `CCParameter` (`isEqSet` = `sameValueAs`; all callers were quant-side and
  want value semantics). `isDiseqSet` also returns true for same-rep pairs at
  different offsets (provably distinct by a non-zero constant; Jochen) — the
  same-rep case is now fully decided between `isEqSet`/`isDiseqSet`, and the
  degenerate `getInfo(rep, rep, ·)` lookup is avoided. Still open:
  `getCCTermRep` → `getCCParamRep` (needed in Q3 for `TermFinder`).
- **Q3 — evaluation & canonicalization. (DONE, uncommitted.)** New
  `Clausifier.getCCParameter(Term)` (offset-free split + `CCParameter.of`);
  `getRepresentativeTerm` returns the canonical *value* term
  (`getValueKey().getFlatTerm()`); `getTermAge`/`evaluateCCEquality
  (KnownShared)`/partial-EM var-subs lookup use `getCCParameter`;
  `addGroundCCTerms` normalizes via `getOffsetFreeTerm`; `getCCTermRep` →
  `getCCParamRep` (constant split, value-keyed signature lookup, returns
  rep+offset; `TermFinder` and the QuantClause array lookup adapted);
  `QuantClause` interesting terms keep offsets (`getArgParam(i).getFlatTerm()`,
  select-index TODO resolved). Same-rep-wrong-offset evaluates FALSE via the
  `isDiseqSet` same-class case. `collectVarInfos:338` needs no fix here (see I).
- **Q4 — flip the quantifier gate. (DONE, uncommitted.)** Dropped
  `mQuantTheory == null` from `Clausifier.createOffsetEqualities()` — this also
  dissolves the raw-vs-effective flag divergence (the `bitVecLearnConflict2`
  class of bugs), since both predicates now coincide. Reverse-trigger
  clash-slot source added to `getNumericClashSlots()` (watched values of
  installed reverse triggers join their (symbol, position) slot;
  `ReverseTriggerTrigger.getTriggers()` accessor). NOTE the proof gate was
  already open at HEAD (`CClosure.createOffsetEqualities` no longer checks
  `isProofGenerationEnabled`), so this flip enables offsets under
  quantifiers+proofs+interpolation together. Validation: new
  `test/quantified/offsetmatch001..003` (offset binding `x := a+3`; a/a+1
  dedup-distinctness; spurious-unsat guard — all pass with `-ea`);
  `quanttest001` unsat; all `test/quantified` verdicts unchanged with
  offset-shaped proofs/checked interpolants (`ArrayInitialization02` has
  `interpolant-check-mode true`); full `ant runtests` **726/726** incl.
  SystemTest (lowlevel proof-check + model-check + interpolant-check on the
  whole corpus) and BitvectorTest.
- **Q5 — offset patterns** (the fragment extension above). Independent,
  largest, do after Q4 is stable.

Q1+Q2 are the substantial work; Q3 is broad but mechanical; the compare-trigger
offset semantics (C) is the one genuinely new CC mechanism.
