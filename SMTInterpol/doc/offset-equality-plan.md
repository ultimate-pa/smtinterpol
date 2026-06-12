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
