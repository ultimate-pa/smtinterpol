/*
 * Copyright (C) 2009-2012 University of Freiburg
 *
 * This file is part of SMTInterpol.
 *
 * SMTInterpol is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * SMTInterpol is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with SMTInterpol.  If not, see <http://www.gnu.org/licenses/>.
 */
package de.uni_freiburg.informatik.ultimate.smtinterpol.theory.cclosure;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedHashSet;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.Clause;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.Literal;
import de.uni_freiburg.informatik.ultimate.smtinterpol.proof.LeafNode;
import de.uni_freiburg.informatik.ultimate.smtinterpol.util.SymmetricPair;

/**
 * This class generates congruence lemmata and their explanation.
 * It takes the CClosure and extracts from it a path of equalities that
 * connect two equivalent CCTerm.  It also computes the required
 * congruences.  All literals are collected and if proof production
 * is enabled, also the paths are collected and remembered.
 *
 *
 * @author Jochen Hoenicke
 *
 */
public class CongruencePath {

	final CClosure mClosure;

	/**
	 * This is the data structure that remembers an equality path if
	 * proof production is enabled.  It just is a list of ccterms that
	 * are connected by equality edges or congruences.
	 *
	 * This data structure is only in use if proof production is enabled.
	 *
	 * @author Jochen Hoenicke
	 */
	public static class SubPath {
		ArrayList<CCTerm> mTermsOnPath;

		public SubPath(final CCParameter start) {
			this(start, true);
		}

		public SubPath(final CCParameter start, final boolean produceProofs) {
			if (produceProofs) {
				mTermsOnPath = new ArrayList<>();
				mTermsOnPath.add(start.getCCTerm());
			}
		}

		/**
		 * The path nodes as {@link CCParameter}s, offset so that every node has the same value as {@code anchor}:
		 * {@code value(node) + offset == value(anchor) + anchor.getOffset()}. So if {@code x = y+4} and {@code y = z+2},
		 * a path rendered with anchor {@code x+2} reads {@code x+2, y+6, z+8}. The relative offsets are intrinsic
		 * ({@link CCTerm#getOffsetToRep} differences), so the anchor only fixes the absolute base and the result is
		 * stable under {@link #addSubPath} concatenation. The anchor is typically one of the path's own nodes.
		 *
		 * <p>The {@code anchor} is treated as the <em>start</em> of the path: its term must be one of the path's two
		 * endpoints, and the result is oriented so that the anchor's term is first (the stored term list may run either
		 * way, since {@link #mVisited} keys paths by an undirected {@link SymmetricPair}). The anchor's term renders at
		 * {@code anchor.getOffset()} and the other endpoint follows from the intrinsic relative offsets.
		 *
		 * <p>{@link CCTerm#getOffsetToRep} is relative to each node's own representative, so for two nodes in different
		 * classes the difference mixes reference frames and yields garbage offsets — the bug behind several earlier
		 * offset conflicts (a path built over a freshly added, not-yet-united merge bridge). For <em>numeric</em> terms
		 * we therefore assert the anchor shares the representative of every node; the conflict builders that legitimately
		 * span two classes ({@link #computeMergeConflictCycle}, {@link #computeAntiCycleDiffClass}) avoid this by rendering
		 * each single-class half separately. The only paths that genuinely cross classes are non-numeric (weak-array
		 * paths over distinct strong classes), and a non-numeric term can never carry an offset, so the rendering is
		 * trivially correct (offset zero) regardless of frame.
		 */
		public CCParameter[] getParams(final CCParameter anchor) {
			final int n = mTermsOnPath.size();
			assert mTermsOnPath.get(0) == anchor.getCCTerm() || mTermsOnPath.get(n - 1) == anchor.getCCTerm()
					: "getParams anchor must be a path endpoint";
			// Orient the path so the anchor's term is first. The stored term list may run either way (mVisited keys
			// paths undirected), so if the anchor is the stored last node, render in reverse.
			final boolean reversed = mTermsOnPath.get(0) != anchor.getCCTerm();
			final CCParameter[] params = new CCParameter[n];
			for (int i = 0; i < n; i++) {
				final CCTerm t = mTermsOnPath.get(reversed ? n - 1 - i : i);
				assert !t.getFlatTerm().getSort().isNumericSort()
						|| anchor.getRepresentative() == t.getRepresentative()
						: "getParams anchor must share the congruence class of every numeric node";
				params[i] = CCParameter.of(t, anchor.getOffsetToRep().sub(t.getOffsetToRep()));
			}
			return params;
		}

		/** {@link #getParams(CCParameter)} self-anchored at the path's first node (offset 0). */
		public CCParameter[] getParams() {
			return getParams(mTermsOnPath.get(0));
		}

		public void addEntry(final CCTerm term, final CCEquality reason) {
			if (mTermsOnPath != null) {
				mTermsOnPath.add(term);
			}
		}

		public void addSubPath(final SubPath second) {
			if (mTermsOnPath != null && second != null) {
				if (second.mTermsOnPath.get(0)
						== mTermsOnPath.get(mTermsOnPath.size() - 1)) {
					for (int i = 1; i < second.mTermsOnPath.size(); i++) {
						mTermsOnPath.add(second.mTermsOnPath.get(i));
					}
				} else {
					/* sub path is reversed */
					assert (second.mTermsOnPath.get(second.mTermsOnPath.size() - 1)
							== mTermsOnPath.get(mTermsOnPath.size() - 1));
					for (int i = second.mTermsOnPath.size() - 2; i >= 0; i--) {
						mTermsOnPath.add(second.mTermsOnPath.get(i));
					}
				}
			}
		}

		@Override
		public String toString() {
			return mTermsOnPath.toString();
		}
	}

	/**
	 * Visited subpaths, keyed by the <em>offset-free</em> end terms. Two requested paths that differ only by a constant
	 * offset (e.g. {@code x+5 = y+7} and {@code x+7 = y+9}, both for the edge {@code x = y+2}) share one key, so only a
	 * single subpath is built; consumers (e.g. {@link CCProofGenerator}) absorb the per-use constant difference.
	 */
	final HashMap<SymmetricPair<CCTerm>,SubPath> mVisited;
	final ArrayDeque<SubPath> mAllPaths;
	final ArrayDeque<SymmetricPair<CCParameter>> mTodo;
	final Set<Literal> mAllLiterals;

	/** The offset-free end terms of a parameter pair, used as the {@link #mVisited} key. */
	private static SymmetricPair<CCTerm> offsetFreeKey(final SymmetricPair<CCParameter> ends) {
		return new SymmetricPair<>(ends.getFirst().getCCTerm(), ends.getSecond().getCCTerm());
	}

	public CongruencePath(final CClosure closure) {
		mClosure = closure;
		mVisited = new HashMap<>();
		mAllLiterals = new LinkedHashSet<>();
		mTodo = new ArrayDeque<>();
		mAllPaths = new ArrayDeque<>();
	}

	private CCAnnotation createAnnotation(final SymmetricPair<CCParameter> diseq) {
		return new CCAnnotation(diseq, mAllPaths, CCAnnotation.RuleKind.CONG);
	}

	private int computeDepth(CCTerm t) {
		int depth = 0;
		while (t.mEqualEdge != null) {
			t = t.mEqualEdge;
			depth++;
		}
		return depth;
	}

	/**
	 * Compute the conflict set and interpolation information for the
	 * congruence path from start to end.  The terms must be congruent AppTerms,
	 * i.e. their func and arg values are congruent.
	 *
	 * The interpolation info should contain the path preceding the congruence,
	 * its tailNr should correspond to the last formula number of the equality edge
	 * pointing to start in the circle.  The parameter tailNr should correspond to
	 * the equality edge pointing to end in the circle.
	 *
	 * @param mVisited a set of equality pairs that were already visited.  This is
	 * used to prevent double work.
	 * @param set  the set of literals in the conflict clause.
	 * @param info the interpolation info containing head/tail interfaces, and collecting
	 * the equality chains.
	 * @param tailNr the last formula number of equality edge connecting end in the
	 *  congruence graph circle.
	 * @param start one of the function application terms.
	 * @param end the other function application term.
	 */
	private void computeCongruence(CCAppTerm start, CCAppTerm end) {
		// Pair the argument values (CCParameters), so the recorded subpath for each argument is anchored at the
		// argument's offset, e.g. f(x+2) congruent f(z+8) yields a subpath from x+2 to z+8. This only enqueues the
		// argument pairs; the surrounding drain loop ({@link #drainTodo}, run by {@link #computePath}) builds them.
		for (int i = 0; i < start.getArgCount(); i++) {
			mTodo.addFirst(new SymmetricPair<>(start.getArgParam(i), end.getArgParam(i)));
		}
	}

	/**
	 * Compute the conflict set and interpolation information for the
	 * congruence path from term t to end.  The terms must be directly connected by the
	 * equalEdge graph, i.e. end is reachable from t by repeatedly following the
	 * equalEdge field.  The last equalEdge must be induced by a equality literal not a
	 * congruence edge.
	 *
	 * The interpolation info should be empty, its head/max/lastNr should correspond
	 * to the last formula number of the edge preceding t in the circle.
	 *
	 * @param mVisited a set of equality pairs that were already visited.  This is
	 * used to prevent double work.
	 * @param set  the set of literals in the conflict clause.
	 * @param info the interpolation info containing head/tail interfaces, and collecting
	 * the equality chains.
	 * @param t the first term in the path.
	 * @param end the last term in the path.
	 * @return the sub path from t to end, if proof production is enabled.
	 *   Without proof production, this returns null.
	 */
	private SubPath computePathTo(final CCParameter startParam, final CCTerm end) {
		final SubPath path =
				new SubPath(startParam, mClosure.isProofGenerationEnabled());
		CCTerm t = startParam.getCCTerm();
		CCTerm startCongruence = t;
		while (t != end) {
			if (t.mOldRep.mReasonLiteral != null) {
				if (startCongruence != t) {
					/* We have a congruence:  The terms startCongruence and t are congruent.
					 * Compute the paths for the func and arg parts and merge into the
					 * interpolation info.
					 */
					computeCongruence((CCAppTerm) startCongruence, (CCAppTerm) t);
					path.addEntry(t, null);
				}
				/* Add the equality literal to conflict set */
				path.addEntry(t.mEqualEdge, t.mOldRep.mReasonLiteral);
				mAllLiterals.add(t.mOldRep.mReasonLiteral);
				startCongruence = t.mEqualEdge;
			}
			t = t.mEqualEdge;
		}
		assert (startCongruence == t);
		return path;
	}

	/**
	 * Compute the conflict set and interpolation information for the
	 * congruence path from term left to right.  The interpolation info should be
	 * empty and its head/max/tailNr should be equal to the (last) formula number of
	 * the equality that precedes left in the conflict circle.  The parameter tailNr
	 * should give the (last) formula number of the next equality after right.
	 * On return info.tailNr is equal to tailNr.
	 *
	 * @param mVisited a set of equality pairs that were already visited.  This is
	 * used to prevent double work.
	 * @param set  the set of literals in the conflict clause.
	 * @param info the interpolation info containing head/tail interfaces, and collecting
	 * the equality chains.
	 * @param tailNr this gives the (last) formula number of the equality after right.
	 * @param left the left end of the congruence chain that should be evaluated.
	 * @param right the right end of the congruence chain that should be evaluated.
	 */
	SubPath computePathNonRecursive(final CCParameter left, final CCParameter right) {
		final CCTerm leftTerm = left.getCCTerm();
		final CCTerm rightTerm = right.getCCTerm();
		/* check for and ignore trivial paths (the offsets coincide for a genuine congruence) */
		if (leftTerm == rightTerm) {
			return null;
		}

		final SymmetricPair<CCTerm> key = new SymmetricPair<>(leftTerm, rightTerm);
		if (mVisited.containsKey(key)) {
			return mVisited.get(key);
		}

		int leftDepth = computeDepth(leftTerm);
		int rightDepth = computeDepth(rightTerm);
		CCTerm ll = leftTerm;
		CCTerm rr = rightTerm;
		CCTerm llWithReason = ll, rrWithReason = rr;
		while (leftDepth > rightDepth) {
			if (ll.mOldRep.mReasonLiteral != null) {
				llWithReason = ll.mEqualEdge;
			}
			ll = ll.mEqualEdge;
			leftDepth--;
		}
		while (rightDepth > leftDepth) {
			if (rr.mOldRep.mReasonLiteral != null) {
				rrWithReason = rr.mEqualEdge;
			}
			rr = rr.mEqualEdge;
			rightDepth--;
		}
		while (ll != rr) {
			if (ll.mOldRep.mReasonLiteral != null) {
				llWithReason = ll.mEqualEdge;
			}
			if (rr.mOldRep.mReasonLiteral != null) {
				rrWithReason = rr.mEqualEdge;
			}
			ll = ll.mEqualEdge;
			rr = rr.mEqualEdge;
		}
		assert (ll != null);
		final SubPath path = computePathTo(left, llWithReason);
		if (llWithReason != rrWithReason) {
			computeCongruence((CCAppTerm)llWithReason, (CCAppTerm)rrWithReason);
			path.addEntry(rrWithReason, null);
		}
		final SubPath pathBack = computePathTo(right, rrWithReason);
		path.addSubPath(pathBack);
		mVisited.put(key, path);
		return path;
	}

	/**
	 * Compute the conflict set and interpolation information for the congruence path from term left to right. The
	 * interpolation info should be empty and its head/max/tailNr should be equal to the (last) formula number of the
	 * equality that precedes left in the conflict circle. The parameter tailNr should give the (last) formula number of
	 * the next equality after right. On return info.tailNr is equal to tailNr.
	 *
	 * @param mVisited
	 *            a set of equality pairs that were already visited. This is used to prevent double work.
	 * @param set
	 *            the set of literals in the conflict clause.
	 * @param info
	 *            the interpolation info containing head/tail interfaces, and collecting the equality chains.
	 * @param tailNr
	 *            this gives the (last) formula number of the equality after right.
	 * @param left
	 *            the left end of the congruence chain that should be evaluated.
	 * @param right
	 *            the right end of the congruence chain that should be evaluated.
	 */
	public void computePath(final CCParameter left, final CCParameter right) {
		// Only enqueue the path. The caller (a top-level compute*Cycle/Lemma method) calls drainTodo() once after all
		// computePath/computeCongruence calls are queued, so a single shared drain builds them all (and dedups subpaths
		// shared between several queued ends).
		mTodo.add(new SymmetricPair<>(left, right));
	}

	/**
	 * Process the work list {@link #mTodo} of (sub)paths to compute, building each one and collecting it into
	 * {@link #mAllPaths} (and its literals into {@link #mAllLiterals}). The top-level compute*Cycle/Lemma methods seed
	 * the work list via {@link #computePath} (a single pair) and {@link #computeCongruence} (argument pairs), then call
	 * this once. {@link WeakCongruencePath} consumes single paths synchronously and drains after each
	 * {@link #computePath}, hence protected.
	 */
	protected void drainTodo() {
		final HashSet<SymmetricPair<CCTerm>> added = new HashSet<>();
		while (!mTodo.isEmpty()) {
			final SymmetricPair<CCParameter> pathEnds = mTodo.removeFirst();

			// don't do anything for trivial paths
			if (pathEnds.getFirst().getCCTerm() == pathEnds.getSecond().getCCTerm()) {
				continue;
			}

			// check if we already visited this path (keyed offset-free, so offset variants share one subpath)
			final SubPath path = mVisited.get(offsetFreeKey(pathEnds));
			if (path == null) {
				// if we did not visit it yet, enqueue again for later and visit the path
				mTodo.addFirst(pathEnds);
				computePathNonRecursive(pathEnds.getFirst(), pathEnds.getSecond());
			} else {
				// already visited it, so we just add the path now unless we did this earlier
				if (added.add(offsetFreeKey(pathEnds))) {
					mAllPaths.addFirst(path);
				}
			}
		}
	}

	public Clause computeCycle(final CCEquality eq, final boolean produceProofs) {
		final CCTerm lhs = eq.getLhs();
		final CCTerm rhs = eq.getRhs();
		computePath(eq.getLhs(), eq.getRhs());
		drainTodo();
		final Literal[] cycle = new Literal[mAllLiterals.size() + 1];
		int i = 0;
		cycle[i++] = eq;
		for (final Literal l: mAllLiterals) {
			cycle[i++] = l.negate();
		}
		final Clause c = new Clause(cycle);
		if (produceProofs) {
			// The disequality being violated is eq, which states value(lhs) == value(rhs) + eq.getOffset(); carry that
			// offset on the main diseq so the proof matches the (offset-aware) literal eq instead of a bare lhs == rhs.
			final SymmetricPair<CCParameter> diseq = new SymmetricPair<>(lhs, CCParameter.of(rhs, eq.getOffset()));
			c.setProof(new LeafNode(LeafNode.THEORY_CC, createAnnotation(diseq)));
		}
		return c;
	}

	/**
	 * Build the clause {@code {¬eq, ¬path}} for an offset equality {@code eq} whose two sides are in the same congruence
	 * class at an offset different from the one {@code eq} claims. The path between the two sides establishes their
	 * actual (constant) offset, so {@code eq} is implied false. Used both as the conflict clause when such an
	 * {@code eq} is asserted true and as the reason when {@code ¬eq} is propagated at merge time. The path-edge literals
	 * are collected exactly as in {@link #computeCycle(CCEquality, boolean)}; only the polarity of {@code eq} differs
	 * (negated here instead of positive).
	 */
	public Clause computeAntiCycle(final CCEquality eq, final boolean produceProofs) {
		final CCTerm lhs = eq.getLhs();
		final CCTerm rhs = eq.getRhs();
		assert lhs.getRepresentative() == rhs.getRepresentative();
		computePath(lhs, rhs);
		drainTodo();
		final Literal[] clause = new Literal[mAllLiterals.size() + 1];
		int i = 0;
		clause[i++] = eq.negate();
		for (final Literal l : mAllLiterals) {
			clause[i++] = l.negate();
		}
		final Clause c = new Clause(clause);
		if (produceProofs) {
			// The path proves lhs = rhs + deltaPath (the actual union-find offset), but eq claims lhs = rhs + deltaEq
			// with deltaEq != deltaPath. We cannot express this as a single congruence: both conflicting values share the
			// CCTerm rhs (the offset was factored out), and a SubPath cannot carry the same CCTerm at two offsets. So we
			// build the trivially-false equality (rhs + deltaEq) = (rhs + deltaPath) and prove it via the trans path
			// [rhs+deltaEq, lhs, ..., rhs+deltaPath]: the first step rhs+deltaEq = lhs is justified by eq, the rest by the
			// path. The explicit leading node rhs+deltaEq carries deltaEq, which the path nodes cannot. The diseq is a
			// trivial offset disequality (constant difference deltaEq - deltaPath), discharged by an EQ lemma.
			final Rational deltaPath = lhs.mOffsetToRep.sub(rhs.mOffsetToRep);
			final Rational deltaEq = eq.getOffset();
			final CCParameter rhsAtEq = CCParameter.of(rhs, deltaEq);
			final CCParameter rhsAtPath = CCParameter.of(rhs, deltaPath);
			final SymmetricPair<CCParameter> diseq = new SymmetricPair<>(rhsAtEq, rhsAtPath);
			c.setProof(new LeafNode(LeafNode.THEORY_CC,
					new CCAnnotation(diseq, mAllPaths, CCAnnotation.RuleKind.CONG, rhsAtEq)));
		}
		return c;
	}

	/**
	 * Build the explanation clause {@code {diseq, ¬eq, ¬path}} for a disequality {@code ¬eq} that is propagated (or
	 * conflicts) because {@code eq}'s two sides are in <em>different</em> congruence classes, separated by the
	 * disequality {@code diseq}. The path runs {@code diseq.lhs … left -[eq]- right … diseq.rhs}, so it spans the two
	 * classes joined by the {@code eq} edge.
	 *
	 * <p>Unlike the old approach (temporarily insert {@code eq} as an equal-edge into the graph and run
	 * {@link #computeCycle(CCEquality, boolean)}), we do <em>not</em> mutate the graph: a path crossing the {@code eq}
	 * edge would have its offsets read from {@code mOffsetToRep}, which is relative to each node's own representative and
	 * meaningless across the two classes. Instead we compute the two halves as ordinary single-class paths (offset-correct
	 * on their own) and stitch them by hand, shifting the second half by {@code eq.getOffset()} so the proof object
	 * carries consistent offsets across the bridge.
	 */
	public Clause computeAntiCycleDiffClass(final CCEquality eq, final CCEquality diseq, final boolean produceProofs) {
		final CCTerm left = eq.getLhs();
		final CCTerm right = eq.getRhs();
		// Orient the separating disequality so dLeft is on left's side and dRight on right's side; dOff is the offset of
		// the forbidden equality in that orientation (diseq forbids dLeft == dRight + dOff). Use the orientation captured
		// when the reason was set (eq.mDiseqOrientation), not the current representatives: by the time this runs left and
		// right may have been merged, after which getRepresentative() can no longer tell the two sides apart.
		final CCTerm dLeft, dRight;
		final Rational dOff;
		if (eq.mDiseqOrientation) {
			dLeft = diseq.getLhs();
			dRight = diseq.getRhs();
			dOff = diseq.getOffset();
		} else {
			dLeft = diseq.getRhs();
			dRight = diseq.getLhs();
			dOff = diseq.getOffset().negate();
		}
		// Two single-class paths, accumulating their reason literals into mAllLiterals and their subpaths into mAllPaths.
		computePath(dLeft, left);
		computePath(right, dRight);
		drainTodo();
		final Literal[] clause = new Literal[mAllLiterals.size() + 2];
		int i = 0;
		clause[i++] = diseq;
		clause[i++] = eq.negate();
		for (final Literal l : mAllLiterals) {
			clause[i++] = l.negate();
		}
		final Clause c = new Clause(clause);
		if (produceProofs) {
			final SubPath segA = dLeft == left ? null : mVisited.get(new SymmetricPair<>(dLeft, left));
			final SubPath segB = right == dRight ? null : mVisited.get(new SymmetricPair<>(right, dRight));
			// paramsA = [dLeft@0, ..., left@offLeft] (anchored and oriented at dLeft). Shift the right half into the left
			// half's frame: after the eq edge (left == right + eq.getOffset()), right sits at left's offset plus
			// eq.getOffset(); rendering the right half anchored there yields it already shifted, so a plain concat.
			final CCParameter[] paramsA = segA != null ? segA.getParams(dLeft) : new CCParameter[] { dLeft };
			final CCParameter rightAnchor =
					CCParameter.of(right, paramsA[paramsA.length - 1].getOffset().add(eq.getOffset()));
			final CCParameter[] paramsB =
					segB != null ? segB.getParams(rightAnchor) : new CCParameter[] { rightAnchor };
			final CCParameter[] mainPath = new CCParameter[paramsA.length + paramsB.length];
			System.arraycopy(paramsA, 0, mainPath, 0, paramsA.length);
			System.arraycopy(paramsB, 0, mainPath, paramsA.length, paramsB.length);
			assert mainPath[mainPath.length - 1].getOffset().equals(dOff) : "net path offset must match the diseq offset";
			// The remaining subpaths (congruences within either half) keep deriving their offsets the usual way.
			final ArrayList<SubPath> otherPaths = new ArrayList<>();
			for (final SubPath p : mAllPaths) {
				if (p != segA && p != segB) {
					otherPaths.add(p);
				}
			}
			final SymmetricPair<CCParameter> diseqParam = new SymmetricPair<>(dLeft, CCParameter.of(dRight, dOff));
			c.setProof(new LeafNode(LeafNode.THEORY_CC,
					new CCAnnotation(diseqParam, mainPath, otherPaths, CCAnnotation.RuleKind.CONG)));
		}
		return c;
	}

	/**
	 * Build the conflict clause for a congruence merge whose two function applications {@code first} and {@code second}
	 * are already in the same congruence class at an offset different from the zero offset that congruence implies. The
	 * two terms have equal value by congruence (their arguments are pairwise equal), but the existing path between them
	 * in their common class establishes a non-zero constant offset {@code existingDiff}; the two facts are
	 * contradictory. The conflict clause negates the argument equalities (which justify the congruence) together with
	 * the path literals (which establish the conflicting offset) — no positive literal is needed, the contradiction is
	 * intrinsic to arithmetic ({@code 0 != existingDiff}).
	 *
	 * <p>For the proof object we mirror {@link #computeAntiCycle}: the leading congruence edge cannot be carried by a
	 * {@link SubPath} node (a SubPath cannot hold the same CCTerm at two offsets), so we build an explicit main path
	 * {@code [first@0, second@0, ..., first@existingDiff]} whose leading step {@code first@0 -> second@0} is recognised
	 * as a congruence (resolved from the argument subpaths in {@code otherPaths}) and whose remaining nodes are the
	 * existing class path. The two endpoints are the same term {@code first} at offsets {@code 0} and
	 * {@code existingDiff}, a trivially-false offset disequality discharged by an EQ lemma.
	 */
	public Clause computeCongruenceAntiCycle(final CCAppTerm first, final CCAppTerm second, final boolean produceProofs) {
		assert first.getRepresentative() == second.getRepresentative();
		final Rational existingDiff = second.mOffsetToRep.sub(first.mOffsetToRep);
		assert !existingDiff.equals(Rational.ZERO);
		assert first.getFunctionSymbol() == second.getFunctionSymbol();
		// The existing path between the two app terms (anchored at second@0 so getParams yields [second@0, ...,
		// first@existingDiff]); it establishes the actual (non-zero) offset.
		computePath(CCParameter.of(second, Rational.ZERO), CCParameter.of(first, Rational.ZERO));
		// The argument equalities that justify the congruence first == second (offset 0).
		computeCongruence(first, second);
		drainTodo();
		final Literal[] clause = new Literal[mAllLiterals.size()];
		int i = 0;
		for (final Literal l : mAllLiterals) {
			clause[i++] = l.negate();
		}
		final Clause c = new Clause(clause);
		if (produceProofs) {
			final SubPath existing = mVisited.get(new SymmetricPair<>(second, first));
			// anchored and oriented at second@0: [second@0, ..., first@existingDiff]
			final CCParameter[] existingParams = existing.getParams(CCParameter.of(second, Rational.ZERO));
			// main path: prepend first@0 (the congruence's other end) so the leading step first@0 -> second@0 is a
			// congruence edge and the two ends first@0 / first@existingDiff form the trivial diseq.
			final CCParameter[] mainPath = new CCParameter[existingParams.length + 1];
			mainPath[0] = CCParameter.of(first, Rational.ZERO);
			System.arraycopy(existingParams, 0, mainPath, 1, existingParams.length);
			final CCParameter firstAtDiff = mainPath[mainPath.length - 1];
			assert firstAtDiff.getCCTerm() == first && firstAtDiff.getOffset().equals(existingDiff);
			// The remaining subpaths (the congruence's argument paths plus any congruences along the existing path) keep
			// deriving their offsets the usual way; only the existing main path is inlined into mainPath.
			final ArrayList<SubPath> otherPaths = new ArrayList<>();
			for (final SubPath p : mAllPaths) {
				if (p != existing) {
					otherPaths.add(p);
				}
			}
			final SymmetricPair<CCParameter> diseqParam = new SymmetricPair<>(mainPath[0], firstAtDiff);
			c.setProof(new LeafNode(LeafNode.THEORY_CC,
					new CCAnnotation(diseqParam, mainPath, otherPaths, CCAnnotation.RuleKind.CONG)));
		}
		return c;
	}

	/**
	 * Build the conflict clause for a clash discovered <em>during</em> a merge of two classes that are joined only by the
	 * freshly added equal edge {@code lhs — rhsTerm} (the union-find is not yet updated, so {@code mOffsetToRep} is still
	 * relative to each node's <em>own</em> representative). The conflicting fact lives between an endpoint {@code srcEnd}
	 * in the source class (reachable from {@code lhs}) and an endpoint {@code destEnd} in the destination class (reachable
	 * from {@code rhsTerm}). Two cases:
	 * <ul>
	 * <li><b>Shared-term clash</b> ({@code diseqLit == null}): {@code srcEnd}/{@code destEnd} are the two classes' shared
	 * terms, whose merged values are provably distinct (e.g. an integer shared term forced to a non-integer value,
	 * {@code to_real a == 1/2}). The contradiction is intrinsic, discharged by an EQ/LA lemma; no positive literal.</li>
	 * <li><b>Disequality clash</b> ({@code diseqLit != null}): a registered disequality {@code diseqLit} between the two
	 * classes forbids exactly the offset at which the merge would unite {@code srcEnd} and {@code destEnd}. The clause
	 * carries {@code diseqLit} as its positive literal.</li>
	 * </ul>
	 *
	 * <p>As in {@link #computeAntiCycleDiffClass}, a single {@code computePath} across the bridge would read offsets from
	 * two different reference frames and produce a garbage proof object. Instead we compute the two halves as ordinary
	 * single-class paths ({@code srcEnd … lhs} and {@code rhsTerm … destEnd}, each offset-correct) and stitch them by
	 * hand, shifting the destination half by {@code bridgeOff} (= {@code value(lhs) − value(rhsTerm)} implied by the
	 * merge reason; {@code 0} for a congruence). The bridge edge itself is justified either by the merge {@code reason}
	 * (a real equality literal) or, for a congruence merge ({@code reason == null}), by the argument equalities — exactly
	 * as in {@link #computeCongruenceAntiCycle}, where the bridge step {@code lhs → rhsTerm} is auto-resolved from the
	 * argument subpaths.
	 */
	public Clause computeMergeConflictCycle(final CCTerm srcEnd, final CCTerm destEnd, final CCTerm lhs,
			final CCTerm rhsTerm, final CCEquality reason, final Rational bridgeOff, final CCEquality diseqLit,
			final boolean produceProofs) {
		// Two single-class paths, each offset-correct on its own.
		computePath(srcEnd, lhs);
		computePath(rhsTerm, destEnd);
		// Justify the bridge edge lhs — rhsTerm.
		if (reason != null) {
			mAllLiterals.add(reason);
		} else {
			// Congruence bridge: the argument equalities justify lhs == rhsTerm (and build the subpaths that the proof
			// generator uses to resolve the bridge step).
			computeCongruence((CCAppTerm) lhs, (CCAppTerm) rhsTerm);
		}
		drainTodo();
		final Literal[] clause = new Literal[mAllLiterals.size() + (diseqLit != null ? 1 : 0)];
		int i = 0;
		// The separating disequality (if any) is the cycle's only positive literal; the merge falsifies it.
		if (diseqLit != null) {
			clause[i++] = diseqLit;
		}
		for (final Literal l : mAllLiterals) {
			clause[i++] = l.negate();
		}
		final Clause c = new Clause(clause);
		if (produceProofs) {
			final SubPath segSrc = srcEnd == lhs ? null : mVisited.get(new SymmetricPair<>(srcEnd, lhs));
			final SubPath segDest = rhsTerm == destEnd ? null : mVisited.get(new SymmetricPair<>(rhsTerm, destEnd));
			// paramsSrc = [srcEnd@0, ..., lhs@offLhs] (anchored and oriented at srcEnd). Shift the destination half into
			// the source half's frame: after the bridge edge (value(lhs) == value(rhsTerm) + bridgeOff), rhsTerm sits at
			// lhs's offset plus bridgeOff; rendering the dest half anchored there yields it already shifted, so the main
			// path is a plain concatenation.
			final CCParameter[] paramsSrc = segSrc != null ? segSrc.getParams(srcEnd) : new CCParameter[] { srcEnd };
			final CCParameter destAnchor =
					CCParameter.of(rhsTerm, paramsSrc[paramsSrc.length - 1].getOffset().add(bridgeOff));
			final CCParameter[] paramsDest =
					segDest != null ? segDest.getParams(destAnchor) : new CCParameter[] { destAnchor };
			final CCParameter[] mainPath = new CCParameter[paramsSrc.length + paramsDest.length];
			System.arraycopy(paramsSrc, 0, mainPath, 0, paramsSrc.length);
			System.arraycopy(paramsDest, 0, mainPath, paramsSrc.length, paramsDest.length);
			// The remaining subpaths (congruences within either half, plus the bridge's argument subpaths) keep deriving
			// their offsets the usual way.
			assert mainPath[0].getCCTerm() == srcEnd : "main path must start at srcEnd";
			assert mainPath[mainPath.length - 1].getCCTerm() == destEnd : "main path must end at destEnd";
			final ArrayList<SubPath> otherPaths = new ArrayList<>();
			for (final SubPath p : mAllPaths) {
				if (p != segSrc && p != segDest) {
					otherPaths.add(p);
				}
			}
			// The clashing equality: a concrete disequality discharged against diseqLit, or (shared case) the trivially
			// distinct shared values discharged by an EQ/LA lemma.
			final SymmetricPair<CCParameter> diseq = new SymmetricPair<>(mainPath[0], mainPath[mainPath.length - 1]);
			c.setProof(new LeafNode(LeafNode.THEORY_CC,
					new CCAnnotation(diseq, mainPath, otherPaths, CCAnnotation.RuleKind.CONG)));
		}
		return c;
	}

	public Clause computeDTLemma(final CCEquality propagatedEq, final DataTypeLemma lemma,
			final boolean produceProofs) {
		for (final SymmetricPair<CCTerm> reason : lemma.getReason()) {
			computePath(reason.getFirst(), reason.getSecond());
		}
		drainTodo();

		final Literal[] negLits = new Literal[mAllLiterals.size() + (propagatedEq != null ? 1 : 0)];
		int i = 0;
		if (propagatedEq != null) {
			negLits[i++] = propagatedEq;
		}
		for (final Literal l : mAllLiterals) {
			negLits[i++] = l.negate();
		}
		final Clause c = new Clause(negLits);
		if (produceProofs) {
			// the main equality carries the offset of a numeric constructor field; CCAnnotation keeps both the
			// CCParameter view (with offset) and the offset-free CCTerm view used by the current proof generator.
			c.setProof(new LeafNode(LeafNode.THEORY_DT, new CCAnnotation(lemma.getMainEquality(), mAllPaths, lemma)));
		}
		return c;
	}

	/**
	 * Compute the earliest decide level at which the path between lhs and rhs exists. There must be a path, i.e.
	 * {@code lhs.getRepresentative() == rhs.getRepresentative()}.
	 *
	 * @param lhs
	 *            the start of the path
	 * @param rhs
	 *            the end of the path
	 * @return the earliest decide level.
	 */
	public int computeDecideLevel(final CCTerm lhs, final CCTerm rhs) {
		computePath(lhs, rhs);
		drainTodo();
		int depth = 0;
		for (final Literal l : mAllLiterals) {
			depth = Math.max(depth, l.getAtom().getDecideLevel());
		}
		return depth;
	}

	@Override
	public String toString() {
		final StringBuilder sb = new StringBuilder();
		sb.append("CongruencePath[");
		sb.append(mAllLiterals.toString());
		sb.append(']');
		return sb.toString();
	}
}
