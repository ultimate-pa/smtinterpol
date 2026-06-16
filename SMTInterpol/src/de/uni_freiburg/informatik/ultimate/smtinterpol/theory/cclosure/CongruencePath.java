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
		/** The anchor (first node) of the path and its offset; the offset of every other node is derived from it. */
		final CCTerm mStart;
		final Rational mStartOffset;

		public SubPath(final CCParameter start) {
			this(start, true);
		}

		public SubPath(final CCParameter start, final boolean produceProofs) {
			mStart = start.getCCTerm();
			mStartOffset = start.getOffset();
			if (produceProofs) {
				mTermsOnPath = new ArrayList<>();
				mTermsOnPath.add(mStart);
			}
		}

		/** The offset-free terms on the path. */
		public CCTerm[] getTerms() {
			return mTermsOnPath.toArray(new CCTerm[mTermsOnPath.size()]);
		}

		/**
		 * The path nodes as {@link CCParameter}s. All nodes are in one congruence class, and the offsets are chosen so
		 * that every node has the same value as the anchor (the first node): {@code value(node) + offset == value(start)
		 * + startOffset}. So if {@code x = y+4} and {@code y = z+2}, a path anchored at {@code x+2} reads
		 * {@code x+2, y+6, z+8}. The relative offsets are intrinsic ({@code mOffsetToRep} differences), so this is stable
		 * under {@link #addSubPath} concatenation regardless of the appended pieces' own anchors.
		 */
		public CCParameter[] getParams() {
			final CCParameter[] params = new CCParameter[mTermsOnPath.size()];
			for (int i = 0; i < params.length; i++) {
				final CCTerm t = mTermsOnPath.get(i);
				final Rational off = mStartOffset.add(mStart.mOffsetToRep).sub(t.mOffsetToRep);
				params[i] = CCParameter.of(t, off);
			}
			return params;
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

	final HashMap<SymmetricPair<CCParameter>,SubPath> mVisited;
	final ArrayDeque<SubPath> mAllPaths;
	final ArrayDeque<SymmetricPair<CCParameter>> mTodo;
	final Set<Literal> mAllLiterals;

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
	private void computeCCPath(CCAppTerm start, CCAppTerm end) {
		// Pair the argument values (CCParameters), so the recorded subpath for each argument is anchored at the
		// argument's offset, e.g. f(x+2) congruent f(z+8) yields a subpath from x+2 to z+8.
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
					computeCCPath((CCAppTerm) startCongruence, (CCAppTerm) t);
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

		final SymmetricPair<CCParameter> key = new SymmetricPair<>(left, right);
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
			computeCCPath((CCAppTerm)llWithReason, (CCAppTerm)rrWithReason);
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
		final HashSet<SymmetricPair<CCParameter>> added = new HashSet<>();
		mTodo.add(new SymmetricPair<>(left, right));
		while (!mTodo.isEmpty()) {
			final SymmetricPair<CCParameter> pathEnds = mTodo.removeFirst();

			// don't do anything for trivial paths
			if (pathEnds.getFirst().getCCTerm() == pathEnds.getSecond().getCCTerm()) {
				continue;
			}

			// check if we already visited this path
			final SubPath path = mVisited.get(pathEnds);
			if (path == null) {
				// if we did not visit it yet, enqueue again for later and visit the path
				mTodo.addFirst(pathEnds);
				computePathNonRecursive(pathEnds.getFirst(), pathEnds.getSecond());
			} else {
				// already visited it, so we just add the path now unless we did this earlier
				if (added.add(pathEnds)) {
					mAllPaths.addFirst(path);
				}
			}
		}
	}

	public Clause computeCycle(final CCEquality eq, final boolean produceProofs) {
		final CCTerm lhs = eq.getLhs();
		final CCTerm rhs = eq.getRhs();
		computePath(eq.getLhs(), eq.getRhs());
		final Literal[] cycle = new Literal[mAllLiterals.size() + 1];
		int i = 0;
		cycle[i++] = eq;
		for (final Literal l: mAllLiterals) {
			cycle[i++] = l.negate();
		}
		final Clause c = new Clause(cycle);
		if (produceProofs) {
			c.setProof(new LeafNode(LeafNode.THEORY_CC, createAnnotation(new SymmetricPair<>(lhs, rhs))));
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
		final Literal[] clause = new Literal[mAllLiterals.size() + 1];
		int i = 0;
		clause[i++] = eq.negate();
		for (final Literal l : mAllLiterals) {
			clause[i++] = l.negate();
		}
		final Clause c = new Clause(clause);
		if (produceProofs) {
			c.setProof(new LeafNode(LeafNode.THEORY_CC, createAnnotation(new SymmetricPair<>(lhs, rhs))));
		}
		return c;
	}

	public Clause computeCycle(final CCTerm lconstant, final CCTerm rconstant, final boolean produceProofs) {
		mClosure.getLogger().debug("computeCycle for Constants");
		computePath(lconstant, rconstant);
		final Literal[] cycle = new Literal[mAllLiterals.size()];
		int i = 0;
		for (final Literal l: mAllLiterals) {
			cycle[i++] = l.negate();
		}
		final Clause c = new Clause(cycle);
		if (produceProofs) {
			c.setProof(new LeafNode(
					LeafNode.THEORY_CC, createAnnotation(new SymmetricPair<>(lconstant, rconstant))));
		}
		return c;
	}

	public Clause computeDTLemma(final CCEquality propagatedEq, final DataTypeLemma lemma,
			final boolean produceProofs) {
		for (final SymmetricPair<CCTerm> reason : lemma.getReason()) {
			computePath(reason.getFirst(), reason.getSecond());
		}

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
