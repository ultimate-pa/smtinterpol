/*
 * Copyright (C) 2009-2016 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.smtinterpol.interpolate;

import java.util.ArrayDeque;
import java.util.Arrays;
import java.util.BitSet;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.logic.AnnotatedTerm;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.logic.Theory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.interpolate.Interpolator.LitInfo;
import de.uni_freiburg.informatik.ultimate.smtinterpol.interpolate.Interpolator.Occurrence;
import de.uni_freiburg.informatik.ultimate.smtinterpol.interpolate.InterpolatorClauseTermInfo.ProofPath;
import de.uni_freiburg.informatik.ultimate.smtinterpol.util.SymmetricPair;

/**
 * The interpolator for congruence-closure theory lemmata.
 *
 * @author Jochen Hoenicke, Tanja Schindler
 */
public class CCInterpolator {

	Interpolator mInterpolator;

	HashMap<SymmetricPair<Term>, AnnotatedTerm> mEqualities;

	Theory mTheory;
	int mNumInterpolants;

	Set<Term>[] mInterpolants;

	/**
	 * Compute the parent partition. This is the next partition, whose subtree includes color.
	 */
	private int getParent(final int color) {
		int parent = color + 1;
		while (mInterpolator.mStartOfSubtrees[parent] > color) {
			parent++;
		}
		return parent;
	}

	/**
	 * Compute the A-local child partition. This is the child, that is A-local to the occurrence. This function returns
	 * -1 if all children are in B.
	 */
	private int getChild(final int color, final Occurrence occur) {
		/* find A-local child of m_Color */
		int child = color - 1;
		while (child >= mInterpolator.mStartOfSubtrees[color]) {
			if (occur.isALocal(child)) {
				return child;
			}
			child = mInterpolator.mStartOfSubtrees[child] - 1;
		}
		return -1;
	}

	class PathInfo {
		Term[] mPath;

		/**
		 * The set of partitions for which there is an AB-shared path from start to end.
		 */
		BitSet mHasABPath;

		/**
		 * The first partition for which the path from start to end is A-local. This is m_numInterpolants, if there is
		 * no such partition. If m_hasABPath is not empty, this value is undefined; we set it to the root of the
		 * m_hasABPath tree, which equals the two mColor of the head and tail node.
		 */
		int mMaxColor;
		PathEnd mHead, mTail;

		/*
		 * max color is the maximum of all firstColor of all literals on the path.
		 *
		 * Head color is the lastColor of the first literal before the first path change. If head color >= max color,
		 * then there is no path change.
		 *
		 */

		class PathEnd {
			/**
			 * The first partition for which there is an A-local prefix of the path. If m_hasABPath is non-empty, this
			 * is the first partition that is not in m_hasABPath, i.e. the first for which only a continuous A-path but
			 * not a continuous B-path exists.
			 */
			int mColor;
			/**
			 * For each partition on the path from m_Color to m_MaxColor this gives the term that ends the first A-local
			 * chain of equalities.
			 */
			Term[] mTerm;

			@SuppressWarnings("unchecked")
			public PathEnd() {
				mColor = mNumInterpolants;
				mTerm = new Term[mNumInterpolants];
			}

			/**
			 * Close the A path for partition color. This is called when we add a term to the chain that is B-local for
			 * the current mColor. We set mColor to the parent node. We also close the open path on mColor or open a new
			 * one and increment mMaxColor if such a path was not yet open.
			 *
			 * @param other
			 *            the other PathEnd
			 * @param boundaryTerm
			 *            the boundary term for opening/closing the path.
			 */
			public void closeSingleAPath(final PathEnd other, final Term boundaryTerm) {
				// this should be empty now, since we anded it with
				// occur.mInA and the occurrence is not in A for color.
				assert mHasABPath.isEmpty();
				final int color = mColor;
				mColor = getParent(color);
				if (color < mMaxColor) {
					addInterpolantClause(color, mTheory.term("=", boundaryTerm, mTerm[color]));
					mTerm[color] = null;
				} else {
					assert (mMaxColor == color);
					other.mTerm[color] = boundaryTerm;
					mMaxColor = getParent(color);
				}
			}

			/**
			 * Open a new A path. This is called when a term is added that is A local in child, where child is a child
			 * of mColor. We start a new A path on child. If we have still slack, since mHasABPath contains child, we
			 * don't have to open the path and just set mMaxColor to child.
			 *
			 * @param other
			 *            the other path end.
			 * @param boundaryTerm
			 *            the term that starts the new A path.
			 * @param child
			 *            the child of mColor for which the added term is A local.
			 */
			public void openSingleAPath(final PathEnd other, final Term boundaryTerm, final int child) {
				if (mHasABPath.get(child)) {
					mMaxColor = other.mColor = mColor = child;
					// compute all nodes below child excluding child itself
					final BitSet subtree = new BitSet();
					subtree.set(mInterpolator.mStartOfSubtrees[child], child);
					// keep only those below the current child.
					mHasABPath.and(subtree);
				} else {
					/* open a new A-path. */
					mTerm[child] = boundaryTerm;
					mColor = child;
				}
			}

			public void closeAPath(final PathEnd other, final Term boundaryTerm, final Occurrence occur) {
				assert (other.mColor <= mMaxColor);
				mHasABPath.and(occur.mInA);
				while (mColor < mNumInterpolants && occur.isBLocal(mColor)) {
					closeSingleAPath(other, boundaryTerm);
				}
			}

			public void closeAPathMixed(final PathEnd other, final Occurrence mixedLhsOccur,
					final TermVariable mixedVar, final Occurrence occur) {
				assert (other.mColor <= mMaxColor);
				mHasABPath.and(occur.mInA);
				while (mColor < mNumInterpolants && occur.isBLocal(mColor)) {
					// this should be empty now, since we anded it with
					// occur.mInA and the occurrence is not in A for color.
					assert mHasABPath.isEmpty();
					final int color = mColor;
					mColor = getParent(color);
					assert color < mMaxColor;
					addInterpolantClause(color, mTheory.term(Interpolator.EQ, mixedVar, mTerm[color]));
					mTerm[color] = null;
				}
			}

			public void openAPath(final PathEnd other, final Term boundaryTerm, final Occurrence occur) {
				while (true) {
					final int child = getChild(mColor, occur);
					/* if there is no A-local child, we are done. */
					if (child < 0) {
						break;
					}
					assert occur.isALocal(child);
					openSingleAPath(other, boundaryTerm, child);
				}
			}

			public Term getBoundTerm(final int color) {
				if (color < mColor) {
					final Term first = this == mHead ? mPath[0] : mPath[mPath.length - 1];
					return first;
				} else if (color < mMaxColor) {
					return mTerm[color];
				} else {
					final Term last = this == mTail ? mPath[0] : mPath[mPath.length - 1];
					return last;
				}
			}

			@Override
			public String toString() {
				final StringBuilder sb = new StringBuilder();
				String comma = "";
				sb.append(mColor).append(":[");
				for (int i = mColor; i < mMaxColor; i++) {
					sb.append(comma);
					sb.append(mTerm[i]);
					comma = ",";
				}
				sb.append(']');
				return sb.toString();
			}
		}

		/*
		 * invariants: HeadTerm[p] != null exactly for p in [m_HeadColor, m_MaxColor-1] HeadPre[p] != null only for p in
		 * [m_HeadColor, numInterpolants] HeadColor is in between first and last color of head term. likewise for Tail.
		 * MaxColor is maximum of all first of all terms and literals involved in current path (but there may be bigger
		 * literals in congruence paths that were added to headPre/tailPre).
		 *
		 * The partial interpolant of the current path is m_Interpolants && HeadPre ==> Lits[0] == m_HeadTerm && TailPre
		 * ==> m_TailTerm == lits[n] where HeadTerm = Lits[0] for partitions < HeadColor and TailTerm = Lits[n] for
		 * partitions < TailColor.
		 *
		 * For partitions >= maxColor, everything so far was in A, so the partial interpolant of the current path is
		 * m_Interpolants && TailPre ==> Lits[0] == lits[n]
		 */

		public PathInfo(final Term[] path) {
			mPath = path;
			mHasABPath = new BitSet(mNumInterpolants);
			mHasABPath.set(0, mNumInterpolants);
			mMaxColor = mNumInterpolants;
		}

		public void interpolatePathInfo() {
			final Occurrence headOccur = mInterpolator.getOccurrence(mPath[0]);

			mHead = new PathEnd();
			mTail = new PathEnd();
			mTail.closeAPath(mHead, null, headOccur);
			mTail.openAPath(mHead, null, headOccur);

			for (int i = 0; i < mPath.length - 1; i++) {
				final Term left = mPath[i];
				final Term right = mPath[i + 1];
				final AnnotatedTerm lit = mEqualities.get(new SymmetricPair<>(left, right));
				final LitInfo info = mInterpolator.getLiteralInfo(lit);
				Term boundaryTerm;
				boundaryTerm = mPath[i];
				if (info.getMixedVar() == null) {
					mTail.closeAPath(mHead, boundaryTerm, info);
					mTail.openAPath(mHead, boundaryTerm, info);
				} else {
					mTail.closeAPath(mHead, boundaryTerm, info);
					mTail.openAPath(mHead, boundaryTerm, info);
					final Occurrence occ = mInterpolator.getOccurrence(mPath[i + 1]);
					boundaryTerm = info.getMixedVar();
					mTail.closeAPath(mHead, boundaryTerm, occ);
					mTail.openAPath(mHead, boundaryTerm, occ);
				}
			}
		}

		/**
		 * Build an interpolant clause and add it to the interpolant set.
		 *
		 * @param pre
		 *            The disequalities summarizing the requirements from the B-part in skipped argument paths.
		 * @param lhsTerm
		 *            The end of the A-equality chain.
		 * @param rhsTerm
		 *            The start of the A-equality chain.
		 * @param isNegated
		 *            True, if there is a disequality in the chain.
		 */
		private void addInterpolantClause(final int color, final Term clause) {
			mInterpolants[color].add(clause);
		}

		@Override
		public String toString() {

			return "PathInfo[" + Arrays.toString(mPath) + "," + mHead + ',' + mTail + "," + mMaxColor + "]";

		}

		public void addDiseq(final AnnotatedTerm diseq) {
			final LitInfo info = mInterpolator.getLiteralInfo(diseq);
			Term boundaryTailTerm, boundaryHeadTerm;
			boundaryHeadTerm = mPath[0];
			boundaryTailTerm = mPath[mPath.length - 1];
			if (info.getMixedVar() == null) {
				mTail.closeAPath(mHead, boundaryTailTerm, info);
				mTail.openAPath(mHead, boundaryTailTerm, info);
				mHead.closeAPath(mTail, boundaryHeadTerm, info);
				mHead.openAPath(mTail, boundaryHeadTerm, info);
			} else {
				final Occurrence occHead = mInterpolator.getOccurrence(mPath[0]);
				mHead.closeAPath(mTail, boundaryHeadTerm, info);
				mHead.openAPath(mTail, boundaryHeadTerm, info);
				final Occurrence occTail = mInterpolator.getOccurrence(mPath[mPath.length - 1]);
				mTail.closeAPath(mHead, boundaryTailTerm, info);
				mTail.openAPath(mHead, boundaryTailTerm, info);

				mHead.closeAPathMixed(mTail, info.getLhsOccur(), info.getMixedVar(), occTail);
				mTail.closeAPathMixed(mHead, info.getLhsOccur(), info.getMixedVar(), occHead);
			}
		}

		public void close() {
			while (mHead.mColor < mNumInterpolants || mTail.mColor < mNumInterpolants) {
				if (mHead.mColor < mTail.mColor) {
					addInterpolantClause(mHead.mColor,
							mTheory.term("=", mHead.getBoundTerm(mHead.mColor), mTail.getBoundTerm(mMaxColor)));
					mHead.mColor = getParent(mHead.mColor);
				} else if (mHead.mColor == mTail.mColor) {
					if (mHead.mColor < mMaxColor) {
						addInterpolantClause(mHead.mColor, mTheory.not(
								mTheory.term("=", mHead.getBoundTerm(mHead.mColor), mTail.getBoundTerm(mHead.mColor))));
					} else {
						addInterpolantClause(mHead.mColor, mTheory.mFalse);
					}
					mHead.mColor = mTail.mColor = getParent(mHead.mColor);
				} else {
					addInterpolantClause(mTail.mColor,
							mTheory.term("=", mHead.getBoundTerm(mMaxColor), mTail.getBoundTerm(mTail.mColor)));
					mTail.mColor = getParent(mTail.mColor);
				}
			}
		}
	}

	@SuppressWarnings("unchecked")
	public CCInterpolator(final Interpolator ipolator) {
		mInterpolator = ipolator;
		mNumInterpolants = ipolator.mNumInterpolants;
		mTheory = ipolator.mTheory;
		mInterpolants = new Set[mNumInterpolants];
		for (int i = 0; i < mNumInterpolants; i++) {
			mInterpolants[i] = new HashSet<>();
		}
	}

	/**
	 * Compute the interpolants for a congruence lemma.
	 *
	 * @param diseq
	 *            The goal equality from the lemma between the function applications.
	 * @param left
	 *            The left application term.
	 * @param right
	 *            The right application term.
	 * @return The array of interpolants.
	 */
	private Term[] interpolateCongruence(final AnnotatedTerm diseq, final ApplicationTerm left,
			final ApplicationTerm right) {
		final LitInfo info = mInterpolator.getLiteralInfo(diseq);
		final Term[] interpolants = new Term[mNumInterpolants];
		final Term[] leftParams = left.getParameters();
		final Term[] rightParams = right.getParameters();
		final LitInfo[] paramInfos = new LitInfo[leftParams.length];
		assert left.getFunction() == right.getFunction() && leftParams.length == rightParams.length;
		for (int i = 0; i < leftParams.length; i++) {
			if (leftParams[i] == rightParams[i]) {
				paramInfos[i] = null;
			} else {
				final AnnotatedTerm eq = mEqualities.get(new SymmetricPair<>(leftParams[i], rightParams[i]));
				paramInfos[i] = mInterpolator.getLiteralInfo(eq);
			}
		}

		for (int part = 0; part < mNumInterpolants; part++) {
			if (info.isBorShared(part)) {
				// collect A-local literals
				final ArrayDeque<Term> terms = new ArrayDeque<>(leftParams.length);
				for (int paramNr = 0; paramNr < leftParams.length; paramNr++) {
					if (paramInfos[paramNr] != null && paramInfos[paramNr].isALocal(part)) {
						terms.add(mTheory.term("=", leftParams[paramNr], rightParams[paramNr]));
					}
				}
				interpolants[part] = mTheory.and(terms.toArray(new Term[terms.size()]));
			} else if (info.isALocal(part)) {
				// collect negated B-local literals
				final ArrayDeque<Term> terms = new ArrayDeque<>(leftParams.length);
				for (int paramNr = 0; paramNr < leftParams.length; paramNr++) {
					if (paramInfos[paramNr] != null && paramInfos[paramNr].isBLocal(part)) {
						terms.add(mTheory.not(mTheory.term("=", leftParams[paramNr], rightParams[paramNr])));
					}
				}
				interpolants[part] = mTheory.or(terms.toArray(new Term[terms.size()]));
			} else {
				// the congruence is mixed.  In this case f must be shared and we need to find boundary
				// terms for every parameter.
				final Term[] boundaryTerms = new Term[leftParams.length];
				for (int paramNr = 0; paramNr < leftParams.length; paramNr++) {
					if (paramInfos[paramNr] == null) {
						// term occurs left and right, so this is obviously shared
						boundaryTerms[paramNr] = leftParams[paramNr];
					} else if (paramInfos[paramNr].isMixed(part)) {
						// mixed case: take mixed var
						boundaryTerms[paramNr] = paramInfos[paramNr].getMixedVar();
					} else if (mInterpolator.getOccurrence(leftParams[paramNr]).isAB(part)) {
						// the left term is shared, use it
						boundaryTerms[paramNr] = leftParams[paramNr];
					} else {
						// if it is not the left, the right must be shared, as the literal is not mixed.
						assert mInterpolator.getOccurrence(rightParams[paramNr]).isAB(part);
						boundaryTerms[paramNr] = rightParams[paramNr];
					}
				}
				final Term sharedTerm = mTheory.term(left.getFunction(), boundaryTerms);
				interpolants[part] = mTheory.term(Interpolator.EQ, info.getMixedVar(), sharedTerm);
			}
		}
		return interpolants;
	}

	public Term[] computeInterpolants(final Term proofTerm) {
		mEqualities = new HashMap<>();
		final InterpolatorClauseTermInfo proofTermInfo = mInterpolator.getClauseTermInfo(proofTerm);
		for (final Term literal : proofTermInfo.getLiterals()) {
			final InterpolatorLiteralTermInfo litTermInfo = mInterpolator.getLiteralTermInfo(literal);
			if (litTermInfo.isNegated()) {
				assert litTermInfo.getAtom() instanceof AnnotatedTerm;
				final ApplicationTerm eq = litTermInfo.getEquality();
				mEqualities.put(new SymmetricPair<>(eq.getParameters()[0], eq.getParameters()[1]),
						(AnnotatedTerm) litTermInfo.getAtom());
			}
		}

		final ProofPath[] paths = proofTermInfo.getPaths();
		assert (paths.length == 1 && paths[0].getIndex() == null);
		final Term[] path = paths[0].getPath();
		final AnnotatedTerm diseq = (AnnotatedTerm) proofTermInfo.getDiseq();
		if (path.length == 2) {
			return interpolateCongruence(diseq, (ApplicationTerm) path[0], (ApplicationTerm) path[1]);
		}

		// Transitivity lemma
		final PathInfo mainPath = new PathInfo(path);
		mainPath.interpolatePathInfo();
		if (diseq != null) {
			mainPath.addDiseq(diseq);
		}
		mainPath.close();
		final Term[] interpolants = new Term[mNumInterpolants];
		for (int i = 0; i < mNumInterpolants; i++) {
			interpolants[i] = mTheory.and(mInterpolants[i].toArray(new Term[mInterpolants[i].size()]));
		}
		return interpolants;
	}

	@Override
	public String toString() {
		return Arrays.toString(mInterpolants);
	}
}
