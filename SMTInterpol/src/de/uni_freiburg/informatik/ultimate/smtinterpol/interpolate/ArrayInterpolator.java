/*
 * Copyright (C) 2016-2017 University of Freiburg
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

import java.util.BitSet;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.logic.Theory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.interpolate.Interpolator.LitInfo;
import de.uni_freiburg.informatik.ultimate.smtinterpol.interpolate.Interpolator.Occurrence;
import de.uni_freiburg.informatik.ultimate.smtinterpol.interpolate.InterpolatorClauseTermInfo.ProofPath;
import de.uni_freiburg.informatik.ultimate.smtinterpol.util.SymmetricPair;

/**
 * The interpolator for the theory of arrays. At the moment, it can deal with read-over-weakeq lemmas only;
 * extensionality is not yet supported.
 * 
 * @author Tanja Schindler, Jochen Hoenicke
 */
public class ArrayInterpolator {

	/* General info to set up the ArrayInterpolator */
	private final Interpolator mInterpolator;
	private final Theory mTheory;
	private final int mNumInterpolants;
	/**
	 * The conjuncts or disjuncts that build the interpolants.
	 */
	private Set<Term>[] mInterpolants;

	/* Information for array lemmas */
	/**
	 * Information about the lemma proof term.
	 */
	private InterpolatorClauseTermInfo mLemmaInfo;
	/**
	 * The main disequality of this lemma. It is of the form "a[i]!=b[j]" for read-over-weakeq lemmas, and of the form
	 * "a!=b" for weakeq-ext lemmas.
	 */
	private ApplicationTerm mDiseq;
	/**
	 * The LitInfo for the main disequality of this lemma.
	 */
	private LitInfo mDiseqInfo;
	/**
	 * The atoms of the equality literals in the lemma that is interpolated. Note that they appear negated in the lemma
	 * clause.
	 */
	private Map<SymmetricPair<Term>, ApplicationTerm> mEqualities;
	/**
	 * The atoms of the disequality literals in the lemma that is interpolated. Note that they appear positively in the
	 * lemma clause.
	 */
	private Map<SymmetricPair<Term>, ApplicationTerm> mDisequalities;

	/* Specific information for read-over-weakeq-lemmas */
	/**
	 * The strong path between the select indices of the main disequality.
	 */
	private ApplicationTerm mIndexEquality;
	/**
	 * The store path between the arrays of the main disequality for weak equivalence modulo i, where i is the path
	 * index.
	 */
	private ProofPath mStorePath;
	/**
	 * This contains the shared select index for all partitions where it exists.
	 */
	private Term[] mSharedIndex;

	@SuppressWarnings("unchecked")
	public ArrayInterpolator(Interpolator ipolator) {
		mInterpolator = ipolator;
		mNumInterpolants = ipolator.mNumInterpolants;
		mTheory = ipolator.mTheory;
		mInterpolants = new Set[mNumInterpolants];
		for (int i = 0; i < mNumInterpolants; i++) {
			mInterpolants[i] = new HashSet<Term>();
		}
	}

	/**
	 * Compute interpolants for array lemmas. At the moment, this covers only read-over-weakeq lemmas.
	 * 
	 * @param proofTerm
	 *            The lemma that is interpolated
	 * @return An array containing interpolants for the different partitions
	 */
	public Term[] computeInterpolants(Term proofTerm) {
		mLemmaInfo = mInterpolator.getClauseTermInfo(proofTerm);

		// At the moment, we only support read-over-weakeq lemmas
		assert mLemmaInfo.getLemmaType().equals(":read-over-weakeq");

		mDiseq = (ApplicationTerm) mLemmaInfo.getDiseq();
		mDiseqInfo = mInterpolator.getLiteralInfo(mDiseq);
		mEqualities = new HashMap<SymmetricPair<Term>, ApplicationTerm>();
		mDisequalities = new HashMap<SymmetricPair<Term>, ApplicationTerm>();
		for (final Term literal : mLemmaInfo.getLiterals()) {
			final InterpolatorLiteralTermInfo litTermInfo = mInterpolator.getLiteralTermInfo(literal);
			if (litTermInfo.isNegated()) {
				final ApplicationTerm eq = (ApplicationTerm) litTermInfo.getAtom();
				mEqualities.put(new SymmetricPair<Term>(eq.getParameters()[0], eq.getParameters()[1]), eq);
			} else {
				final ApplicationTerm diseq = (ApplicationTerm) litTermInfo.getAtom();
				mDisequalities.put(new SymmetricPair<Term>(diseq.getParameters()[0], diseq.getParameters()[1]), diseq);
			}
		}

		Term[] interpolants = new Term[mNumInterpolants];
		interpolants = computeReadOverWeakeqInterpolants(proofTerm);
		return interpolants;
	}

	/**
	 * Compute interpolants for a read-over-weakeq lemma. The lemma consists of a disequality of form "a[i] != b[j]", a
	 * (strong) path of length 2 for the index equality "i = j" unless the disequality is of form "a[i] != b[i]", and a
	 * weak path from array "a" to array "b" consisting of equality or store steps with store operations only at indices
	 * different from the weakpath index, which is one of the select indices. We distinguish four cases for
	 * interpolation: either (i) there is a shared index term and the main diseq is in B or mixed -> terms of the form
	 * "s1[x]=s2[x]" for A-paths; or (ii) there is a shared index term and the main diseq is A local -> terms of the
	 * form "s1[x]!=s2[x]" for B paths; or (iii) both i,j are B-local -> terms of the form "weq(s1,s2,k,F(·))" are built
	 * for A paths; or (iv) both i,j are A-local -> terms of the form "nweq(s1,s2,k,F(·))" are built for B paths.
	 * 
	 * @param proofTerm
	 *            The lemma which interpolants are calculated for.
	 * @return An array containing the interpolants for all partitions.
	 */
	private Term[] computeReadOverWeakeqInterpolants(Term proofTerm) {
		final ProofPath[] paths = mLemmaInfo.getPaths();
		assert paths.length <= 2;
		if (paths.length == 2) {
			final Term[] indexPath;
			if (paths[0].getIndex() == null) {
				indexPath = paths[0].getPath();
				mStorePath = paths[1];
			} else {
				indexPath = paths[1].getPath();
				mStorePath = paths[0];
			}
			assert indexPath.length == 2;
			mIndexEquality = mEqualities.get(new SymmetricPair<Term>(indexPath[0], indexPath[1]));
		} else { // In this case, the main disequality is of form "a[i] != b[i]"
			assert paths.length == 1;
			mStorePath = paths[0];
		}
		WeakPathInfo arrayPath = new WeakPathInfo(mStorePath);

		// Determine the shared select index for all partitions where it exists
		computeSharedSelectIndices();
		// Calculate the interpolant terms from the store path
		arrayPath.interpolateWeakPathInfo();
		// In some cases, the index equality has to be added
		if (mIndexEquality != null) {
			addIndexEquality();
		}
		// Build the interpolants for all partitions.
		final Term[] interpolants = new Term[mNumInterpolants];
		for (int color = 0; color < mNumInterpolants; color++) {
			if (mDiseqInfo.isALocal(color)) { // the interpolant is the disjunction of all path interpolants
				interpolants[color] = mTheory.or(mInterpolants[color].toArray(new Term[mInterpolants[color].size()]));
			} else { // the interpolant is the conjunction of all path interpolants
				interpolants[color] = mTheory.and(mInterpolants[color].toArray(new Term[mInterpolants[color].size()]));
			}
		}
		return interpolants;
	}

	/**
	 * Determine for all partitions whether there exists a shared select index. This can be the weakpathindex, if no
	 * index equality exists; the mixed variable, if the index equality is mixed; the weakpathindex, if the index
	 * equality is local or shared; the other select index, if the index equality is A- or B-local, and weakpathindex is
	 * not shared. Note: if both select indices are shared, take weakpathindex. This information is used during
	 * interpolation to determine the partitions where a "simple" interpolant can be built.
	 */
	private void computeSharedSelectIndices() {
		mSharedIndex = new Term[mNumInterpolants];
		// If the main disequality is of form "a[i] != b[i]", there is no path for the index equality
		if (mIndexEquality == null) {
			// Check if the weakpath index is shared
			Term index = mStorePath.getIndex();
			for (int color = 0; color < mNumInterpolants; color++) {
				if (mInterpolator.getOccurrence(index, null).isAB(color)) {
					mSharedIndex[color] = index;
				}
			}
		} else {
			for (int color = 0; color < mNumInterpolants; color++) {
				// Check if the weakpath index is shared
				if (mInterpolator.getOccurrence(mStorePath.getIndex(), null).isAB(color)) {
					mSharedIndex[color] = mStorePath.getIndex();
				} else {
					LitInfo info = mInterpolator.getLiteralInfo(mIndexEquality);
					// Check if there is a mixed variable
					if (info.isMixed(color)) {
						mSharedIndex[color] = info.getMixedVar();
					} else { // Check the other select index
						assert info.isALocal(color) || info.isBLocal(color);
						Term otherIndex = ((ApplicationTerm) mIndexEquality).getParameters()[0];
						otherIndex = otherIndex == mStorePath.getIndex()
								? ((ApplicationTerm) mIndexEquality).getParameters()[1]
								: otherIndex;
						if (mInterpolator.getOccurrence(otherIndex, null).isAB(color)) {
							mSharedIndex[color] = otherIndex;
						}
					}
				}
			}
		}
	}

	/**
	 * For read-over-weakeq, the index equality has to be added to the interpolant if both indices are shared and either
	 * a) it is A-local and the main diseq is mixed or in B, or b) it is B-local and the main diseq is A-local.
	 */
	private void addIndexEquality() {
		final LitInfo indexEqInfo = mInterpolator.getLiteralInfo(mIndexEquality);
		final Term otherSelect = // not the select with the store path index
				getIndexFromSelect((ApplicationTerm) mDiseq.getParameters()[0]).equals(mStorePath.getIndex())
						? mDiseq.getParameters()[1]
						: mDiseq.getParameters()[0];
		final Occurrence otherSelectOccur = mInterpolator.getOccurrence(otherSelect, null);
		for (int color = 0; color < mNumInterpolants; color++) {
			if (mSharedIndex[color] != null && mSharedIndex[color] == mStorePath.getIndex()) {
				if (mDiseqInfo.isALocal(color) && indexEqInfo.isBLocal(color)) {
					mInterpolants[color].add(mTheory.not(mIndexEquality));
				} else if (indexEqInfo.isALocal(color) && otherSelectOccur.isBorShared(color)) {
					mInterpolants[color].add(mIndexEquality);
				}
			}
		}
	}

	/* Methods for tree interpolation */

	/**
	 * Compute the parent partition. This is the next partition whose subtree includes color.
	 */
	private int getParent(int color) {
		int parent = color + 1;
		while (mInterpolator.mStartOfSubtrees[parent] > color) {
			parent++;
		}
		return parent;
	}

	/**
	 * Compute the A-local child partition. This is the child that is A-local to the occurrence. This function returns
	 * -1 if all children are in B.
	 */
	private int getChild(int color, Occurrence occur) {
		int child = color - 1;
		while (child >= mInterpolator.mStartOfSubtrees[color]) {
			if (occur.isALocal(child)) {
				return child;
			}
			child = mInterpolator.mStartOfSubtrees[child] - 1;
		}
		return -1;
	}

	/* Methods to deal with array terms */

	private static boolean isSelectTerm(Term term) {
		if (term instanceof ApplicationTerm) {
			return ((ApplicationTerm) term).getFunction().getName().equals("select");
		}
		return false;
	}

	private static boolean isStoreTerm(Term term) {
		if (term instanceof ApplicationTerm) {
			return ((ApplicationTerm) term).getFunction().getName().equals("store");
		}
		return false;
	}

	private static Term getArrayFromSelect(Term select) {
		assert isSelectTerm(select);
		return ((ApplicationTerm) select).getParameters()[0];
	}

	private static Term getIndexFromSelect(Term select) {
		assert isSelectTerm(select);
		return ((ApplicationTerm) select).getParameters()[1];
	}

	private static Term getArrayFromStore(Term store) {
		assert isStoreTerm(store);
		return ((ApplicationTerm) store).getParameters()[0];
	}

	private static Term getIndexFromStore(Term store) {
		assert isStoreTerm(store);
		return ((ApplicationTerm) store).getParameters()[1];
	}

	/**
	 * Build a select equality to summarize an inner A-path in the simple case for read-over-weakeq.
	 * 
	 * @param left
	 *            the shared array at the left path end.
	 * @param right
	 *            the shared array at the right path end.
	 * @param index
	 *            the shared index for which the arrays match, i.e. the shared term for the weakpath index.
	 * @return an interpolant term of the form "¬pre \/ left[index]=right[index]"
	 */
	private Term buildSelectEq(Term left, Term right, Term index) {
		final Term leftSelect = mTheory.term("select", left, index);
		final Term rightSelect = mTheory.term("select", right, index);
		return mTheory.equals(leftSelect, rightSelect);
	}

	/**
	 * Build a weq term for two arrays and a given formula. It states that two arrays differ at most at #stores
	 * positions, and each difference satisfies F.
	 * 
	 * @param left
	 *            the shared array at the left path end
	 * @param right
	 *            the shared array at the right path end
	 * @param order
	 *            the order (= #stores) of the weq term
	 * @param formula
	 *            the formula satisfied by the diff terms, with an auxiliary variable
	 * @param auxVar
	 *            the auxiliary variable in the formula
	 * @return
	 */
	private Term buildWeqTerm(Term left, Term right, int order, Term formula, TermVariable auxVar) {
		Term rewrite = left;
		Term weqTerm = mTheory.mTrue;

		for (int m = 0; m < order; m++) {
			Term arrayEquality = mTheory.equals(rewrite, right);
			Term diffTerm = mTheory.term("@diff", rewrite, right);
			Term fTerm = mTheory.let(auxVar, diffTerm, formula);
			weqTerm = mTheory.and(weqTerm, mTheory.or(arrayEquality, fTerm));
			rewrite = mTheory.term("store", rewrite, diffTerm, mTheory.term("select", right, diffTerm));
		}
		weqTerm = mTheory.and(weqTerm, mTheory.equals(rewrite, right));

		return weqTerm;
	}

	/**
	 * Build an nweq term for two arrays and a given formula. It states that two arrays differ at some index that
	 * satisfies F or on more than #stores indices.
	 * 
	 * @param left
	 *            the shared array at the left path end
	 * @param right
	 *            the shared array at the right path end
	 * @param order
	 *            the order (= #stores) of the nweq term
	 * @param formula
	 *            the formula satisfied by the diff terms, with an auxiliary variable
	 * @param auxVar
	 *            the auxiliary variable in the formula
	 * @return
	 */
	private Term buildNweqTerm(Term left, Term right, int order, Term formula, TermVariable auxVar) {
		Term rewrite = left;
		Term nweqTerm = mTheory.mFalse;

		for (int m = 0; m < order; m++) {
			Term arrayDisequality = mTheory.not(mTheory.equals(rewrite, right));
			Term diffTerm = mTheory.term("@diff", rewrite, right);
			Term fTerm = mTheory.let(auxVar, diffTerm, formula);
			nweqTerm = mTheory.or(nweqTerm, mTheory.and(arrayDisequality, fTerm));
			rewrite = mTheory.term("store", rewrite, diffTerm, mTheory.term("select", right, diffTerm));
		}
		nweqTerm = mTheory.or(nweqTerm, mTheory.not(mTheory.equals(rewrite, right)));

		return nweqTerm;
	}

	/**
	 * Build the F_pi^A - term. It collects the B-parts of index disequalities on an A-path.
	 * 
	 * @param color
	 *            the current partition
	 * @param sharedIndex
	 *            the shared term representing the weakpathindex
	 * @param indexDiseqs
	 *            disequalities between weakpathindex and all indices on the store path between left and right.
	 * @return the disjunction of the negated B-parts of index diseqs on an A-path, in shared terms.
	 */
	private Term buildFPiATerm(int color, Term sharedIndex, Map<ApplicationTerm, LitInfo> indexDiseqs) {
		if (indexDiseqs == null) {
			return mTheory.mFalse;
		}
		Set<Term> indexTerms = new HashSet<Term>();
		for (ApplicationTerm diseq : indexDiseqs.keySet()) {
			final LitInfo info = indexDiseqs.get(diseq);
			// Collected index diseqs are either mixed or B-local.
			// In the first case, there is a mixed term, in the second, the store index is shared.
			final Term index = info.isMixed(color) ? info.getMixedVar()
					: diseq.getParameters()[0].equals(mStorePath.getIndex()) ? diseq.getParameters()[1]
							: diseq.getParameters()[0];
			indexTerms.add(mTheory.equals(index, sharedIndex));
		}
		Term fATerm = mTheory.or(indexTerms.toArray(new Term[indexTerms.size()]));
		return fATerm;
	}

	/**
	 * Build the F_pi^B - term. It collects the A-parts of index disequalities on a B-path.
	 * 
	 * @param color
	 *            the current partition
	 * @param sharedIndex
	 *            the shared term representing the weakpathindex
	 * @param indexDiseqs
	 *            disequalities between weakpathindex and all indices on the store path between left and right.
	 * @return the conjunction of the A-parts of index diseqs on a B-path, in shared terms.
	 */
	private Term buildFPiBTerm(int color, Term sharedIndex, Map<ApplicationTerm, LitInfo> indexDiseqs) {
		if (indexDiseqs == null) {
			return mTheory.mTrue;
		}
		Set<Term> indexTerms = new HashSet<Term>();
		for (ApplicationTerm diseq : indexDiseqs.keySet()) {
			final LitInfo info = indexDiseqs.get(diseq);
			// Collected index diseqs are either mixed or A-local.
			// In the first case, there is a mixed term, in the second, the store index is shared.
			final Term index = info.isMixed(color) ? info.getMixedVar()
					: diseq.getParameters()[0].equals(mStorePath.getIndex()) ? diseq.getParameters()[1]
							: diseq.getParameters()[0];
			if (info.isMixed(color)) { // Add the A projection of the index disequality (an equality in the mixed case)
				indexTerms.add(mTheory.equals(index, sharedIndex));
			} else if (info.isALocal(color)) {
				// If the index diseq is A local, the A projection is the diseq itself.
				indexTerms.add(mTheory.not(mTheory.equals(index, sharedIndex)));
			}
		}
		Term fBTerm = mTheory.and(indexTerms.toArray(new Term[indexTerms.size()]));
		return fBTerm;
	}

	/**
	 * This class interpolates a single weak path.
	 */
	class WeakPathInfo {
		Term mPathIndex;
		Term[] mPath;
		/**
		 * The set of partitions for which there is an AB-shared path from start to end.
		 */
		BitSet mHasABPath;
		/**
		 * The first partition for which the path from start to end is A-local. This is mNumInterpolants, if there is no
		 * such partition. If mHasABPath is not empty, this value is undefined; we set it to the root of the mHasABPath
		 * tree, which equals the two mColor of the head and tail node.
		 */
		int mMaxColor;
		/**
		 * When interpolating mPath, this stores the information for a path which is not yet closed at the left side.
		 */
		WeakPathEnd mHead;
		/**
		 * When interpolating mPath, this stores the information for a path which is closed at the left side but still
		 * open on the right side.
		 */
		WeakPathEnd mTail;

		boolean mComputed;

		public WeakPathInfo(ProofPath path) {
			mPathIndex = path.getIndex();
			mPath = path.getPath();
			mHasABPath = new BitSet(mNumInterpolants);
			mHasABPath.set(0, mNumInterpolants);
			mMaxColor = mNumInterpolants;
		}

		/**
		 * Calculate the interpolants for the complete weakpath and all partitions for read-over-weakeq.
		 */
		public void interpolateWeakPathInfo() {
			if (mComputed) {
				return;
			}

			mHead = new WeakPathEnd();
			mTail = new WeakPathEnd();

			final Term[] diseqTerms = mDiseq.getParameters();

			// Depending on mDiseq, determine whether to start and end with A or B or AB.
			final Term headTerm, tailTerm;
			final Occurrence headOccur, tailOccur;
			if (getArrayFromSelect((ApplicationTerm) diseqTerms[0]).equals(mPath[0])) {
				headTerm = diseqTerms[0];
				tailTerm = diseqTerms[1];
			} else {
				headTerm = diseqTerms[1];
				tailTerm = diseqTerms[0];
			}
			headOccur = mInterpolator.getOccurrence(headTerm, null);
			tailOccur = mInterpolator.getOccurrence(tailTerm, null);

			mTail.closeAPath(mHead, null, headOccur);
			mTail.openAPath(mHead, null, headOccur);

			for (int i = 0; i < mPath.length - 1; i++) {
				final Term left = mPath[i];
				final Term right = mPath[i + 1];
				final ApplicationTerm lit = mEqualities.get(new SymmetricPair<Term>(left, right));
				Term boundaryTerm = left;

				// Each step in a weak path can be either an equality literal or a store step of form "a (store a i v)".
				// In the second case, there is no literal in the lemma.
				if (lit == null) {
					// A store step can only open or close a path at term "a" if "a" is the left term;
					// we also open (resp. close) at shared stores if the index diseq "storeindex != weakpathindex" is
					// A-local (resp. B-local) to avoid collecting the diseq.
					// after this, we store the index disequality "storeindex != weakpathindex" for the interpolant if
					// it is mixed, or if it is A-local on a B-local path or vice versa.
					final Term storeTerm =
							isStoreTerm(left) && getArrayFromStore((ApplicationTerm) left).equals(right) ? left : right;
					final Term arrayTerm = storeTerm.equals(left) ? right : left;
					assert getArrayFromStore((ApplicationTerm) storeTerm).equals(arrayTerm);
					Occurrence stepOcc = mInterpolator.getOccurrence(storeTerm, null);
					final Term storeIndex = getIndexFromStore((ApplicationTerm) storeTerm);
					ApplicationTerm indexDiseq = mDisequalities.get(new SymmetricPair<Term>(storeIndex, mPathIndex));
					Occurrence indexDiseqOcc = mInterpolator.getLiteralInfo(indexDiseq);
					Occurrence intersectOcc = stepOcc.intersect(indexDiseqOcc);

					mTail.closeAPath(mHead, boundaryTerm, stepOcc);
					mTail.closeAPath(mHead, boundaryTerm, intersectOcc);
					mTail.openAPath(mHead, boundaryTerm, intersectOcc);
					mTail.openAPath(mHead, boundaryTerm, stepOcc);
					mTail.addIndexDisequality(mHead, storeTerm);
				} else { // In equality steps, we just close or open A paths.
					LitInfo stepInfo = mInterpolator.getLiteralInfo(lit);
					mTail.closeAPath(mHead, boundaryTerm, stepInfo);
					mTail.openAPath(mHead, boundaryTerm, stepInfo);
					// If the equality is mixed in some partition, we open or close the path at the mixed variable.
					if (((LitInfo) stepInfo).getMixedVar() != null) {
						final Occurrence occ = mInterpolator.getOccurrence(right, null);
						boundaryTerm = ((LitInfo) stepInfo).getMixedVar();
						mTail.closeAPath(mHead, boundaryTerm, occ);
						mTail.openAPath(mHead, boundaryTerm, occ);
					}
				}
			}

			mTail.closeAPath(mHead, mPath[mPath.length - 1], tailOccur);
			mTail.openAPath(mHead, mPath[mPath.length - 1], tailOccur);

			// Paths which are still open at mPath[0] or mPath[mPath.length - 1] have to be closed.
			// Note that we might need mixed vars in the case where we build select equalities.
			closeWeakPath();

			mComputed = true;
		}

		/**
		 * Close the outer paths which are still open at the left or right end. There is nothing to do in the cases
		 * where we don't have a shared index, because if there was an A-local outer path in the B-local case (or vice
		 * versa), it has already been closed by using either head- or tailOccur. For partitions where the main diseq is
		 * mixed, we have to close all the partitions on the way from mHead.mColor to mTail.mColor (except for their lca
		 * partition). For partitions where the main diseq is A(resp. B)-local or shared and a shared select index
		 * exists, B(resp. A)-local and mixed index diseqs on outer A(resp. B)-paths have to be added to the interpolant
		 * as premise (resp. conjunct).
		 */
		private void closeWeakPath() {
			// First, close the paths in partitions where the main diseq is mixed, or where it is shared and one of the
			// outer paths is in A and the other one in B => select equalities are built.
			while (mHead.mColor < mNumInterpolants || mTail.mColor < mNumInterpolants) {
				if (mHead.mColor < mTail.mColor) { // the left outer path is an A-path
					final int color = mHead.mColor;
					// Add the interpolant for the left (A) path
					mHead.addInterpolantClauseOuterAPath(color);
					// Add the interpolant for the right (B) path, i.e. the A part of index diseqs
					mTail.addInterpolantClauseOuterBPath(color);
					// go to the parent partition
					mHead.mColor = getParent(mHead.mColor);
				} else if (mHead.mColor == mTail.mColor) {
					break;
				} else { // the right outer path is an A-path
					final int color = mTail.mColor;
					// Add the interpolant for the right (A) path
					mTail.addInterpolantClauseOuterAPath(color);
					// Add the interpolant for the left (B) path, i.e. the A part of index diseqs
					mHead.addInterpolantClauseOuterBPath(color);
					// go to the parent partition
					mTail.mColor = getParent(mTail.mColor);
				}
			}
			// Then, close the paths for partitions where the outer open paths and the main diseq are all in A (or B).
			// Here, only index disequalities are added.
			for (int color = 0; color < mNumInterpolants; color++) {
				if (mSharedIndex[color] == null) { // Nothing to do in the cases where no shared select index exists.
					continue;
				}
				if (mHead.mIndexDiseqs[color] == null && mTail.mIndexDiseqs[color] == null) { // No index diseqs to add.
					continue;
				}
				final Term index = mSharedIndex[color];
				Map<ApplicationTerm, LitInfo> allDiseqs = new HashMap<ApplicationTerm, LitInfo>();
				if (mHead.mIndexDiseqs[color] != null) {
					allDiseqs.putAll(mHead.mIndexDiseqs[color]);
				}
				if (mTail.mIndexDiseqs[color] != null) {
					allDiseqs.putAll(mTail.mIndexDiseqs[color]);
				}
				if (mDiseqInfo.isALocal(color)) {
					// A-local outer paths must be closed, B-local ones are already apart from the shared case.
					assert mHead.mTerm[color] != null || mTail.mTerm[color] != null; // one of the outer paths is in A
					// Add the B part of the diseqs as premise for the interpolant
					final Term fPiA = buildFPiATerm(color, index, allDiseqs);
					mInterpolants[color].add(fPiA);
					mHead.mIndexDiseqs[color] = mTail.mIndexDiseqs[color] = null;
				} else {
					assert mDiseqInfo.isBorShared(color);
					// B-local paths must be closed, A-local ones are already closed, at the latest in the 1st part.
					assert mHead.mTerm[color] == null || mTail.mTerm[color] == null; // one of the outer paths is in B
					// Add the A part of the diseqs as conjunct to the interpolant
					final Term fPiB = buildFPiBTerm(color, index, allDiseqs);
					mInterpolants[color].add(fPiB);
					mHead.mIndexDiseqs[color] = mTail.mIndexDiseqs[color] = null;
				}
			}
		}

		/**
		 * To interpolate a weak path, we iterate over the equality and store steps on the weak path. This class
		 * collects the information that has to be processed between this weak path end and the current position.
		 */
		class WeakPathEnd {
			/**
			 * The first partition for which there is an A-local prefix of the path. If mHasABPath is non-empty, this is
			 * the first partition that is not in mHasABPath, i.e. the first for which only a continuous A-path but not
			 * a continuous B-path exists.
			 */
			int mColor;
			/**
			 * For each partition this gives the term that ends the first A-local chain of equalities. Note that
			 * mTerm[color] is distinct from null only for paths which are still open on the opposite end.
			 */
			Term[] mTerm;
			/**
			 * For each partition, this gives the term which marks the last change from A to B or vice versa. This can
			 * be the same term as in mTerm if the path is A local and still open on the opposite side.
			 */
			Term[] mLastChange;
			/**
			 * For each partition this gives the set of B(resp. A)-local and mixed store index disequalities found on
			 * the A (resp. B) path so far.
			 */
			Map<ApplicationTerm, LitInfo>[] mIndexDiseqs;

			@SuppressWarnings("unchecked")
			public WeakPathEnd() {
				mColor = mNumInterpolants;
				mTerm = new Term[mNumInterpolants];
				mLastChange = new Term[mNumInterpolants];
				mIndexDiseqs = new Map[mNumInterpolants];
			}

			public void closeAPath(WeakPathEnd other, Term boundary, Occurrence occur) {
				assert (other.mColor <= mMaxColor);
				mHasABPath.and(occur.mInA);
				while (mColor < mNumInterpolants && occur.isBLocal(mColor)) {
					closeSingleAPath(other, boundary);
				}
			}

			public void openAPath(WeakPathEnd other, Term boundary, Occurrence occur) {
				while (true) {
					final int child = getChild(mColor, occur);
					// if there is no A-local child, we are done.
					if (child < 0) {
						break;
					}
					assert occur.isALocal(child);
					openSingleAPath(other, boundary, child);
				}
			}

			/**
			 * Close the A path for partition color. This is called when we add a term to the chain that is B-local for
			 * the current mColor. We set mColor to the parent node. We also close the open path on mColor or open a new
			 * one and increment mMaxColor if such a path was not yet open. Note that closing an A path opens a B path
			 * at the same time.
			 * 
			 * @param other
			 *            the other PathEnd
			 * @param boundary
			 *            the boundary term for opening/closing the path.
			 */
			private void closeSingleAPath(WeakPathEnd other, Term boundary) {
				// This should be empty now, since we anded it with occur.mInA and the occurrence is not in A for color.
				assert mHasABPath.isEmpty();
				final int color = mColor;
				mColor = getParent(color);
				if (color < mMaxColor) { // the path is already closed at the left side by a B path in front of it
					// Add the interpolant clause for this A path.
					addInterpolantClauseAPath(color, boundary);
					mTerm[color] = null;
				} else {
					assert (mMaxColor == color);
					other.mTerm[color] = boundary;
					mMaxColor = getParent(color);
				}
				mLastChange[color] = boundary;
				if (other.mLastChange[color] == null) {
					other.mLastChange[color] = boundary;
				}
			}

			/**
			 * Open a new A path. This is called when a term is added that is A local in child, where child is a child
			 * of mColor. We start a new A path on child. If we have still slack, since mHasABPath contains child, we
			 * don't have to open the path and just set mMaxColor to child. Note that opening an A path closes a B path
			 * at the same time.
			 * 
			 * @param other
			 *            the other path end.
			 * @param boundary
			 *            the term that starts the new A path.
			 * @param child
			 *            the child of mColor for which the added term is A local.
			 */
			private void openSingleAPath(WeakPathEnd other, Term boundary, int child) {
				if (mHasABPath.get(child)) {
					mMaxColor = other.mColor = mColor = child;
					// Compute all nodes below child excluding child itself
					final BitSet subtree = new BitSet();
					subtree.set(mInterpolator.mStartOfSubtrees[child], child);
					// Keep only those below the current child.
					mHasABPath.and(subtree);
				} else {
					// Open a new A path.
					mTerm[child] = boundary;
					mColor = child;
					// Add an interpolant clause for partitions where this closes a B path
					addInterpolantClauseBPath(mColor, boundary);
					mLastChange[child] = boundary;
					if (other.mLastChange[child] == null) {
						other.mLastChange[child] = boundary;
					}
					mHasABPath.clear();
				}
			}

			/**
			 * Add the disequality between the weakpath index and a store index. There are three cases where it has to
			 * be included in the interpolant: (i) the disequality is mixed, (ii) the disequality is A local on a B
			 * local path segment, (iii) the disequality is B local on an A local path segment.
			 * 
			 * @param other
			 *            The other path end.
			 * @param storeTerm
			 *            The store term from which we extract the store index.
			 * @param storeOccur
			 *            The occurrence of the store term.
			 */
			private void addIndexDisequality(WeakPathEnd other, Term storeTerm) {
				assert isStoreTerm(storeTerm);
				final Term storeIndex = getIndexFromStore((ApplicationTerm) storeTerm);
				ApplicationTerm diseq = mDisequalities.get(new SymmetricPair<Term>(storeIndex, mPathIndex));
				LitInfo diseqInfo = mInterpolator.getLiteralInfo(diseq);

				// The diseq has to be added to all partitions where it is mixed and all partitions that lie on the
				// tree path between the partition of the diseq and the partition of the store term.
				// In nodes under the lca which are not on the way, both are in B, in nodes above the lca both are in A,
				// and in both cases there is nothing to do.
				addIndexDiseqAllColors(other, diseqInfo, diseq, diseqInfo);
				if (diseqInfo.getMixedVar() != null) {
					// additionally go up and down with weakpathindexoccur
					final Occurrence occur = mInterpolator.getOccurrence(mPathIndex, null);
					addIndexDiseqAllColors(other, occur, diseq, diseqInfo);
				}
			}

			/**
			 * Go through the colors determined by occur, starting from currentColor, and add the index disequality to
			 * those partitions. This adds the index disequality to all partitions where it is not in A (resp. B) while
			 * the path is.
			 */
			private void addIndexDiseqAllColors(WeakPathEnd other, Occurrence occur, ApplicationTerm diseq,
					LitInfo diseqInfo) {
				int currentColor = mColor;
				// Up
				mHasABPath.and(occur.mInA);
				while (currentColor < mNumInterpolants && occur.isBLocal(currentColor)) {
					assert mHasABPath.isEmpty();
					final int color = currentColor;
					currentColor = getParent(color);
					addIndexDiseqOneColor(other, diseq, diseqInfo, color);
				}
				// Down
				while (true) {
					final int child = getChild(currentColor, occur);
					// If there is no A-local child, we are done.
					if (child < 0) {
						break;
					}
					assert occur.isALocal(child);
					if (mHasABPath.get(child)) {
						// Compute all nodes below child excluding child itself
						final BitSet subtree = new BitSet();
						subtree.set(mInterpolator.mStartOfSubtrees[child], child);
						// Keep only those below the current child.
						mHasABPath.and(subtree);
					} else {
						addIndexDiseqOneColor(other, diseq, diseqInfo, child);
						currentColor = child;
					}
				}
			}

			/**
			 * Add the index disequality to one partition.
			 */
			private void addIndexDiseqOneColor(WeakPathEnd other, ApplicationTerm diseq, LitInfo diseqInfo, int color) {
				// If the path is still open at the other path end, i.e. if other.mLastChange[color] is still null, we
				// have to store the diseq in the other pathend
				if (other.mLastChange[color] == null) {
					if (other.mIndexDiseqs[color] == null) {
						other.mIndexDiseqs[color] = new HashMap<ApplicationTerm, LitInfo>();
					}
					other.mIndexDiseqs[color].put(diseq, diseqInfo);
				} else { // else in this one.
					if (mIndexDiseqs[color] == null) {
						mIndexDiseqs[color] = new HashMap<ApplicationTerm, LitInfo>();
					}
					mIndexDiseqs[color].put(diseq, diseqInfo);
				}
			}

			/**
			 * Add an interpolant clause for a closed A path. Case (i) (shared select index and mDiseq not A-local): the
			 * conjunction of all B-local or the B-part of mixed index diseqs on this path is a premise for the arrays
			 * at the path ends to coincide at weakpathindex => interpolant conjunct of the form
			 * "i!=k1/\.../\i!=kn->start[i]=end[i]". Case (ii) (shared select index and mDiseq A-local): B-local index
			 * diseqs are a premise for all interpolant parts summarizing A paths. Case (iii) Case 3 (mDiseq B-local, no
			 * shared select index): Summarize the path by a WEQ term stating that the arrays at the path end differ at
			 * most at k locations (k= # of B-local and mixed index diseqs on the path) which are all different from
			 * weakpathindex. Case (iv) (mDiseq A-local, no shared select index): Nothing to do.
			 */
			private void addInterpolantClauseAPath(int color, Term boundary) {
				Term left = mLastChange[color];
				Term right = boundary;
				if (mSharedIndex[color] != null) {
					if (mDiseqInfo.isALocal(color)) { // Case (ii)
						if (mIndexDiseqs[color] != null) {
							assert mSharedIndex[color] == mPathIndex;
							final Term fPiA = buildFPiATerm(color, mSharedIndex[color], mIndexDiseqs[color]);
							mInterpolants[color].add(fPiA);
							mIndexDiseqs[color] = null;
						}
					} else { // Case (i)
						Term index = mSharedIndex[color];
						Term fPiA = buildFPiATerm(color, index, mIndexDiseqs[color]);
						final Term selectEq = buildSelectEq(left, right, index);
						final Term itpClause = mTheory.or(selectEq, fPiA);
						mInterpolants[color].add(itpClause);
						mIndexDiseqs[color] = null;
					}
				} else if (mDiseqInfo.isALocal(color)) { // Case (iv)
					assert mIndexDiseqs[color] == null;
					return;
				} else { // Case (iii)
					assert mDiseqInfo.isBLocal(color);
					final int order = mIndexDiseqs[color] == null ? 0 : mIndexDiseqs[color].size();
					final TermVariable cdot = mTheory.createFreshTermVariable("cdot", mPathIndex.getSort());
					final Term fPiA = buildFPiATerm(color, cdot, mIndexDiseqs[color]);
					final Term itpClause = buildWeqTerm(left, right, order, fPiA, cdot);
					mInterpolants[color].add(itpClause);
					mIndexDiseqs[color] = null;
				}
			}

			/**
			 * Add an interpolant clause for a closed B path.
			 * Case (i) (shared select index, mDiseq not A-local): A-local and the A part of
			 * mixed index disequalities are added as conjunct to the entire lemma interpolant.
			 * Case (ii) (shared select index, mDiseq A-local): Summarize the path by stating that the arrays at the path ends differ at weakpathindex =>
			 * interpolant disjunct of the form "i!=k1/\.../\i!=kn/\start[i]!=end[i]".
			 * Case (iii) (B-local, no shared select index): Nothing to do.
			 * Case (iv) (A-local, no shared select index):
			 * Summarize the path by an NWEQ term stating that the arrays at the path end differ at least at k locations
			 * (k= # B-local and mixed index diseqs on the path) of which (at least) one equals the weakpathindex.
			 */
			private void addInterpolantClauseBPath(int color, Term boundary) {
				final Term left = mLastChange[color];
				final Term right = boundary;
				Term fPiB = mTheory.mTrue;
				if (mSharedIndex[color] != null) {
					final Term index = mSharedIndex[color];
					if (mIndexDiseqs[color] != null) {
						fPiB = buildFPiBTerm(color, index, mIndexDiseqs[color]);
					}
					if (mDiseqInfo.isALocal(color)) { // Case (ii)
						final Term selectDiseq = mTheory.not(buildSelectEq(left, right, index));
						final Term itpClause = mTheory.and(selectDiseq, fPiB);
						mInterpolants[color].add(itpClause);
					} else { // Case (i)
						mInterpolants[color].add(fPiB);
					}
					mIndexDiseqs[color] = null;
				} else if (mDiseqInfo.isALocal(color)) { // Case (iv)
					final int order = mIndexDiseqs[color] == null ? 0 : mIndexDiseqs[color].size();
					final TermVariable cdot = mTheory.createFreshTermVariable("cdot", mPathIndex.getSort());
					fPiB = buildFPiBTerm(color, cdot, mIndexDiseqs[color]);
					final Term itpClause = buildNweqTerm(left, right, order, fPiB, cdot);
					mInterpolants[color].add(itpClause);
					mIndexDiseqs[color] = null;
				} else { // Case (iii)
					assert mDiseqInfo.isBLocal(color);
					assert mIndexDiseqs[color] == null;
					return;
				}
			}

			/**
			 * Add an interpolant clause for an A path ending at the very left or very right path end. This is only used
			 * for partitions where the main disequality is mixed or shared. => interpolant conjunct of the form
			 * "i!=k1/\.../\i!=kn->start[i]=end[i]" Note that one needs the mixedVar here if mDiseqInfo.isMixed(color).
			 * 
			 * @param color
			 *            the current partition
			 */
			private void addInterpolantClauseOuterAPath(int color) {
				// Add the interpolant for the outer (A) path
				final Term index = mSharedIndex[color];
				assert index != null;
				final Term fPiA = buildFPiATerm(color, mSharedIndex[color], mIndexDiseqs[color]);
				mIndexDiseqs[color] = null;
				if (mDiseqInfo.isALocal(color)) { // Case (ii)
					mInterpolants[color].add(fPiA);
				} else { // Case (i)
					final Term inner = mLastChange[color];
					final Term innerSelect, outerSelect;
					if (mDiseqInfo.isMixed(color)) {
						assert inner != null;
						innerSelect = mTheory.term("select", inner, index);
						outerSelect = mDiseqInfo.getMixedVar();
					} else { // The whole path from mPath[0] to mPath[mPath.length - 1] is A
						assert mDiseqInfo.isAB(color);
						if (this.equals(mHead)) {
							innerSelect = mTheory.term("select", mPath[0], index);
							outerSelect = mTheory.term("select", mPath[mPath.length - 1], index);
						} else {
							innerSelect = mTheory.term("select", mPath[mPath.length - 1], index);
							outerSelect = mTheory.term("select", mPath[0], index);
						}
					}
					final Term selectEq = mTheory.equals(outerSelect, innerSelect);
					/*
					 * Here, we have to add the index equality if we are on a right outer A-path in the mixed case where
					 * the index equality is B-local and both indices are shared.
					 */
					Term indexEq = mTheory.mFalse;
					if (this.equals(mTail) && mDiseqInfo.isMixed(color)) {
						final LitInfo indexEqInfo = mInterpolator.getLiteralInfo(mIndexEquality);
						if (indexEqInfo.isBLocal(color)) {
							final Term otherIndex = indexEqInfo.getMixedVar() != null ? indexEqInfo.getMixedVar()
									: mIndexEquality.getParameters()[0].equals(mStorePath.getIndex())
											? mIndexEquality.getParameters()[1]
											: mIndexEquality.getParameters()[0];
							final Occurrence otherIndexOccur = mInterpolator.getOccurrence(otherIndex, null);
							if (otherIndexOccur.isAB(color)) {
								indexEq = mTheory.not(mIndexEquality);
							}
						}
					}
					final Term pre = mTheory.or(indexEq, fPiA);
					final Term itpClause = mTheory.or(pre, selectEq);
					mInterpolants[color].add(itpClause);
				}
			}

			/**
			 * Add an interpolant clause for a B path ending at the very left or very right path end.
			 * This is not needed for the cases where mDiseq is A-local.
			 * 
			 * @param color
			 *            the current partition
			 */
			private void addInterpolantClauseOuterBPath(int color) {
				final Term index = mSharedIndex[color];
				assert index != null;
				final Term fPiB = buildFPiBTerm(color, index, mIndexDiseqs[color]);
				mIndexDiseqs[color] = null;
				mInterpolants[color].add(fPiB);
			}
		}
	}
}
