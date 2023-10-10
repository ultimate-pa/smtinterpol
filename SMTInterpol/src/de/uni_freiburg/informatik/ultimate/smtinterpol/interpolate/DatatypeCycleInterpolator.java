/*
 * Copyright (C) 2023 University of Freiburg
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
import de.uni_freiburg.informatik.ultimate.logic.DataType;
import de.uni_freiburg.informatik.ultimate.logic.DataType.Constructor;
import de.uni_freiburg.informatik.ultimate.logic.FunctionSymbol;
import de.uni_freiburg.informatik.ultimate.logic.SMTLIBConstants;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.Theory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.interpolate.Interpolator.LitInfo;
import de.uni_freiburg.informatik.ultimate.smtinterpol.interpolate.Interpolator.Occurrence;
import de.uni_freiburg.informatik.ultimate.smtinterpol.util.SymmetricPair;

/**
 * The interpolator for the cycle lemma of the theory of datatypes.
 *
 * @author Leon Cacace, Jochen Hoenicke
 */
public class DatatypeCycleInterpolator {

	private final Interpolator mInterpolator;
	private final Theory mTheory;
	private final int mNumInterpolants;
	// a set for each Interpolant, to be filled with the literals of the interpolant
	private final Set<Term>[] mInterpolants;
	// the equalities of the lemma
	private final HashMap<SymmetricPair<Term>, LitInfo> mEqualityInfos;
	// the testers as a map from their inner Term to their Occurrence
	private final HashMap<Term, LitInfo> mTestersOccurrence;
	// the testers as a map from their inner Term to their function name
	private final HashMap<Term, FunctionSymbol> mTestersFunctions;
	// the ordered literals of the lemma
	private Term[] mPath;

	// the partitions for which every literal so far was shared
	BitSet mAllInA;

	private int mMaxColor;
	private int mLastColor;

	// stores for cycles if the recent relation between literals was a select or a construct
	private boolean mIsSelectRel;

	// for each partition, the boundary terms thats start the A Path
	private final Term[] mStart;
	// for each partition, the boundary terms thats end the A Path
	private final Term[] mEnd;
	//
	private final Term[] mHead;
	// for each partition, the indices of the literals where the current A-path started (-1 if there is none for that partition)
	private final int[] mStartIndices;
	// for each partition, the indices of the literals where the A-path was closed
	// but not opened (-1 if there is none for this partition)
	private final int[] mEndIndices;
	//
	private final int[] mHeadIndices;

	// array to store select functions later applied to the start of the a path
	private String[] mStartSelectors;
	// array to store constructor names for testers
	private String[] mStartConstructors;
	// array to store tester functions
	private FunctionSymbol[] mStartTesters;

	@SuppressWarnings("unchecked")
	public DatatypeCycleInterpolator(final Interpolator interpolator,
			final HashMap<SymmetricPair<Term>, LitInfo> equalityInfos,
			final HashMap<SymmetricPair<Term>, LitInfo> disequalityInfos) {
		mInterpolator = interpolator;
		mTheory = interpolator.mTheory;
		mNumInterpolants = interpolator.mNumInterpolants;
		mInterpolants = new Set[mNumInterpolants];
		for (int i = 0; i < mNumInterpolants; i++) {
			mInterpolants[i] = new HashSet<>();
		}
		mStart = new Term[mNumInterpolants];
		mEnd = new Term[mNumInterpolants];
		mHead = new Term[mNumInterpolants];
		mStartIndices = new int[mNumInterpolants];
		mEndIndices = new int[mNumInterpolants];
		mHeadIndices = new int[mNumInterpolants];
		mAllInA = new BitSet(mNumInterpolants);
		mEqualityInfos = equalityInfos;
		mTestersOccurrence = new HashMap<>();
		mTestersFunctions = new HashMap<>();
		collectTesterInfo(equalityInfos);
		collectTesterInfo(disequalityInfos);
	}

	private void collectTesterInfo(Map<SymmetricPair<Term>, LitInfo> atomInfo) {
		for (final Map.Entry<SymmetricPair<Term>, LitInfo> entry : atomInfo.entrySet()) {
			final SymmetricPair<Term> key = entry.getKey();
			final LitInfo atomOccurenceInfo = entry.getValue();
			final Term left = key.getFirst();
			final Term right = key.getSecond();
			if (left instanceof ApplicationTerm && ((ApplicationTerm) left).getFunction().getName().equals(SMTLIBConstants.IS)) {
				mTestersFunctions.put(((ApplicationTerm) left).getParameters()[0], ((ApplicationTerm) left).getFunction());
				mTestersOccurrence.put(((ApplicationTerm) left).getParameters()[0], atomOccurenceInfo);
			} else if (right instanceof ApplicationTerm && ((ApplicationTerm) left).getFunction().getName().equals(SMTLIBConstants.IS)) {
				mTestersFunctions.put(((ApplicationTerm) right).getParameters()[0], ((ApplicationTerm) right).getFunction());
				mTestersOccurrence.put(((ApplicationTerm) right).getParameters()[0], atomOccurenceInfo);
			}
		}
	}

	/**
	 * Interpolate a datatype dt-cycle conflict. The lemma is annotated with a cycle
	 * {@code a1,b1,a2,b2,..,an} that shows that {@code a1} is equal to a
	 * constructor call on itself. The conflict must contain {@code ai == bi} (if it
	 * is not trivial) and {@code a(i+1)} is a child of {@code bi} in the sense that
	 * either {@code bi} is a term {@code cons(..,a(i+1),...)}, or that
	 * {@code a(i+1)} is a term {@code sel(bi)} and for the corresponding
	 * constructor {@code is_cons(bi) = true} occurs negated in the lemma.
	 *
	 * @param annot the argument of the :dt-cycle annotation. It has the form
	 *              {@code :cycle a1 b1 a2 b2 ... an} where a1 == an.
	 * @return The array of interpolants.
	 */
	public Term[] interpolateCycle(Term[] path) {
		mPath = path;
		mLastColor = mNumInterpolants;
		mMaxColor = mNumInterpolants;
		mAllInA.set(0, mNumInterpolants);
		mStartSelectors = new String[(mPath.length - 1) / 2 * 3 + 1];
		mStartConstructors = new String[(mPath.length - 1) / 2 * 3 + 1];
		mStartTesters = new FunctionSymbol[(mPath.length - 1) / 2 * 3 + 1];
		mIsSelectRel =  false;

		traverseCycleLemma();
		collectCycleInterpolants();

		final Term[] interpolants = new Term[mNumInterpolants];
		for (int color = 0; color < mNumInterpolants; color++) {
			interpolants[color] = mTheory.and(mInterpolants[color].toArray(new Term[mInterpolants[color].size()]));
		}
		return interpolants;
	}

	// goes through the literals for a cycle lemma
	private void traverseCycleLemma() {
		for (int i = 0; i < mPath.length - 2; i += 2) {
			final Term left = mPath[i];
			final Term right = mPath[i+1];
			if (!left.equals(right)) {
				final LitInfo literalInfo = mEqualityInfos.get(new SymmetricPair<>(left, right));

				mAllInA.and(literalInfo.mInA);
				// close and open A-paths before the literal when switches happen
				closeAPaths(literalInfo, i /2);
				openAPaths(literalInfo, i / 2);
				// close and open A-paths in the middle of mixed literals
				closeAPathsOnMixedLiterals(literalInfo, i / 2);
				openAPathsOnMixedLiterals(literalInfo, i / 2);
			}

			final Term nextTerm = mPath[i+2];
			if (isConsParentOf(right, nextTerm)) {
				mIsSelectRel = false;
				// store
				addConsToAPath((ApplicationTerm) right, i / 2);
			} else {
				assert(isSelParentOf(right, nextTerm));
				mIsSelectRel = true;
				// store
				addSelToAPath(right, (ApplicationTerm) nextTerm, i / 2);
				// close and open A-paths after the literal where the tester occurrence forces a switch
				closeAPathsForTesters((ApplicationTerm) nextTerm, i / 2);
				openAPathsForTesters((ApplicationTerm) nextTerm, i / 2);
			}
		}
	}

	//
	private void collectCycleInterpolants() {
		for (int color = 0; color < mNumInterpolants; color++) {
			if (mAllInA.get(color)) {
				assert(mInterpolants[color].isEmpty());
				mInterpolants[color].add(mTheory.mFalse);
				continue;
			}
			// APath was closed at the beginning and needs to be connected to the start of
			// the APath
			if (mHead[color] != null) {
				assert(mEnd[color] == null);
				if (mStart[color] == null) {
					mStart[color] = mPath[0];
					mStartIndices[color] = 0;
				}
				mEnd[color] = mHead[color];
				mEndIndices[color] = mHeadIndices[color];
				addCompletedAPath(color);
			}
			// APath was opened before but still needs to be closed
			else if (mStart[color] != null) {
				assert(mEnd[color] == null);
				// TODO:
				mEnd[color] = mPath[0];
				mEndIndices[color] = 0;
				addCompletedAPath(color);
			}
		}

	}

	// store the function symbol, and needed testers to later add to the
	// interpolation term
	private void addConsToAPath(final ApplicationTerm consTerm, int litIndex) {
		// store the corresponding selector and tester function
		final FunctionSymbol functionSymbol = consTerm.getFunction();
		assert(functionSymbol.isConstructor());
		mStartSelectors[litIndex * 3 + 1] = getSelector((ApplicationTerm) mPath[litIndex * 2 + 1], mPath[litIndex * 2 + 2]);
		final DataType dataType = (DataType) consTerm.getSort().getSortSymbol();
		mStartConstructors[litIndex * 3 + 1] = dataType.findConstructor(functionSymbol.getName()).getName();
	}

	//
	private void addSelToAPath(final Term parentTerm, final ApplicationTerm childTerm, int litIndex) {
		final FunctionSymbol functionSymbol = childTerm.getFunction();
		// store the selector and tester function
		assert(functionSymbol.isSelector());
		mStartSelectors[litIndex * 3 + 3] = functionSymbol.getName();
		// String testerFunction = mTestersFunctions.get(((ApplicationTerm) term).getParameters()[0]);
		final FunctionSymbol testerFunction = mTestersFunctions.get(parentTerm);
		mStartTesters[litIndex * 3 + 2] = testerFunction;
	}


	// closes the A Paths where the switch occurred
	private void closeAPaths(LitInfo literalInfo, int litIndex) {
		int color = mLastColor;
		final int top = mNumInterpolants - 1;

		// increase the color to go up the Tree, while the occurrence is in B, and close the A-Paths for those partitions
		while (color <= top) {
			// stop on the partition that doesn't see a switch anymore
			if (literalInfo.isAorShared(color)) {
				break;
			}
			if (literalInfo.isMixed(color)) {
				break;
			}
			// switch from shared (open A path) to B
			if (literalInfo.isBLocal(color)) {
				if (mStart[color] != null) {
					if (mIsSelectRel) {
						mEnd[color] = mPath[litIndex * 2 - 1];
					} else {
						mEnd[color] = mPath[litIndex * 2];
					}
					mEndIndices[color] = litIndex * 3;
					addCompletedAPath(color);
				} else {
					if (mIsSelectRel) {
						mHead[color] = mPath[litIndex * 2 - 1];
					} else {
						mHead[color] = mPath[litIndex * 2];
					}
					mHeadIndices[color] = litIndex * 3;
				}
			}
			color = getParent(color);
			mLastColor = color;
		}
		if (color > mMaxColor) {
			mMaxColor = color;
		}
	}

	// opens the A Path where the switch occurred
	// mLastColor has to be set correctly
	// TODO : use closeAPaths() first to set mLastColor correctly
	private void openAPaths(LitInfo literalInfo, int litIndex) {
		// TODO: check for mixed lits
		// assert(mLastColor == 0 || literalInfo.isAorShared(mLastColor));

		int color = mLastColor;
		color = getALocalChild(color, literalInfo);
		// decrease the color to go down the Tree, while the occurrence is in A, and open the A Paths for those partitions
		while (color >= 0) {
			if (mAllInA.get(color)) {
				mMaxColor = color;
				mLastColor = color;
			} else {
				// stop on the partition that doesn't see a switch anymore
				if (literalInfo.isBorShared(color)) {
					assert(false);
					break;
				}
				// switch from B to A
				if (literalInfo.isALocal(color)) {
					if (mIsSelectRel) {
						mStart[color] = mPath[litIndex * 2 - 1];
					} else {
						mStart[color] = mPath[litIndex * 2];
					}
					mStartIndices[color] = litIndex * 3;
				}
			}
			mLastColor = color;
			color = getALocalChild(color, literalInfo);
		}
	}

	private void closeAPathsOnMixedLiterals(LitInfo literalInfo, int litIndex) {
		int color = mLastColor;
		// move up the tree and close A-paths for partitions that need to see a switch
		while (color <= mNumInterpolants - 1) {
			// stop as soon as no closing is needed (path can stay in A)
			if (literalInfo.isAorShared(color)) {
				break;
			}
			if (literalInfo.isMixed(color)) {
				// close the A-Path
				if (mStart[color] != null) {
					mEnd[color] = literalInfo.getMixedVar();
					mEndIndices[color] = litIndex * 3 + 1;
					addCompletedAPath(color);
				}
				else {
					mHead[color] = literalInfo.getMixedVar();
					mHeadIndices[color] = litIndex * 3 + 1;
				}
			}
			// go up the tree
			color = getParent(color);
			mLastColor = color;
		}
		if (color > mMaxColor) {
			mMaxColor = color;
		}
	}

	private void openAPathsOnMixedLiterals(LitInfo literalInfo, int litIndex) {
		int color = mLastColor;
		color = getMixedChild(color, literalInfo);
		while (color <= mNumInterpolants - 1 && color >= 0) {
			if (literalInfo.isBorShared(color)) {
				break;
			}
			if (literalInfo.isMixed(color) ) {
				mStart[color] = literalInfo.getMixedVar();
				mStartIndices[color] = litIndex * 3 + 1;
			}
			mLastColor = color;
			color = getMixedChild(color, literalInfo);
		}
	}

	//
	private void closeAPathsForTesters(ApplicationTerm selTerm, int litIndex) {
		// get the occurrence of the tester
		final Occurrence testerOcc = mTestersOccurrence.get(selTerm.getParameters()[0]);
		mAllInA.and(testerOcc.mInA);
		int color = mLastColor;
		// move up the tree and close A-paths for partitions that need to see a switch
		while (color <= mNumInterpolants - 1) {
			// stop as soon as no closing is needed (path can stay in A)
			if (testerOcc.isAorShared(color)) {
				break;
			}
			// testers can't be mixed
			assert(testerOcc.isBLocal(color));
			// close the A-Path
			if (mStart[color] != null) {
				mEnd[color] = selTerm.getParameters()[0];
				mEndIndices[color] = litIndex * 3 + 2;
				addCompletedAPath(color);
			} else {
				mHead[color] = selTerm.getParameters()[0];
				mHeadIndices[color] = litIndex * 3 + 2;
			}
			// go up the tree
			color = getParent(color);
			mLastColor = color;
		}
		if (color > mMaxColor) {
			mMaxColor = color;
		}
	}

	//
	private void openAPathsForTesters(ApplicationTerm selTerm, int litIndex) {
		final Occurrence testerOcc = mTestersOccurrence.get(selTerm.getParameters()[0]);
		int color = mLastColor;
		color = getALocalChild(color, testerOcc);
		// decrease the color to go down the Tree, while the occurrence is in A, and open the A Paths for those partitions
		while (color >= 0) {
			if (mAllInA.get(color)) {
				mMaxColor = color;
				mLastColor = color;
			} else {
				// stop on the partition that doesn't see a switch anymore
				if (testerOcc.isBorShared(color)) {
					break;
				}
				// switch from B to A
				if (testerOcc.isALocal(color)) {
					// mStart[color] = mPath[litIndex * 2];
					mStart[color] = selTerm.getParameters()[0];
					mStartIndices[color] = litIndex * 3 + 2;
				}
			}
			mLastColor = color;
			color = getALocalChild(color, testerOcc);
		}
	}

	// adds the completed A path to the interpolant of the given interpolant (color)
	private void addCompletedAPath(int color) {
		Term left = mStart[color];
		final Term right = mEnd[color];
		for (int i = mStartIndices[color]; i != mEndIndices[color]; i = (i + 1) % mStartTesters.length) {
			if (mStartTesters[i] != null) {
				// String s = mStartTesters[i];
				mInterpolants[color].add(mTheory.term(mStartTesters[i], left));
			}
			if (mStartConstructors[i] != null) {
				mInterpolants[color].add(mTheory.term(SMTLIBConstants.IS, new String[] { mStartConstructors[i] },
						null, left));
			}
			if (mStartSelectors[i] != null) {
				left = mTheory.term(mStartSelectors[i], left);
			}
		}
		mInterpolants[color].add(mTheory.term("=", left, right));

		mEndIndices[color] = -1;
		mStartIndices[color] = -1;
		mEnd[color] = null;
		mStart[color] = null;
	}


	/**
	 * Checks if the child term is a selector application on the parent term.
	 *
	 * @param parent the parent term.
	 * @param child  the child term.
	 * @return true if child term is a selector application on the parent term.
	 */
	private boolean isSelParentOf(Term parent, Term child) {
		if (!(child instanceof ApplicationTerm)) {
			return false;
		}
		if (((ApplicationTerm) child).getFunction().isSelector()) {
			if (((ApplicationTerm) child).getParameters()[0] == parent) {
				return true;
			}
		}
		return false;
	}

	/**
	 * Checks if the parent term is a constructor application, that includes the
	 * child term.
	 *
	 * @param parent the parent term.
	 * @param child  the child term.
	 * @return true if parent is constructor and child one of its arguments.
	 */
	private boolean isConsParentOf(Term parent, Term child) {
		if (!(parent instanceof ApplicationTerm)) {
			return false;
		}
		if (((ApplicationTerm) parent).getFunction().isConstructor()) {
			for (final Term term : ((ApplicationTerm) parent).getParameters()) {
				if (child == term) {
					return true;
				}
			}
		}
		return false;
	}

	// returns the selector that would give the "childTerm" when applied to the "consTerm"
	private String getSelector(ApplicationTerm consTerm, Term childTerm) {
		final FunctionSymbol constructorSymbol = consTerm.getFunction();
		assert(constructorSymbol.getReturnSort().getSortSymbol().isDatatype());
		final DataType datatype = (DataType) consTerm.getSort().getSortSymbol();
		final Constructor cons = datatype.findConstructor(constructorSymbol.getName());
		final String[] s = cons.getSelectors();
		final Term[] terms = consTerm.getParameters();
		for (int i = 0; i < terms.length; i++) {
			if (childTerm.equals(terms[i])) {
				return s[i];
			}
		}
		throw new AssertionError("child term not found in constructors");
	}

	// returns the parent partition for the given partition (color)
	private int getParent(int color) {
		int parent = color + 1;
		while (mInterpolator.mStartOfSubtrees[parent] > color) {
			parent++;
		}
		return parent;
	}

	// returns for the given occurrence an A-local child partition of the given partition (color)
	// returns -1 if there is none
	private int getALocalChild(int color, Occurrence occ) {
		int child = color - 1;
		while (child >= mInterpolator.mStartOfSubtrees[color]) {
			if (occ.isALocal(child)) {
				return child;
			}
			child = mInterpolator.mStartOfSubtrees[child] - 1;
		}
		return -1;
	}

	// returns for the given occurrence a child partition of the given partition
	// (color) where the occurrence is mixed
	// returns -1 if there is none
	private int getMixedChild(int color, Occurrence occ) {
		int child = color - 1;
		while (child >= mInterpolator.mStartOfSubtrees[color]) {
			if (occ.isMixed(child)) {
				return child;
			}
			child = mInterpolator.mStartOfSubtrees[child] - 1;
		}
		return -1;
	}
}
