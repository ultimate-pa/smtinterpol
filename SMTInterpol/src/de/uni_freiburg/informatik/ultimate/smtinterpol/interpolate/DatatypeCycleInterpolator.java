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
		mStartSelectors = new String[mPath.length];
		mStartConstructors = new String[mPath.length];
		mStartTesters = new FunctionSymbol[mPath.length];

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
				closeAPaths(literalInfo, mPath[i], i);
				openAPaths(literalInfo, mPath[i], i);
				// close and open A-paths in the middle of mixed literals
				if (literalInfo.isMixed(mLastColor)) {
					final Occurrence rightOccurrence = mInterpolator.getOccurrence(right);
					closeAPaths(rightOccurrence, literalInfo.getMixedVar(), i);
					openAPaths(rightOccurrence, literalInfo.getMixedVar(), i);
				}
			}

			final Term nextTerm = mPath[i+2];
			if (isConsParentOf(right, nextTerm)) {
				// generate selector for child step
				addConsToAPath((ApplicationTerm) right, i + 1);
			} else {
				assert(isSelParentOf(right, nextTerm));
				// close and open A-paths after the literal where the tester occurrence forces a switch
				final Occurrence testerOccurrence = mTestersOccurrence.get(right);
				closeAPaths(testerOccurrence, right, i + 1);
				openAPaths(testerOccurrence, right, i + 1);
				// generate selector for child step
				addSelToAPath(right, (ApplicationTerm) nextTerm, i + 1);
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
		mStartSelectors[litIndex] = getSelector((ApplicationTerm) mPath[litIndex], mPath[litIndex + 1]);
		final DataType dataType = (DataType) consTerm.getSort().getSortSymbol();
		mStartConstructors[litIndex] = dataType.findConstructor(functionSymbol.getName()).getName();
	}

	//
	private void addSelToAPath(final Term parentTerm, final ApplicationTerm childTerm, int litIndex) {
		final FunctionSymbol functionSymbol = childTerm.getFunction();
		// store the selector and tester function
		assert(functionSymbol.isSelector());
		mStartSelectors[litIndex] = functionSymbol.getName();
		// String testerFunction = mTestersFunctions.get(((ApplicationTerm) term).getParameters()[0]);
		final FunctionSymbol testerFunction = mTestersFunctions.get(parentTerm);
		mStartTesters[litIndex] = testerFunction;
	}


	/**
	 * Closes all A paths and goes up the tree until the occurrence is in A or
	 * mixed.
	 *
	 * @param occurence    the occurrence of the term/literal that we use
	 * @param boundaryTerm the boundary term
	 * @param litIndex     the index into the mPath.
	 */
	private void closeAPaths(Occurrence occurrence, Term boundaryTerm, int litIndex) {
		mAllInA.and(occurrence.mInA);
		int color = mLastColor;
		final int top = mNumInterpolants;

		// increase the color to go up the Tree, while the occurrence is in B, and close the A-Paths for those partitions
		while (color < top && occurrence.isBLocal(color)) {
			// switch from shared (open A path) to B
			if (mStart[color] != null) {
				mEnd[color] = boundaryTerm;
				mEndIndices[color] = litIndex;
				addCompletedAPath(color);
			} else {
				mHead[color] = boundaryTerm;
				mHeadIndices[color] = litIndex;
			}
			color = getParent(color);
			mLastColor = color;
		}
		if (color > mMaxColor) {
			mMaxColor = color;
		}
	}

	/**
	 * Open A-paths (or close B-Paths) with the boundary term until there is no
	 * A-local child for occur. This means that we go down the tree until the
	 * corresponding literal/term occurs in this partition. For mixed literals we do
	 * nothing, since we are already at the occurrence of one of the literals.
	 *
	 * @param occurence    the occurrence of the term/literal that we use
	 * @param boundaryTerm the boundary term
	 * @param litIndex     the index into the mPath.
	 */
	private void openAPaths(Occurrence occurrence, Term boundaryTerm, int litIndex) {

		int color = mLastColor;
		color = getALocalChild(color, occurrence);
		// decrease the color to go down the Tree, while the occurrence is in A, and open the A Paths for those partitions
		while (color >= 0) {
			assert occurrence.isALocal(color);
			if (mAllInA.get(color)) {
				mMaxColor = color;
			} else {
				// stop on the partition that doesn't see a switch anymore
				// switch from B to A
				mStart[color] = boundaryTerm;
				mStartIndices[color] = litIndex;
			}
			mLastColor = color;
			color = getALocalChild(color, occurrence);
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

	/**
	 * Compute the parent partition. This is the next partition, whose subtree
	 * includes color.
	 */
	private int getParent(int color) {
		int parent = color + 1;
		while (mInterpolator.mStartOfSubtrees[parent] > color) {
			parent++;
		}
		return parent;
	}

	/**
	 * Compute the A-local child partition. This is the child, that is A-local to
	 * the occurrence. This function returns -1 if all children are in B.
	 */
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
}
