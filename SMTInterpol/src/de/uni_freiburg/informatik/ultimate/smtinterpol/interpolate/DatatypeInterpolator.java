// TODO: copyright

package de.uni_freiburg.informatik.ultimate.smtinterpol.interpolate;

import java.util.BitSet;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.Map;
import java.util.Set;
import java.util.Vector;

import de.uni_freiburg.informatik.ultimate.logic.DataType;
import de.uni_freiburg.informatik.ultimate.logic.DataType.Constructor;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.FormulaUnLet;
import de.uni_freiburg.informatik.ultimate.logic.FunctionSymbol;
import de.uni_freiburg.informatik.ultimate.logic.SMTLIBConstants;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.logic.Theory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.interpolate.Interpolator.LitInfo;
import de.uni_freiburg.informatik.ultimate.smtinterpol.interpolate.Interpolator.Occurrence;
import de.uni_freiburg.informatik.ultimate.smtinterpol.option.SMTInterpolConstants;
import de.uni_freiburg.informatik.ultimate.smtinterpol.util.SymmetricPair;

/**
 * The interpolator for the Theory of datatypes.
 */
public class DatatypeInterpolator {
	
	private final Interpolator mInterpolator;
	private final Theory mTheory;
	private final int mNumInterpolants;
	private InterpolatorClauseInfo mClauseInfo;
	// a set for each Interpolant, to be filled with the literals of the interpolant
	private Set<Term>[] mInterpolants;
	// the equalities of the lemma
	private HashMap<SymmetricPair<Term>, LitInfo> mEqualityLiterals;
	// the disequality of the lemma
	private HashMap<SymmetricPair<Term>, LitInfo> mDisequalityLiteral;
	// the testers as a map from their inner Term to their Occurrence
	private HashMap<Term, LitInfo> mTestersOccurrence;
	// the testers as a map from their inner Term to their function name
	private HashMap<Term, String> mTestersFunctions;
	// the ordered literals of the lemma
	private Term[] mPath;
	
	// the LitInfo for the literal currently working on
	private LitInfo mLitInfo;
	
	// the partitions for which every literal so far was shared
	BitSet mAllInA;
	
	private int mMaxColor;
	private int mHeadColor;
	private int mLastColor;
	
	// for each partition, the boundery terms thats start the A Path
	private Term[] mStart;
	// for each partition, the boundery terms thats end the A Path
	private Term[] mEnd;
	//
	private Term[] mHead;
	// for each partition, the indices of the literals where the current A-path started (-1 if there is none for that partition)
	private int[] mStartIndices;
	// for each partition, the indices of the literals where the A-path was closed but not opend (-1 if there is none for this partition)
	private int[] mEndIndices;
	//
	private int[] mHeadIndices;
	
	// array to store select functions later applied to the strat of the a path
	private String[] mStartSelectors;
	// array to store select functions later applied to the end of the a path
	private String[] mEndSelectors;
	// array to store constructor names for testers
	private String[] mStartConstructors;
	// array to store constructor names for testers
	private String[] mEndConstructors;
	// array to store tester functions
	private String[] mStartTesters;
	// array to store tester functions
	private String[] mEndTesters;

	
	// TODO: should be in function?
	// private boolean[] mIsDisequality;
	
	
	@SuppressWarnings("unchecked")
	public DatatypeInterpolator(final Interpolator interpolator) {
		mInterpolator = interpolator;
		mTheory = interpolator.mTheory;
		mNumInterpolants = interpolator.mNumInterpolants;
		mInterpolants = new Set[mNumInterpolants];
		for (int i = 0; i < mNumInterpolants; i++) {
			mInterpolants[i] = new HashSet<>();
		}
		mStart = new Term[mNumInterpolants];
		mEnd = new Term[mNumInterpolants];
		mStartIndices = new int[mNumInterpolants];
		mEndIndices = new int[mNumInterpolants];
		mAllInA = new BitSet(mNumInterpolants);
		
		// int mCurrentColor = 0;
		// int mLastColor = 0;
		// mIsDisequality = new boolean[mNumInterpolants];
	}
	
	// computes Interpolants and returns them as an array
	public Term[] computeDatatypeInterpolants(final InterpolatorClauseInfo clauseInfo) {
		mClauseInfo = clauseInfo;
		for (final Term literal : mClauseInfo.getLiterals()) {
			final Term atom = mInterpolator.getAtom(literal);
			final InterpolatorAtomInfo atomTermInfo = mInterpolator.getAtomTermInfo(atom);
			final ApplicationTerm eqTerm = atomTermInfo.getEquality();
			final LitInfo atomOccurenceInfo = mInterpolator.getAtomOccurenceInfo(atom);
			Term left = eqTerm.getParameters()[0];
			Term right = eqTerm.getParameters()[1];
			if (left instanceof ApplicationTerm && ((ApplicationTerm) left).getFunction().getName().equals(SMTLIBConstants.IS)) {
				mTestersFunctions.put(((ApplicationTerm) left).getParameters()[0], ((ApplicationTerm) left).getFunction().getName());
				mTestersOccurrence.put(((ApplicationTerm) left).getParameters()[0], atomOccurenceInfo);
			} else if (right instanceof ApplicationTerm && ((ApplicationTerm) left).getFunction().getName().equals(SMTLIBConstants.IS)) {
				mTestersFunctions.put(((ApplicationTerm) right).getParameters()[0], ((ApplicationTerm) right).getFunction().getName());
				mTestersOccurrence.put(((ApplicationTerm) right).getParameters()[0], atomOccurenceInfo);
			}
			mEqualityLiterals.put(new SymmetricPair<>(left, right), atomOccurenceInfo);			
			
			/*
			boolean isDisequality = atom == literal;
			*/
			
		}
		mPath = (Term[]) clauseInfo.getLemmaAnnotation();
		
		mLastColor = mNumInterpolants;
		mMaxColor = mNumInterpolants;
		mHeadColor = mNumInterpolants;
		mAllInA.set(0, mNumInterpolants);
		mStartSelectors = new String[mPath.length];
		mEndSelectors = new String[mPath.length];
		mStartConstructors = new String[mPath.length];
		mEndConstructors = new String[mPath.length];
		mStartTesters = new String[mPath.length];
		mEndTesters = new String[mPath.length];
		
		traverseLemma();
		
		
		Term[] interpolants = new Term[mNumInterpolants];
		for (int color = 0; color < mNumInterpolants; color++) {
			mTheory.and(mInterpolants[color].toArray(new Term[mInterpolants[color].size()]));
		}
		return interpolants;
	}
	
	private void traverseLemma() {
		for (int i = 0; i < mPath.length - 1; i += 2) {
			Term left = mPath[i];
			Term right = mPath[i+1];
			LitInfo literalInfo = mEqualityLiterals.get(new SymmetricPair<>(left, right));
			
			// TODO : lastcolor / maxcolor
			if (left instanceof ApplicationTerm) {
				growAPath((ApplicationTerm) left, i);
				// close A-paths before the literal where the tester occurrence forces a switch
				if (((ApplicationTerm) left).getFunction().isSelector()) {
					closeAPathsForTesters((ApplicationTerm) left, i);
					openAPathsForTesters((ApplicationTerm) left, i);
				}
			}
			mAllInA.and(literalInfo.mInA);
			// close and open A-paths before the literal when switches happen
			closeAPaths(literalInfo, i);
			openAPaths(literalInfo, i);
			// close and open A-paths in the middle of mixed literals
			closeAPathsOnMixedLiterals(literalInfo, i + 1);
			openAPathsOnMixedLiterals(literalInfo, i + 1);
			if (right instanceof ApplicationTerm) {
				growAPath((ApplicationTerm) right, i+1);
				if (((ApplicationTerm) right).getFunction().isSelector()) {
					// close and open A-paths after the iteral where the tester occurrence forces a switch
					closeAPathsForTesters((ApplicationTerm) right, i + 2);
					openAPathsForTesters((ApplicationTerm) right, i + 2);
				}
			}
			
		}
		if (!mAllInA.isEmpty()) {
			// TODO: set interpolants to false / true
		} 
		for (int color = 0; color < mNumInterpolants; color++) {
			if (mAllInA.get(color)) {
				assert(mInterpolants[color].isEmpty());
				mInterpolants[color].add(mTheory.mTrue);
			}
			// int color = mLastColor;
			while (color <= mNumInterpolants + 1) {
				if (mInterpolator.mStartOfSubtrees[mHeadColor] == mInterpolator.mStartOfSubtrees[color]) {
					break;
				}
				mEnd[color] = mPath[-1];
				color = getParent(color);
			}
			// TODO: build occ
			Occurrence occ = mInterpolator.new Occurrence();
			while (color > mHeadColor) {
				mStart[color] = mPath[-1];
				color = getALocalChild(color, occ);
			}
		}
		
	}
	
	// store the function symbol, and needed testers to later add to the interpolantion term
	private void growAPath(final ApplicationTerm term, int storeIndex) {
		// store the correspondng selector and tester function
		FunctionSymbol functionSymbol = ((ApplicationTerm) term).getFunction();
		if (functionSymbol.isConstructor()) {
			mStartSelectors[storeIndex] = getSelector(functionSymbol, storeIndex, storeIndex - 1);
			DataType dataType = (DataType) functionSymbol.getReturnSort().getSortSymbol();
			mStartConstructors[storeIndex] = dataType.findConstructor(functionSymbol.getName()).getName();
		}
		// store the selector and tester function
		else if (functionSymbol.isSelector()) {
			mEndSelectors[storeIndex] = functionSymbol.getName();
			String testerFunction = mTestersFunctions.get(((ApplicationTerm) term).getParameters()[0]);
			mEndTesters[storeIndex] = testerFunction;
		}
	}

	
	// closes the A Paths where the switch occured 
	private void closeAPaths(LitInfo literalInfo, int pathIndex) {
		int color = mLastColor;
		int top = mNumInterpolants + 1;
		
		// increase the color to go up the Tree, while the occurrence is in B, and close the A-Paths for those partitions
		while (color <= top) {
			// stop on the partition that doesn't see a switch anymore
			if (literalInfo.isAorShared(color)) {
				break;
			}
			if (literalInfo.isMixed(color)) {
				break;
			}
			mAllInA.clear();
			// switch from shared (open A path) to B
			if (literalInfo.isBLocal(color)) {
				if (mStart[color] != null) {
					if (mPath[pathIndex] instanceof ApplicationTerm) {
						mEnd[color] = mPath[pathIndex - 1];
					} else {
						mEnd[color] = mPath[pathIndex];
					}
					mEndIndices[color] = pathIndex;
					addCompletedAPath(color);
				} else {
					if (mPath[pathIndex] instanceof ApplicationTerm) {
						mHead[color] = mPath[pathIndex - 1];
					} else {
						mHead[color] = mPath[pathIndex];
					}
					mHeadIndices[color] = pathIndex;
				}
			}
			color = getParent(color);
		}
		mLastColor = color;
		if (color > mMaxColor) {
			mMaxColor = color;
		}
	}
	
	// opens the A Path where the switch occured 
	// TODO : use closeAPaths() first to set mLastColor correctly 
	private void openAPaths(LitInfo literalInfo, int pathIndex) {
		assert(literalInfo.isAorShared(mLastColor));
		
		int color = mLastColor;
		// increase the color to go up the Tree and close the Paths for those partitions
		while (color >= 0) {
			if (mAllInA.get(color)) {
				mMaxColor = color;
				mLastColor = color;
				mHeadColor = color;
			} else {
				// stop on the partition that doesn't see a switch anymore
				if (literalInfo.isBorShared(color)) {
					break;
				}
				// switch from B to A
				if (literalInfo.isALocal(color)) {
					mStart[color] = mPath[pathIndex];
					mStartIndices[color] = pathIndex;
					// TODO: addCompletedAPath(color);
				}				
			}
			color = getALocalChild(color, literalInfo);
		}
		if (color >= 0) { 
			mLastColor = color;
		}
	}
	
	private void closeAPathsOnMixedLiterals(LitInfo literalInfo, int closingIndex) {
		int color = mLastColor;
		// move up the tree and close A-paths for partitions that need to see a switch
		while (color <= mNumInterpolants + 1) {
			// stop as soon as no closing is needed (path can stay in A)
			if (literalInfo.isAorShared(color)) {
				break;
			}
			mAllInA.clear();
			if (literalInfo.isMixed(color)) {
				// close the A-Path
				mEnd[color] = literalInfo.getMixedVar();
				mEndIndices[color] = closingIndex;
				if (mStart[color] != null) {
					mEnd[color] = literalInfo.getMixedVar();
					mEndIndices[color] = closingIndex;
					addCompletedAPath(color);
				}
				else {
					mHead[color] = literalInfo.getMixedVar();
					mHeadIndices[color] = closingIndex;
				}
			}
			// go up the tree
			color = getParent(color);
		}
		mLastColor = color;
		if (color > mMaxColor) {
			mMaxColor = color;
		}
	}
	
	private void openAPathsOnMixedLiterals(LitInfo literalInfo, int openingIndex) {
		int color = mLastColor;
		
		while (color <= mNumInterpolants + 1) {
			if (literalInfo.isBorShared(color)) {
				break;
			}
			if (literalInfo.isMixed(color) ) {
				mStart[color] = literalInfo.getMixedVar();
				mStartIndices[color] = openingIndex;
			}
			color = getALocalChild(color, literalInfo);
		}
	}
	
	// 
	private void closeAPathsForTesters(ApplicationTerm selTerm, int closingIndex) {
		// get the occurrence of the tester
		Occurrence testerOcc = mTestersOccurrence.get(selTerm.getParameters()[0]);
		mAllInA.and(testerOcc.mInA);
		int color = mLastColor;
		// move up the tree and close A-paths for partitions that need to see a switch
		while (color <= mNumInterpolants + 1) {
			// stop as soon as no closing is needed (path can stay in A)
			if (testerOcc.isAorShared(color)) {
				break;
			}
			mAllInA.clear();
			// testers can't be mixed
			assert(testerOcc.isBLocal(color));
			// close the A-Path
			if (mStart[color] != null) {
				mEnd[color] = selTerm.getParameters()[0];
				mEndIndices[color] = closingIndex;
				addCompletedAPath(color);
			} else {
				mHead[color] = selTerm.getParameters()[0];
				mHeadIndices[color] = closingIndex;
			}
			// go up the tree
			color = getParent(color);
		}
		mLastColor = color;
		if (color > mMaxColor) {
			mMaxColor = color;
		}
	}
	
	// 
	private void openAPathsForTesters(ApplicationTerm selTerm, int openingIndex) {
		Occurrence testerOcc = mTestersOccurrence.get(selTerm.getParameters()[0]);
		int color = mLastColor;
		while (color >= 0) {
			if (testerOcc.isBorShared(color) ) {
				break;
			}
			if (mAllInA.get(color)) {
				mLastColor = color;
				mMaxColor = color;
				mHeadColor = color;
			}
			mInterpolants[color].add(mTheory.term(mTestersFunctions.get(selTerm.getParameters()[0]), selTerm.getParameters()[0]));
			color = getALocalChild(color, testerOcc);
		}
		
	}
	
	// adds the completed A path to the interpolant of the given interpolant (color)
	private void addCompletedAPath(int color) {
		Term left = mStart[color];
		Term right = mEnd[color];
		
		for (int i = mStartIndices[color]; i != mEndIndices[color]; i++, i = i % mNumInterpolants) {
			if (mStartSelectors[i] != null) {
				// TODO: tester
				left = mTheory.term(mStartSelectors[i], left);
				
				// if (mIsCons[color] == true)
				// TODO: isCons(left)
				mInterpolants[color].add(left);
			}
			if (mEndSelectors[i] != null) {
				if (mEndTesters[i] != null) {
					mInterpolants[color].add(mTheory.term(mEndTesters[i], right));
				}
				if (mEndConstructors[i] != null) {
					mInterpolants[color].add(mTheory.term(SMTLIBConstants.IS, new String[] { mEndConstructors[i] },
							null, right));
				}
				right = mTheory.term(mEndSelectors[i], right);
				
				// if (mIsCons[color] == true)
				// TODO: isCons(right)
				// Term term = mTheory.equals(isCons, right)
				mInterpolants[color].add(right);
			}
		}
		mInterpolants[color].add(mTheory.equals(left, right));
		
		mEndIndices[color] = -1;
		mStartIndices[color] = -1;
		mEnd[color] = null;
		mStart[color] = null;
		// mIsDisequality[color] = false;
	}
	
	/*
	private Term getRelevantSubTerm(ApplicationTerm applicationTerm, Term term) {
		FunctionSymbol func = applicationTerm.getFunction();
		if (func.isSelector() ) {
			return applicationTerm.getParameters()[0];
		} else if (func.isConstructor()){
			for (Term t : applicationTerm.getParameters()) {
				if ( t == term) {
					return t;
				}
			}
		}
		return null;
	}
	 */
	
	// returns the fitting selector
	private String getSelector(FunctionSymbol constructorSymbol, int consTermIndex, int childTermIndex) {
		assert(constructorSymbol.getReturnSort().getSortSymbol().isDatatype());
		DataType datatype = (DataType) constructorSymbol.getReturnSort().getSortSymbol();
		String[] s = datatype.findConstructor(constructorSymbol.getName()).getSelectors();
		Term[] terms = ((ApplicationTerm) mPath[consTermIndex]).getParameters();
		Term child = mPath[childTermIndex];
		for (int i = 0; i < terms.length; i++) {
			// TODO: application term??
			if (child.equals(terms[i])) {
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
	private int getALocalChild(int color, Occurrence occ) {
		int child = color - 1;
		while (child >= mInterpolator.mStartOfSubtrees[color]) {
			// TODO: 
			if (occ.isALocal(child)) {
				return child;
			}
			child = mInterpolator.mStartOfSubtrees[child] - 1;
		}
		return -1;
	}
	
}



// TODO: empty interpolants become true/false
// A-Local testers on B paths
// connect at the end
// open closed paths
// sels / cons
// isC ... 