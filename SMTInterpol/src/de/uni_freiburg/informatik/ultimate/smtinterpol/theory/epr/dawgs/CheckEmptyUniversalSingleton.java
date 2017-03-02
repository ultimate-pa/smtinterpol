package de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.dawgs;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.Stack;

import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.BinaryRelation;


/**
 * Given a transition relation and an initial state, checks if the corresponding Dawg is
 *  - empty
 *  - universal
 *  - a singleton (i.e. accepts exactly one word)
 * 
 * @author Alexander Nutz (nutz@informatik.uni-freiburg.de)
 *
 * @param <LETTER>
 * @param <COLNAMES>
 */
public class CheckEmptyUniversalSingleton<LETTER, COLNAMES> {


	private boolean mIsEmpty;
	private boolean mIsSingleton;
	private boolean mIsUniversal;

	private final Set<LETTER> mAllConstants;
	private final int mNoColumns;
	private final DawgState mInitialState;
	private final DeterministicDawgTransitionRelation<DawgState, IDawgLetter<LETTER, COLNAMES>, DawgState> mTransitionRelation;
	private final DawgFactory<LETTER, COLNAMES> mDawgFactory;
	
//	private final Map<DawgState, Pair<DawgState, IDawgLetter<LETTER, COLNAMES>>> mDawgStateToVisitedInEdge = 
//			new HashMap<DawgState, Pair<DawgState,IDawgLetter<LETTER,COLNAMES>>>();
	
	
	Stack<DawgState> mSamplePathOpenStates = new Stack<DawgState>();
	Set<DawgState> mSamplePathVisitedStates = new HashSet<DawgState>();
	
	BinaryRelation<DawgState, List<IDawgLetter<LETTER,COLNAMES>>> mOpenStateToPaths = 
			new BinaryRelation<DawgState, List<IDawgLetter<LETTER,COLNAMES>>>();
	
	Set<List<IDawgLetter<LETTER,COLNAMES>>> mSampledPaths = new HashSet<List<IDawgLetter<LETTER,COLNAMES>>>();
	Set<List<IDawgLetter<LETTER,COLNAMES>>> mVisitedSuffixes = new HashSet<List<IDawgLetter<LETTER,COLNAMES>>>();
	

	public CheckEmptyUniversalSingleton(DawgFactory<LETTER, COLNAMES> dawgFactory, Set<LETTER> allConstants, int size, 
			DawgState initialState,	DeterministicDawgTransitionRelation<DawgState, IDawgLetter<LETTER, COLNAMES>, DawgState> transitionRelation) {
		mDawgFactory = dawgFactory;
		mAllConstants = allConstants;
		mNoColumns = size;
		mInitialState =initialState;
		mTransitionRelation = transitionRelation;
		check();
	}

	private void check() {
				
		Set<DawgState> currentStates = new HashSet<DawgState>();
		currentStates.add(mInitialState);
		
		mIsUniversal = true;
		
		for (int i = 0; i < mNoColumns; i++) {
			final Set<DawgState> newCurrentStates = new HashSet<DawgState>();
			for (DawgState cs : currentStates) {
			
				final Set<IDawgLetter<LETTER, COLNAMES>> outLetters = new HashSet<IDawgLetter<LETTER,COLNAMES>>();

				for (Pair<IDawgLetter<LETTER, COLNAMES>, DawgState> outEdge : 
					mTransitionRelation.getOutEdgeSet(cs)) {
					
					outLetters.add(outEdge.getFirst());
					newCurrentStates.add(outEdge.getSecond());
				}
				
				if (!DawgLetterFactory.isUniversal(outLetters, mAllConstants)) {
					mIsUniversal = false;
				}
				
			}
			
			if (i == mNoColumns - 1) {
				/*
				 * by construction all states in newCurrentStates are reachable from the initial state
				 *  --> the language is empty iff those are empty after visiting the last column
				 */
				if (newCurrentStates.isEmpty()) {
					assert mIsUniversal == false;
					mIsEmpty = true;
					mIsSingleton = false;
				} else {
					mIsEmpty = false;
					// check if we have a singleton
					mIsSingleton = checkSingleton(newCurrentStates);
				}
			}
			currentStates = newCurrentStates;
		}
	}

	private boolean checkSingleton(Set<DawgState> finalStates) {
		if (finalStates.size() != 1) {
			return false;
		}
//		final DawgState finalState = finalStates.iterator().next();

		boolean foundSingletonPathBefore = false;
		
		
		for (DawgState finalState : finalStates) {
			mSamplePathOpenStates.add(finalState);
			mOpenStateToPaths.addPair(finalState, new ArrayList<IDawgLetter<LETTER,COLNAMES>>());
		}

		
		// iteratively reconstruct paths from initial state to final state
		while (true) {
			
			List<IDawgLetter<LETTER, COLNAMES>> path = samplePath();

			if (path == null && !foundSingletonPathBefore) {
				return false;
			}
			if (path == null && foundSingletonPathBefore) {
				return true;
			}
			if (path != null && foundSingletonPathBefore) {
				return false;
			}
			
			if (isPathSingleton(path)) {
				foundSingletonPathBefore = true;
			} else {
				return false;
			}
		}
	}

	private boolean isPathSingleton(List<IDawgLetter<LETTER, COLNAMES>> path) {
		if (mDawgFactory.getDawgLetterFactory().useSimpleDawgLetters()) {
			for (IDawgLetter<LETTER, COLNAMES> ltr : path) {
				assert !(ltr instanceof EmptyDawgLetter);
				if (ltr instanceof UniversalDawgLetter) {
					return false;
				}
				SimpleDawgLetter<LETTER, COLNAMES> sdl = (SimpleDawgLetter<LETTER, COLNAMES>) ltr;
				if (sdl.getLetters().size() != 1) {
					return false;
				}
			}
			return true;
		} else {
			// TODO
			assert false : "TODO";
			return false;
		}
	}

	/**
	 * At each call looks for a fresh (not yet returned) path trough the graph from a final state to 
	 * the initial state.
	 * 
	 * Convention: the sampled path is in reverse order, i.e., goes from final to initial state.
	 * @param finalState
	 * @return A path from final to initial state, that has not yet been returned, null if there is none.
	 * 
	 * 
	 * TODO: simplify this once Dawg.iterator() works!
	 */
	private List<IDawgLetter<LETTER, COLNAMES>> samplePath() {

		while (!mSamplePathOpenStates.isEmpty()) {
			DawgState currentState = mSamplePathOpenStates.pop();
			
			if (currentState.equals(mInitialState)) {
				 for (List<IDawgLetter<LETTER, COLNAMES>> path : mOpenStateToPaths.getImage(mInitialState)) {
					 if (mSampledPaths.contains(path)) {
						 continue;
					 }
					 mSampledPaths.add(path);
					 return path;
				 }
				 continue;
			}

			for (Pair<DawgState, IDawgLetter<LETTER, COLNAMES>> inEdge : mTransitionRelation.getInverse(currentState)) {

				final DawgState targetState = inEdge.getFirst();
			
				boolean foundNewSuffix = false;
				for (List<IDawgLetter<LETTER, COLNAMES>> path : mOpenStateToPaths.getImage(currentState)) {
					List<IDawgLetter<LETTER, COLNAMES>> newPath = new ArrayList<IDawgLetter<LETTER, COLNAMES>>(path);
					newPath.add(inEdge.getSecond());

					if (!mVisitedSuffixes.contains(newPath)) {
						mOpenStateToPaths.addPair(targetState, newPath);
						foundNewSuffix = true;
					}
				}
				if (foundNewSuffix) {
					mSamplePathOpenStates.push(targetState);
				}
			}
			
			mSamplePathVisitedStates.add(currentState);
		}
		return null;
	}

	public boolean isEmpty() {
		return mIsEmpty;
	}

	public boolean isSingleton() {
		return mIsSingleton;
	}

	public boolean isUniversal() {
		return mIsUniversal;
	}
}
