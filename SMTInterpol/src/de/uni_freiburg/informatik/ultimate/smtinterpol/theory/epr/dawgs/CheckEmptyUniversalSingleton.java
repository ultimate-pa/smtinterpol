package de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.dawgs;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;


public class CheckEmptyUniversalSingleton<LETTER, COLNAMES> {


	private boolean mIsEmpty;
	private boolean mIsSingleton;
	private boolean mIsUniversal;

	private final Set<LETTER> mAllConstants;
	private final int mNoColumns;
	private final DawgState mInitialState;
	private final NestedMap2<DawgState, IDawgLetter<LETTER, COLNAMES>, DawgState> mTransitionRelation;
	private final DawgFactory<LETTER, COLNAMES> mDawgFactory;
	
//	private final Map<DawgState, Pair<DawgState, IDawgLetter<LETTER, COLNAMES>>> mDawgStateToVisitedInEdge = 
//			new HashMap<DawgState, Pair<DawgState,IDawgLetter<LETTER,COLNAMES>>>();
	
	Set<List<IDawgLetter<LETTER,COLNAMES>>> mVisitedSuffixes = new HashSet<List<IDawgLetter<LETTER,COLNAMES>>>();
	

	public CheckEmptyUniversalSingleton(DawgFactory<LETTER, COLNAMES> dawgFactory, Set<LETTER> allConstants, int size, 
			DawgState initialState,	NestedMap2<DawgState, IDawgLetter<LETTER, COLNAMES>, DawgState> transitionRelation) {
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
		final DawgState finalState = finalStates.iterator().next();

		boolean foundSingletonPath = false;
		// iteratively reconstruct paths from initial state to final state
		while (true) {
			
			List<IDawgLetter<LETTER, COLNAMES>> path = samplePath(finalState);

			if (path == null && foundSingletonPath) {
				return true;
			}
			if (path != null && foundSingletonPath) {
				return false;
			}
			
			if (isPathSingleton(path)) {
				foundSingletonPath = true;
			} else {
				return false;
			}
		}
	}

	private boolean isPathSingleton(List<IDawgLetter<LETTER, COLNAMES>> path) {
		if (mDawgFactory.getDawgLetterFactory().useSimpleDawgLetters()) {
			for (IDawgLetter<LETTER, COLNAMES> ltr : path) {
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
	 * Convention: the sampled path is in reverse order, i.e., goes from final to initial state.
	 * @param finalState
	 * @return
	 */
	private List<IDawgLetter<LETTER, COLNAMES>> samplePath(DawgState finalState) {
		DawgState currentState = finalState;
		List<IDawgLetter<LETTER, COLNAMES>> currentSuffix = new ArrayList<IDawgLetter<LETTER,COLNAMES>>();

		while (true) {

			boolean foundNewSuffix = false;
			for (Pair<DawgState, IDawgLetter<LETTER, COLNAMES>> inEdge : mTransitionRelation.getInverse(finalState)) {
				List<IDawgLetter<LETTER, COLNAMES>> hypotheticNewSuffix = 
						new ArrayList<IDawgLetter<LETTER,COLNAMES>>(currentSuffix);
				hypotheticNewSuffix.add(inEdge.getSecond());
				if (!mVisitedSuffixes.contains(hypotheticNewSuffix)) {
					currentSuffix = hypotheticNewSuffix;
					currentState = inEdge.getFirst();
					mVisitedSuffixes.add(currentSuffix);
					foundNewSuffix = true;
				}
			}
			
			if (!foundNewSuffix) {
				return null;
			}
			
			if (currentState.equals(mInitialState)) {
				return currentSuffix;
			}

		}
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
