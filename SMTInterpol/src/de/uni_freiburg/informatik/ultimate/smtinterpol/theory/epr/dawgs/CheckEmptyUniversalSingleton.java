package de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.dawgs;

import java.util.HashSet;
import java.util.List;
import java.util.Set;


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

	private final DawgState mInitialState;
	private final DeterministicDawgTransitionRelation<DawgState, IDawgLetter<LETTER, COLNAMES>, DawgState> mTransitionRelation;
	private final DawgFactory<LETTER, COLNAMES> mDawgFactory;
	private final DawgSignature<COLNAMES> mSignature;

	public CheckEmptyUniversalSingleton(DawgFactory<LETTER, COLNAMES> dawgFactory, 
			DawgState initialState,	
			DeterministicDawgTransitionRelation<DawgState, IDawgLetter<LETTER, COLNAMES>, DawgState> transitionRelation,
			DawgSignature<COLNAMES> signature) {
		mDawgFactory = dawgFactory;
		mInitialState =initialState;
		mTransitionRelation = transitionRelation;
		mSignature = signature;
		check();
	}

	private void check() {
				
		Set<DawgState> currentStates = new HashSet<DawgState>();
		currentStates.add(mInitialState);
		
		mIsUniversal = true;
		
		for (int i = 0; i < mSignature.getNoColumns(); i++) {
			final Set<DawgState> newCurrentStates = new HashSet<DawgState>();
			for (DawgState cs : currentStates) {
			
				final Set<IDawgLetter<LETTER, COLNAMES>> outLetters = new HashSet<IDawgLetter<LETTER,COLNAMES>>();

				for (Pair<IDawgLetter<LETTER, COLNAMES>, DawgState> outEdge : 
					mTransitionRelation.getOutEdgeSet(cs)) {
					
					outLetters.add(outEdge.getFirst());
					newCurrentStates.add(outEdge.getSecond());
				}
				
				if (!mDawgFactory.getDawgLetterFactory().isUniversal(outLetters)) {
					mIsUniversal = false;
				}
				
			}
			currentStates = newCurrentStates;
		}
		
		if (isUniversal()) {
			mIsEmpty = false;
			mIsSingleton = false;
			return;
		}
		
		/*
		 * emptiness and being singleton can be checked easily using the iterator.
		 */
		final DawgIterator<LETTER, COLNAMES> it = 
				new DawgIterator<LETTER, COLNAMES>(mTransitionRelation, mInitialState, mSignature);
		if (!it.hasNext()) {
			mIsEmpty = true;
			mIsSingleton = false;
			return;
		} else {
			mIsEmpty = false;
		}
		final List<LETTER> firstWord = it.next();
		assert firstWord != null;
		assert firstWord.size() == mSignature.getNoColumns();
		if (it.hasNext()) {
			mIsSingleton = false;
		} else {
			mIsSingleton = true;
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
