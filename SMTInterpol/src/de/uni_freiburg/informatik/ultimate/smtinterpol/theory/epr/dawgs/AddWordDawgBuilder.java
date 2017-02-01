package de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.dawgs;

import java.util.List;
import java.util.Map.Entry;

public class AddWordDawgBuilder<LETTER, COLNAMES> {

	private final DawgFactory<LETTER, COLNAMES> mDawgFactory;
	private final Dawg<LETTER, COLNAMES> mInputDawg;
	private final List<LETTER> mWordToAdd;
	private NestedMap2<DawgState, DawgLetter<LETTER, COLNAMES>, DawgState> mNewTransitionRelation;

	public AddWordDawgBuilder(DawgFactory<LETTER, COLNAMES> dawgFactory, Dawg<LETTER, COLNAMES> dawg,
			List<LETTER> word) {
		mDawgFactory = dawgFactory;
		mInputDawg = dawg;
		mWordToAdd = word;
		addWord();
	}

	private void addWord() {
		DawgState currentState = mInputDawg.getInitialState();
		for (LETTER letter : mWordToAdd) {
			for (Entry<DawgLetter<LETTER, COLNAMES>, DawgState> outEdge : 
				mInputDawg.getTransitionRelation().get(currentState).entrySet()) {
				if (outEdge.getKey().matches(letter, mWordToAdd, mInputDawg.getColNameToIndex())) {
					// we already have a transition for the current letter
					// (assumption: the Dawg is deterministic in the sense that outgoing DawgLetters of one 
					//  state don't intersect)
					currentState = outEdge.getValue();
				} else {
					// we need a fresh transition (effectively building one fresh "tail" for the dawg for
					// the given word suffix..
					
					final DawgState newState = mDawgFactory.getDawgStateFactory().createDawgState();
					final DawgLetter<LETTER, COLNAMES> newLetter = mDawgFactory.getDawgLetterFactory()
							.createSingletonSetDawgLetter(letter);
					mNewTransitionRelation.put(currentState, newLetter, newState);
					currentState = newState;
				}
			}
			
		}
		
	}

	public Dawg<LETTER, COLNAMES> build() {
		assert mNewTransitionRelation != null;
		return new Dawg<LETTER, COLNAMES>(mDawgFactory, 
				mInputDawg.getColnames(), mInputDawg.getAllConstants(), 
				mInputDawg.getLogger(), mNewTransitionRelation, mInputDawg.getInitialState());
	}

}
