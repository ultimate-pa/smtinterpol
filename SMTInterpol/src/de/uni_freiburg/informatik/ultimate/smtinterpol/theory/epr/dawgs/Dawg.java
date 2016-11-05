package de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.dawgs;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;
import java.util.SortedSet;

import de.uni_freiburg.informatik.ultimate.smtinterpol.LogProxy;

public class Dawg<LETTER, COLNAMES> extends AbstractDawg<LETTER, COLNAMES> {
	
	/*
	 * convention:
	 * states are just integers
	 * 
	 * the initial state is "0"
	 * the accepting state is <mArity>
	 * the sink state is "-1"
	 */
	
	DawgState mInitialState;
	DawgState mFinalState;
	
//	// TODO: do we need a sink state?
//	DawgState mSinkState;
	
	private boolean mIsEmpty;
	private boolean mIsUniversal;
	
	/**
	 * Transition relation of the finite automaton as a nested map.
	 */
	Map<DawgState, Map<DawgLetter<LETTER, COLNAMES>, DawgState>> mTransitionRelation;

	/**
	 * Create an empty dawg
	 * @param colnames
	 * @param allConstants
	 * @param logger
	 */
	public Dawg(SortedSet<COLNAMES> colnames, Set<LETTER> allConstants, LogProxy logger) {
		super(colnames, allConstants, logger);
		
		/*
		 * create as an empty dawg
		 */
//		addTransition(0, UniversalDawgLetter.INSTANCE, -1);
		
//		mSinkState = new DawgState();
//		mInitialState = mSinkState;
		mInitialState = new DawgState();
		
		mIsUniversal = true;
		mIsEmpty = false;
	}

	


	/**
	 * Creates a dawg that accepts all words of the given signature.
	 * @param colnames
	 * @param allConstants
	 * @param logger
	 * @param fullDawg
	 */
	public Dawg(SortedSet<COLNAMES> colnames, Set<LETTER> allConstants, boolean fullDawg, 
			LogProxy logger, DawgLetterFactory<LETTER, COLNAMES> dawgLetterFactory) {
		super(colnames, allConstants, logger);
		assert fullDawg : "use other constructor for empty dawg";
		
		mInitialState = new DawgState();
		
		DawgState currentState = mInitialState;
		for (int i = 0; i < colnames.size(); i++) {
			DawgState nextState = new DawgState();
			addTransition(currentState, dawgLetterFactory.getUniversalDawgLetter(), nextState);
			currentState = nextState;
		}
		mFinalState = currentState;
		
		mIsUniversal = true;
		mIsEmpty = false;
	}

	/**
	 * Creates a dawg that accepts one word.
	 * @param colnames
	 * @param allConstants
	 * @param logger
	 * @param fullDawg
	 */
	public Dawg(SortedSet<COLNAMES> colnames, Set<LETTER> allConstants, List<LETTER> word, 
			LogProxy logger, 
			DawgLetterFactory<LETTER, COLNAMES> dawgLetterFactory) {
		super(colnames, allConstants, logger);
		
		mInitialState = new DawgState();
		
		DawgState currentState = mInitialState;

		for (int i = 0; i < colnames.size(); i++) {
			DawgState nextState = new DawgState();
			DawgLetter<LETTER, COLNAMES> dl = dawgLetterFactory.createSingletonSetDawgLetter(word.get(i));
			addTransition(currentState, dl, nextState);
			currentState = nextState;
		}
		mFinalState = currentState;
		
		mIsUniversal = false;
		mIsEmpty = false;
	}


	@Override
	public IDawg<LETTER, COLNAMES> intersect(IDawg<LETTER, COLNAMES> fp) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public IDawg<LETTER, COLNAMES> union(IDawg<LETTER, COLNAMES> other) {
		return new UnionDawgBuilder<LETTER, COLNAMES>(
				this, 
				(Dawg<LETTER, COLNAMES>) other
					).build();
	}




	@Override
	public IDawg<LETTER, COLNAMES> complement() {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public boolean accepts(List<LETTER> word) {
		DawgState currentState = mInitialState;
		for (LETTER ltr : word) {
			if (currentState == mFinalState) {
				assert word.lastIndexOf(ltr) == word.size() - 1 : "we haven't read the word completely "
						+ "but accept, this is unforseen";
				return true;
			}
			DawgState nextState = makeTransition(currentState, ltr, word);
			if (nextState == null) {
				return false;
			}
			currentState = nextState;
		}
		return false;
	}
	
	private void addTransition(DawgState source, DawgLetter<LETTER, COLNAMES> dawgLetter, DawgState target) {
		Map<DawgLetter<LETTER, COLNAMES>, DawgState> letterToTarget = mTransitionRelation.get(source);
		if (letterToTarget == null) {
			letterToTarget = new HashMap<DawgLetter<LETTER, COLNAMES>, DawgState>();
			mTransitionRelation.put(source, letterToTarget);
		}
		letterToTarget.put(dawgLetter, target);
	}

	private DawgState makeTransition(DawgState source, LETTER ltr, List<LETTER> word) {
		Map<DawgLetter<LETTER, COLNAMES>, DawgState> letterToTarget = mTransitionRelation.get(source);
		if (letterToTarget == null) {
			// source state has no outgoing edges
			return null;
		}
		// look for an outgoing edge with a DawgLetter that matches ltr
		for (Entry<DawgLetter<LETTER, COLNAMES>, DawgState> en : letterToTarget.entrySet()) {
			DawgLetter<LETTER, COLNAMES> dl = en.getKey();
			if (dl.matches(ltr, word, mColNameToIndex)) {
				// dl allows a transition with ltr
				return en.getValue();
			}
		}
		// could not find a viable transition
		return null;
	}

	@Override
	public boolean isEmpty() {
		return mIsEmpty;
	}

	@Override
	public boolean isUniversal() {
		return mIsUniversal;
	}

	@Override
	public void add(List<LETTER> arguments) {
		// TODO Auto-generated method stub
	
	}

	@Override
	public IDawg<LETTER, COLNAMES> select(Map<COLNAMES, LETTER> selectMap) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	protected Iterable<List<LETTER>> listPoints() {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Iterator<List<LETTER>> iterator() {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public boolean isSingleton() {
		// TODO Auto-generated method stub
		return false;
	}

	@Override
	public boolean supSetEq(IDawg<LETTER, COLNAMES> points) {
		// TODO Auto-generated method stub
		return false;
	}

	@Override
	public IDawg<LETTER, COLNAMES> translatePredSigToClauseSig(Map<COLNAMES, Object> translation,
			SortedSet<COLNAMES> targetSignature) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public IDawg<LETTER, COLNAMES> translateClauseSigToPredSig(Map<COLNAMES, COLNAMES> translation,
			List<Object> argList, SortedSet<COLNAMES> newSignature) {
		// TODO Auto-generated method stub
		return null;
	}




	@Override
	public IDawg<LETTER, COLNAMES> difference(IDawg<LETTER, COLNAMES> other) {
		// TODO Auto-generated method stub
		return null;
	}
}

class UnionDawgBuilder<LETTER, COLNAMES> {
	
	DawgState mUnionInitialState;
	
	Map<DawgState, Map<DawgLetter<LETTER, COLNAMES>, DawgState>> mUnionTransitionRelation;

	UnionDawgBuilder(Dawg<LETTER, COLNAMES> first, Dawg<LETTER, COLNAMES> second) {
		assert first.mColNames.equals(second.mColNames) : "signatures don't match!";

		mUnionInitialState = new PairDawgState(first.mInitialState, second.mInitialState);
		
		
		
		
		Set<PairDawgState> currentStates = new HashSet<PairDawgState>();
		currentStates.add((PairDawgState) mUnionInitialState);
		
		for (int i = 0; i < first.getColnames().size(); i++) {
//			DawgState nextState = new DawgState();
//			addTransition(currentState, UniversalDawgLetter.INSTANCE, nextState);
//			currentState = nextState;
			Set<PairDawgState> nextStates = new HashSet<PairDawgState>();
			
			for (PairDawgState cs : currentStates) {
				Map<DawgLetter<LETTER, COLNAMES>, DawgState> firstLetterToTarget = first.mTransitionRelation.get(cs.getFirst());
				Map<DawgLetter<LETTER, COLNAMES>, DawgState> secondLetterToTarget = second.mTransitionRelation.get(cs.getSecond());
				
				for (Entry<DawgLetter<LETTER, COLNAMES>, DawgState> firstEn : firstLetterToTarget.entrySet()) {
					DawgLetter<LETTER, COLNAMES> firstDl = firstEn.getKey();
					for (Entry<DawgLetter<LETTER, COLNAMES>, DawgState> secondEn : firstLetterToTarget.entrySet()) {
						DawgLetter<LETTER, COLNAMES> secondDl = secondEn.getKey();
						
						DawgLetter<LETTER, COLNAMES> intersection;
						DawgLetter<LETTER, COLNAMES> firstWithoutSecond;
						DawgLetter<LETTER, COLNAMES> secondWithoutFirst;
						
						boolean disjoint = false;
						boolean equal = false;
						boolean firstProperSubsetOfSecond = false;
						boolean secondProperSubsetOfFirst = false;

						if (disjoint) {
							
							
							
							
						} else if (equal) {
							
						} else if (firstProperSubsetOfSecond) {

						} else if (secondProperSubsetOfFirst) {
							
						} else {
							assert false : "forgot a case?";
							
						}
					}
				}
			}
		}
		
	}
	
	Dawg<LETTER, COLNAMES> build() {
		return null;
	}
}
