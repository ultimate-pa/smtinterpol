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
//	DawgState mFinalState;
	
//	// TODO: do we need a sink state?
//	DawgState mSinkState;
	
	private boolean mIsEmpty;
	private boolean mIsUniversal;
	
	private final DawgStateFactory mDawgStateFactory;
	
	/**
	 * Transition relation of the finite automaton as a nested map.
	 */
	private final Map<DawgState, Map<DawgLetter<LETTER, COLNAMES>, DawgState>> mTransitionRelation;
	
	/**
	 * Create an empty dawg
	 * @param colnames
	 * @param allConstants
	 * @param logger
	 */
	public Dawg(SortedSet<COLNAMES> colnames, Set<LETTER> allConstants, LogProxy logger, DawgStateFactory dsf) {
		super(colnames, allConstants, logger);
		mDawgStateFactory = dsf;
		
		mTransitionRelation = new HashMap<DawgState, Map<DawgLetter<LETTER,COLNAMES>,DawgState>>();
		
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
			LogProxy logger, DawgLetterFactory<LETTER, COLNAMES> dawgLetterFactory, DawgStateFactory dsf) {
		super(colnames, allConstants, logger);
		assert fullDawg : "use other constructor for empty dawg";
		mDawgStateFactory = dsf;
		
		mInitialState = new DawgState();

		mTransitionRelation = new HashMap<DawgState, Map<DawgLetter<LETTER,COLNAMES>,DawgState>>();
		
		DawgState currentState = mInitialState;
		for (int i = 0; i < colnames.size(); i++) {
			DawgState nextState = new DawgState();
			addTransition(currentState, dawgLetterFactory.getUniversalDawgLetter(), nextState);
			currentState = nextState;
		}
//		mFinalState = currentState;
		
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
			DawgLetterFactory<LETTER, COLNAMES> dawgLetterFactory, DawgStateFactory dsf) {
		super(colnames, allConstants, logger);
		
		mDawgStateFactory = dsf;

		mTransitionRelation = new HashMap<DawgState, Map<DawgLetter<LETTER,COLNAMES>,DawgState>>();

		mInitialState = new DawgState();
		
		DawgState currentState = mInitialState;

		for (int i = 0; i < colnames.size(); i++) {
			DawgState nextState = new DawgState();
			DawgLetter<LETTER, COLNAMES> dl = dawgLetterFactory.createSingletonSetDawgLetter(word.get(i));
			addTransition(currentState, dl, nextState);
			currentState = nextState;
		}
//		mFinalState = currentState;
		
		mIsUniversal = false;
		mIsEmpty = false;
	}
	
	Dawg(SortedSet<COLNAMES> colnames, Set<LETTER> allConstants, 
			LogProxy logger, 
			DawgStateFactory dsf, 
			Map<DawgState, Map<DawgLetter<LETTER, COLNAMES>, DawgState>> tr) {
		super(colnames, allConstants, logger);
		mDawgStateFactory = dsf;
		mTransitionRelation = tr;

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
		return new UnionDawgBuilder<LETTER, COLNAMES>(this, (Dawg<LETTER, COLNAMES>) other,	mDawgStateFactory).build();
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
			DawgState nextState = makeTransition(currentState, ltr, word);
			if (nextState == null) {
				return false;
			}
			currentState = nextState;
		}
		//we have read the complete word
		assert currentState != null;
		return true;
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
		Set<DawgState> currentColnamesPrestates = new HashSet<DawgState>();
		currentColnamesPrestates.add(mInitialState);
		for (COLNAMES cn : getColnames()) {
			
			Set<DawgState> newCurrentColnamesPrestates = new HashSet<DawgState>();
			for (DawgState ccp : currentColnamesPrestates) {
				Map<DawgLetter<LETTER, COLNAMES>, DawgState> letterToState = mTransitionRelation.get(ccp);

				Map<DawgLetter<LETTER, COLNAMES>, DawgState> newLetterToState = 
						new HashMap<DawgLetter<LETTER,COLNAMES>, DawgState>();

				if (letterToState == null) {
					continue;
				}
				
				for (Entry<DawgLetter<LETTER, COLNAMES>, DawgState> lts : letterToState.entrySet()) {
					LETTER selectLetter = selectMap.get(cn);
					if (selectLetter == null) {
						// no select constraint 
						// --> retain all transition and get the states before the next column
						newLetterToState.put(lts.getKey(), lts.getValue());
						newCurrentColnamesPrestates.add(lts.getValue());
					} else {
						// we have a select constraint
						// --> Dawg edges that don't allow the select letter are removed
						// --> Dawg edges that allow the select letter are constrained to only that letter; (un)equals
						//   constraints remain untouched for those
						DawgLetter<LETTER, COLNAMES> dawgLetter = lts.getKey();
						
						DawgLetter<LETTER, COLNAMES> restrictedDL = dawgLetter.restrictToLetter(selectLetter);

						if (restrictedDL == null) {
							// dawgLetter does not allow transitions with selectLetter
							// --> omit transition
						} else {
							// dawgLetter does allow transitions with selectLetter
							// --> replace the label of the transition by the restricted letter
							newLetterToState.put(restrictedDL, lts.getValue());
							newCurrentColnamesPrestates.add(lts.getValue());
						}
					}
				}
				mTransitionRelation.put(ccp, newLetterToState);
			}
			currentColnamesPrestates = newCurrentColnamesPrestates;
		}
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
	
	Map<DawgState, Map<DawgLetter<LETTER, COLNAMES>, DawgState>> getTransitionRelation() {
		return mTransitionRelation;
	}
	
	Set<LETTER> getAllConstants() { 
		return mAllConstants;
	}
	
	LogProxy getLogger() {
		return mLogger;
	}
}

class UnionDawgBuilder<LETTER, COLNAMES> {
	
	private final DawgState mUnionInitialState;
	
	private final DawgStateFactory mDawgStateFactory;
	
	private Map<DawgState, Map<DawgLetter<LETTER, COLNAMES>, DawgState>> mUnionTransitionRelation;

	private Map<DawgState, Map<DawgLetter<LETTER, COLNAMES>, DawgState>> mTransitionRelation;

	private final Dawg<LETTER, COLNAMES> mFirst;
	private final Dawg<LETTER, COLNAMES> mSecond;

	UnionDawgBuilder(Dawg<LETTER, COLNAMES> first, Dawg<LETTER, COLNAMES> second, DawgStateFactory dsf) {
		assert first.mColNames.equals(second.mColNames) : "signatures don't match!";
		
		mDawgStateFactory = dsf;
		
		mFirst = first; 
		mSecond = second;
		
		mTransitionRelation = new HashMap<DawgState, Map<DawgLetter<LETTER,COLNAMES>,DawgState>>();

		mUnionInitialState = new PairDawgState(first.mInitialState, second.mInitialState);
		
	}
	
	Dawg<LETTER, COLNAMES> build() {
		Set<PairDawgState> currentStates = new HashSet<PairDawgState>();
		currentStates.add((PairDawgState) mUnionInitialState);
		
		for (int i = 0; i < mFirst.getColnames().size(); i++) {
			Set<PairDawgState> nextStates = new HashSet<PairDawgState>();
			
			for (PairDawgState cs : currentStates) {
				
				if (!cs.mFirstIsSink && !cs.mSecondIsSink) {
					Map<DawgLetter<LETTER, COLNAMES>, DawgState> firstLetterToTarget = 
							mFirst.getTransitionRelation().get(cs.getFirst());
					Map<DawgLetter<LETTER, COLNAMES>, DawgState> secondLetterToTarget = 
							mSecond.getTransitionRelation().get(cs.getSecond());

					for (Entry<DawgLetter<LETTER, COLNAMES>, DawgState> firstEn : firstLetterToTarget.entrySet()) {
						DawgLetter<LETTER, COLNAMES> firstDl = firstEn.getKey();
						for (Entry<DawgLetter<LETTER, COLNAMES>, DawgState> secondEn : secondLetterToTarget.entrySet()) {
							DawgLetter<LETTER, COLNAMES> secondDl = secondEn.getKey();

							DawgLetter<LETTER, COLNAMES> intersectionDl = firstDl.intersect(secondDl);

							if (intersectionDl != null && !(intersectionDl instanceof EmptyDawgLetter)) {
								// dawgletters do intersect --> add transition and new state
								PairDawgState newState = mDawgStateFactory.createPairDawgState(
										firstEn.getValue(), secondEn.getValue());

								nextStates.add(newState);
								addTransition(cs, intersectionDl, newState);
							}

							Set<DawgLetter<LETTER, COLNAMES>> firstWithoutSecondDls = firstDl.difference(secondDl);
							if (!firstWithoutSecondDls.isEmpty()) {
								PairDawgState fwsDs = mDawgStateFactory.createPairDawgState(firstEn.getValue(), false, true);
								nextStates.add(fwsDs);
								for (DawgLetter<LETTER, COLNAMES> dl : firstWithoutSecondDls) {
									addTransition(cs, dl, fwsDs);
								}
							}

							Set<DawgLetter<LETTER, COLNAMES>> secondWithoutFirstDls = secondDl.difference(firstDl);
							if (!secondWithoutFirstDls.isEmpty()) {
								PairDawgState swfDs = new PairDawgState(secondEn.getValue(), true, false);
								nextStates.add(swfDs);
								for (DawgLetter<LETTER, COLNAMES> dl : secondWithoutFirstDls) {
									addTransition(cs, dl, swfDs);
								}
							}
						}
					}
				} else if (cs.mFirstIsSink) {
					Map<DawgLetter<LETTER, COLNAMES>, DawgState> firstLetterToTarget = 
							mFirst.getTransitionRelation().get(cs.getFirst());
					for (Entry<DawgLetter<LETTER, COLNAMES>, DawgState> firstEn : firstLetterToTarget.entrySet()) {
						PairDawgState ds = mDawgStateFactory.createPairDawgState(firstEn.getValue(), true, false);
						nextStates.add(ds);
						addTransition(cs, firstEn.getKey(), ds);
					}
				} else if (cs.mSecondIsSink) {
					Map<DawgLetter<LETTER, COLNAMES>, DawgState> secondLetterToTarget = 
							mSecond.getTransitionRelation().get(cs.getSecond());
					for (Entry<DawgLetter<LETTER, COLNAMES>, DawgState> secondEn : secondLetterToTarget.entrySet()) {
						PairDawgState ds = mDawgStateFactory.createPairDawgState(secondEn.getValue(), false, true);
						nextStates.add(ds);
						addTransition(cs, secondEn.getKey(), ds);
					}
				}
			}
			currentStates = nextStates;
		}
		
		return new Dawg<LETTER, COLNAMES>(mFirst.getColnames(), mFirst.getAllConstants(), 
				mFirst.getLogger(), mDawgStateFactory, mTransitionRelation);
	}
	
	private void addTransition(DawgState source, DawgLetter<LETTER, COLNAMES> dawgLetter, DawgState target) {
		Map<DawgLetter<LETTER, COLNAMES>, DawgState> letterToTarget = mTransitionRelation.get(source);
		if (letterToTarget == null) {
			letterToTarget = new HashMap<DawgLetter<LETTER, COLNAMES>, DawgState>();
			mTransitionRelation.put(source, letterToTarget);
		}
		letterToTarget.put(dawgLetter, target);
	}
}
