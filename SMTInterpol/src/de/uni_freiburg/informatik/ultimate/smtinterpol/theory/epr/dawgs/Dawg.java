package de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.dawgs;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;
import java.util.SortedSet;
import java.util.TreeSet;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
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
//	private final Map<DawgState, Map<DawgLetter<LETTER, COLNAMES>, DawgState>> mTransitionRelation;
	private final NestedMap2<DawgState, DawgLetter<LETTER, COLNAMES>, DawgState> mTransitionRelation;
	
	private final DawgLetterFactory<LETTER, COLNAMES> mDawgLetterFactory;
	private final DawgFactory<LETTER, COLNAMES> mDawgFactory;
	
	/**
	 * Create an empty dawg
	 * @param colnames
	 * @param allConstants
	 * @param logger
	 */
	public Dawg(SortedSet<COLNAMES> colnames, Set<LETTER> allConstants, LogProxy logger, 
			DawgFactory<LETTER, COLNAMES> df) {
		super(colnames, allConstants, logger);
		mDawgFactory = df;
		mDawgStateFactory = df.getDawgStateFactory();
		mDawgLetterFactory = df.getDawgLetterFactory();
		
//		mTransitionRelation = new HashMap<DawgState, Map<DawgLetter<LETTER,COLNAMES>,DawgState>>();
		mTransitionRelation = new NestedMap2<DawgState, DawgLetter<LETTER,COLNAMES>,DawgState>();
		
		mInitialState =  mDawgStateFactory.createDawgState();
		
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
			LogProxy logger, DawgFactory<LETTER, COLNAMES> df) {
		super(colnames, allConstants, logger);
		assert fullDawg : "use other constructor for empty dawg";
		mDawgFactory = df;
		mDawgStateFactory = df.getDawgStateFactory();
		mDawgLetterFactory = df.getDawgLetterFactory();
		
		mInitialState = mDawgStateFactory.createDawgState();

		mTransitionRelation = new NestedMap2<DawgState, DawgLetter<LETTER,COLNAMES>,DawgState>();
		
		DawgState currentState = mInitialState;
		for (int i = 0; i < colnames.size(); i++) {
			DawgState nextState = mDawgStateFactory.createDawgState();
//			addTransition(currentState, mDawgLetterFactory.getUniversalDawgLetter(), nextState);
			mTransitionRelation.put(currentState, mDawgLetterFactory.getUniversalDawgLetter(), nextState);
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
			DawgFactory<LETTER, COLNAMES> df) {
//			DawgLetterFactory<LETTER, COLNAMES> dawgLetterFactory, DawgStateFactory dsf) {
		super(colnames, allConstants, logger);
		
		mDawgFactory = df;
		mDawgStateFactory = df.getDawgStateFactory();
		mDawgLetterFactory = df.getDawgLetterFactory();
	
//		mDawgStateFactory = dsf;
//		mDawgLetterFactory = dawgLetterFactory;

		mTransitionRelation = new NestedMap2<DawgState, DawgLetter<LETTER,COLNAMES>,DawgState>();

		mInitialState =  mDawgStateFactory.createDawgState();
		
		DawgState currentState = mInitialState;

		for (int i = 0; i < colnames.size(); i++) {
			DawgState nextState =  mDawgStateFactory.createDawgState();
			DawgLetter<LETTER, COLNAMES> dl = mDawgLetterFactory.createSingletonSetDawgLetter(word.get(i));
//			addTransition(currentState, dl, nextState);
			mTransitionRelation.put(currentState, dl, nextState);
			currentState = nextState;
		}
//		mFinalState = currentState;
		
		mIsUniversal = false;
		mIsEmpty = false;
	}
	
	Dawg(SortedSet<COLNAMES> colnames, Set<LETTER> allConstants, 
			LogProxy logger, 
//			Map<DawgState, Map<DawgLetter<LETTER, COLNAMES>, DawgState>> tr, 
			NestedMap2<DawgState, DawgLetter<LETTER, COLNAMES>, DawgState> tr, 
			DawgFactory<LETTER, COLNAMES> df) {
		super(colnames, allConstants, logger);
		
		mDawgFactory = df;
		mDawgStateFactory = df.getDawgStateFactory();
		mDawgLetterFactory = df.getDawgLetterFactory();
	

//		mDawgLetterFactory = dawgLetterFactory;
//		mDawgStateFactory = dsf;
		mTransitionRelation = tr;

		mIsUniversal = false;
		mIsEmpty = false;
	}



	@Override
	public IDawg<LETTER, COLNAMES> intersect(IDawg<LETTER, COLNAMES> other) {
		return new UnionOrIntersectionDawgBuilder<LETTER, COLNAMES>(
				this, (Dawg<LETTER, COLNAMES>) other, mDawgFactory).buildIntersection();
	}

	@Override
	public IDawg<LETTER, COLNAMES> union(IDawg<LETTER, COLNAMES> other) {
		return new UnionOrIntersectionDawgBuilder<LETTER, COLNAMES>(
				this, (Dawg<LETTER, COLNAMES>) other, mDawgFactory).buildUnion();
	}




	/**
	 * Compute and return a Dawg that represents the complement of the input dawg's language.
	 * (in Sigma^n, where Sigma = allConstants and n = |colnames|)
	 */
	@Override
	public IDawg<LETTER, COLNAMES> complement() {
		/*
		 * algorithmic plan:
		 *  - as usual: iterate through state "level by level" (or column by column)
		 *  - in principle this performs a completion of the automaton viewed as a DFA, with some changes:
		 *   -- the complement we want to compute is the complement in Sigma^|colnames|, not Sigma^*
		 *   -- thus we do not introduce loops, instead we have a sink state (which is no more sink after
		 *        complementation) for each level
		 *       the sink state to each level has a UniversalDawgLetter-transition to the sink state in the
		 *       next level
		 *   -- only the "sink state" for the last level becomes an accepting state through complementation
		 */
		
//		final Map<DawgState, Map<DawgLetter<LETTER, COLNAMES>, DawgState>> newTransitionRelation = 
//				new HashMap<DawgState, Map<DawgLetter<LETTER,COLNAMES>,DawgState>>();
		final NestedMap2<DawgState, DawgLetter<LETTER, COLNAMES>, DawgState> newTransitionRelation
				= new NestedMap2<DawgState, DawgLetter<LETTER, COLNAMES>, DawgState>();

		
		
		Set<DawgState> currentStates = new HashSet<DawgState>();
		currentStates.add(mInitialState);
		
		DawgState nextLevelFormerSinkState = null;
		
		
		//TODO:
		// - double check
		
		for (int i = 0; i < this.getColnames().size(); i++) {
			Set<DawgState> nextStates = new HashSet<DawgState>();
			
			DawgState lastLevelFormerSinkState = nextLevelFormerSinkState;
			nextLevelFormerSinkState = mDawgStateFactory.createDawgState();
			nextStates.add(nextLevelFormerSinkState);
//			addTransition(newTransitionRelation, 
//					lastLevelFormerSinkState, mDawgLetterFactory.getUniversalDawgLetter(), nextLevelFormerSinkState);
			newTransitionRelation.put(
					lastLevelFormerSinkState, mDawgLetterFactory.getUniversalDawgLetter(), nextLevelFormerSinkState);

			for (DawgState cs : currentStates) {
				Map<DawgLetter<LETTER, COLNAMES>, DawgState> oldLetterToDawgState = mTransitionRelation.get(cs);

				
				Set<DawgLetter<LETTER, COLNAMES>> outgoingDawgLetters = new HashSet<DawgLetter<LETTER,COLNAMES>>();

				/*
				 * the old transitions stay intact (except for the ones leading to the final state
				 */
				for (Entry<DawgLetter<LETTER, COLNAMES>, DawgState> letterAndState : oldLetterToDawgState.entrySet()) {
					if (i == this.getColnames().size() - 1) {
						// we are in the last column
						// the old transitions lead to the old final state(s)
						// --> omit those
						break;
					}
					outgoingDawgLetters.add(letterAndState.getKey());
					nextStates.add(letterAndState.getValue());
//					addTransition(newTransitionRelation, cs, letterAndState.getKey(), letterAndState.getValue());
					newTransitionRelation.put(cs, letterAndState.getKey(), letterAndState.getValue());
				}
				
				/*
				 * collects all the DawgLetters that do not have a transition from the current state
				 * those lead to the "former sink state"
				 */
				Set<DawgLetter<LETTER, COLNAMES>> complementDawgLetters = 
						mDawgLetterFactory.complementDawgLetterSet(outgoingDawgLetters);
				for (DawgLetter<LETTER, COLNAMES> cdl : complementDawgLetters) {
//					addTransition(newTransitionRelation, cs, cdl, nextLevelFormerSinkState);
					newTransitionRelation.put(cs, cdl, nextLevelFormerSinkState);
				}
	
			}
			currentStates = nextStates;
		}
		
		return new Dawg<LETTER, COLNAMES>(
				mColNames, mAllConstants, mLogger, newTransitionRelation, mDawgFactory);
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
	
//	private void addTransition(DawgState source, DawgLetter<LETTER, COLNAMES> dawgLetter, DawgState target) {
//		addTransition(mTransitionRelation, source, dawgLetter, target);	
//	}
	
//	static <LETTER, COLNAMES> void  addTransition(
////			Map<DawgState, Map<DawgLetter<LETTER, COLNAMES>, DawgState>> transitionRelation, 
//			Map<DawgState, Map<DawgLetter<LETTER, COLNAMES>, DawgState>> transitionRelation, 
//			DawgState source, DawgLetter<LETTER, COLNAMES> dawgLetter, DawgState target) {
//		assert transitionRelation != null;
//		Map<DawgLetter<LETTER, COLNAMES>, DawgState> letterToTarget = transitionRelation.get(source);
//		if (letterToTarget == null) {
//			letterToTarget = new HashMap<DawgLetter<LETTER, COLNAMES>, DawgState>();
//			transitionRelation.put(source, letterToTarget);
//		}
//		letterToTarget.put(dawgLetter, target);
//	}

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

		NestedMap2<DawgState, DawgLetter<LETTER, COLNAMES>, DawgState> newTransitionRelation
			= new NestedMap2<DawgState, DawgLetter<LETTER,COLNAMES>, DawgState>();

		for (COLNAMES cn : getColnames()) {
			
			Set<DawgState> newCurrentColnamesPrestates = new HashSet<DawgState>();
			for (DawgState ccp : currentColnamesPrestates) {
				Map<DawgLetter<LETTER, COLNAMES>, DawgState> letterToState = mTransitionRelation.get(ccp);

//				Map<DawgLetter<LETTER, COLNAMES>, DawgState> newLetterToState = 
//						new HashMap<DawgLetter<LETTER,COLNAMES>, DawgState>();

				if (letterToState == null) {
					continue;
				}
				
				for (Entry<DawgLetter<LETTER, COLNAMES>, DawgState> lts : letterToState.entrySet()) {
					LETTER selectLetter = selectMap.get(cn);
					if (selectLetter == null) {
						// no select constraint 
						// --> retain all transition and get the states before the next column
//						newLetterToState.put(lts.getKey(), lts.getValue());
						newTransitionRelation.put(ccp, lts.getKey(), lts.getValue());
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
//							newLetterToState.put(restrictedDL, lts.getValue());
							newTransitionRelation.put(ccp, restrictedDL, lts.getValue());
							newCurrentColnamesPrestates.add(lts.getValue());
						}
					}
				}
//				mTransitionRelation.a.put(ccp, newLetterToState);
			}
			currentColnamesPrestates = newCurrentColnamesPrestates;
		}
		return new Dawg<LETTER, COLNAMES>(mColNames, mAllConstants, mLogger, newTransitionRelation, mDawgFactory);
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
	public boolean supSetEq(IDawg<LETTER, COLNAMES> other) {
		// TODO: think about optimizations
		return this.complement().intersect(other).isEmpty();
	}

	@SuppressWarnings("unchecked")
	@Override
	public IDawg<LETTER, COLNAMES> translatePredSigToClauseSig(
			Map<COLNAMES, COLNAMES> translationVariables,
			Map<COLNAMES, LETTER> translationConstants,
			SortedSet<COLNAMES> targetSignature) {
		/*
		 * algorithmic plan:
		 *  - basic operations:
		 *    reorder & rename
		 *    select & project
		 *    blowup (or: multiple insert column operations..)
		 */
		Dawg<LETTER, COLNAMES> result = (Dawg<LETTER, COLNAMES>) mDawgFactory.copyDawg(this);
		
		/*
		 * 1. select according to constants in the image of translation
		 */
		result = (Dawg<LETTER, COLNAMES>) result.select(translationConstants);
		
		/*
		 * 2. project selected columns away
		 */
		for (Entry<COLNAMES, LETTER> en : translationConstants.entrySet()) {
			result = (Dawg<LETTER, COLNAMES>) result.projectColumnAway(en.getKey());
		}
		
		/*
		 * 3. reorder Dawg according to variables in the image of translation
		 */
		result = result.reorderAndRename(translationVariables);
		
		return result;
	}

	@Override
	public IDawg<LETTER, COLNAMES> translateClauseSigToPredSig(
			Map<COLNAMES, COLNAMES> translation,
			List<Object> argList, SortedSet<COLNAMES> newSignature) {
		/*
		 * algorithmic plan:
		 *  - basic operations:
		 *   insert column (for constants in argList)
		 *   reorder & rename (match order from argList to order in newSignature)
		 */
	
		Class<? extends Object> colNamesType = newSignature.iterator().next().getClass();
		Dawg<LETTER, COLNAMES> result = (Dawg<LETTER, COLNAMES>) mDawgFactory.copyDawg(this);
		
		// assert new TreeSet<COLNAMES>(translation.values()).equals(newSignature); --> this assertion is wrong
		// because translation does not account for constants (LETTERs) in the argList
		
		
		/*
		 * 1. project away all columns that we do not need (we only need those that occur
		 *  in the ClauseLiteral
		 */
		for (COLNAMES colname : mColNames) {
			if (!translation.containsKey(colname)) {
				assert !argList.contains(colname);
				result = result.projectColumnAway(colname);
			}
		}
		
		/*
		 * 2. reorder an rename the remaining columns
		 */
		result = reorderAndRename(translation);
		
		/*
		 * 3. for the constants in argList: insert a column into the dawg where precisely that constant is 
		 *   accepted.
		 */
		Iterator<COLNAMES> newSigIt = newSignature.iterator();
		for (int i = 0; i < argList.size(); i++) {
			Object arg = argList.get(i);
			COLNAMES newSigColname = newSigIt.next();
			if (colNamesType.isInstance(arg)) {
				// arg is a COLNAME (typically a TermVariable)
				assert newSigColname == translation.get(arg);
			} else {
				// arg must be a LETTER (typically a constant 0-ary ApplicationTerm)
				insertColumn(newSigColname, mDawgLetterFactory.createSingletonSetDawgLetter((LETTER) arg));
			}
		}
		
		return result;
	}
	
	private Dawg<LETTER, COLNAMES> projectColumnAway(
			COLNAMES column) {
		if (!mColNames.contains(column)) {
			return this;
		}
		/*
		 * algorithmic plan:
		 *  1. obtain DawgStates directly before (set L) and after (set R) the given column
		 *  2. merge the states as if there were epsilon transitions, i.e. every edge that
		 *   leads to a state l in L now leads to all the states from R that have an edge coming from l. 
		 *  
		 */
		int columnIndex = mColNameToIndex.get(column);
		Set<DawgState> leftOfColumn = obtainStatesLeftOfColumn(columnIndex);
//		Set<DawgState> rightOfColumn = obtainStatesLeftOfColumn(columnIndex + 1);
		

//		Map<DawgState, Map<DawgLetter<LETTER, COLNAMES>, DawgState>> newTransitionRelation;
		NestedMap2<DawgState, DawgLetter<LETTER, COLNAMES>, DawgState> newTransitionRelation
		 	= new NestedMap2<DawgState, DawgLetter<LETTER,COLNAMES>, DawgState>();
		
		for (DawgState stateLeft : leftOfColumn) {
			for (Pair<DawgState, DawgLetter<LETTER, COLNAMES>> edgeLeadingToStateLeft : 
				mTransitionRelation.getInverse(stateLeft)) {
				for (Entry<DawgLetter<LETTER, COLNAMES>, DawgState> edgeLeadingFromStateLeftToAStateRight : 
					mTransitionRelation.get(stateLeft).entrySet()) {
					newTransitionRelation.put(edgeLeadingToStateLeft.getFirst(), 
							edgeLeadingToStateLeft.getSecond(), 
							edgeLeadingFromStateLeftToAStateRight.getValue());
				}
			}
		}
		
		/*
		 * add all the edges from the other columns
		 */
		for (Triple<DawgState, DawgLetter<LETTER, COLNAMES>, DawgState> edge : mTransitionRelation.entrySet()) {
			if (leftOfColumn.contains(edge.getFirst()) || leftOfColumn.contains(edge.getThird())) {
				// we have added a replacement for this edge above
				continue;
			}
			newTransitionRelation.put(edge.getFirst(), edge.getSecond(), edge.getThird());
		}
		
		
		final SortedSet<COLNAMES> newColnames = new TreeSet<COLNAMES>(mColNames);
		newColnames.remove(column);
		final Dawg<LETTER, COLNAMES> result = new Dawg<LETTER, COLNAMES>(
				newColnames, mAllConstants, mLogger, newTransitionRelation, mDawgFactory);

		return result;
	}

	private Set<DawgState> obtainStatesLeftOfColumn(int columnIndex) {
		Set<DawgState> result = new HashSet<DawgState>();
		result.add(mInitialState);
		for (int i = 0; i < columnIndex; i++)  {
			Set<DawgState> newResult = new HashSet<DawgState>();
			for (DawgState state : result) {
				// add all successor states without considering the letter
				newResult.addAll(mTransitionRelation.get(state).values());
			}
			result = newResult;
		}
		return result;
	}

	/**
	 * Renames columns of the input dawg according to the given renaming.
	 * The reordering is given implicitly through the renaming because the colnames are sorted automatically.
	 * @param other
	 * @param renaming
	 * @return
	 */
	private Dawg<LETTER, COLNAMES> reorderAndRename(Map<COLNAMES, COLNAMES> renaming) {
		assert false : "TODO: implement";
		return null;
	}


	/**
	 * We insert a column into the dawg. In that column, by convention, only one DawgLetter 
	 * labels all the edges. (Should be enough for our purposes..)
	 * 
	 * @param other
	 * @param columnName the name of the fresh column
	 * @param columnLetter the letter that is accepted in the fresh column
	 * @return
	 */
	private IDawg<LETTER, COLNAMES> insertColumn(COLNAMES columnName, DawgLetter<LETTER, COLNAMES> columnLetter) {
		assert false : "TODO: implement";
		return null;
	}


	@Override
	public IDawg<LETTER, COLNAMES> difference(IDawg<LETTER, COLNAMES> other) {
		// TODO: think about optimizations
		return this.intersect(other.complement());
	}
	
//	Map<DawgState, Map<DawgLetter<LETTER, COLNAMES>, DawgState>> getTransitionRelation() {
	NestedMap2<DawgState, DawgLetter<LETTER, COLNAMES>, DawgState> getTransitionRelation() {
		return mTransitionRelation;
	}
	
	Set<LETTER> getAllConstants() { 
		return mAllConstants;
	}
	
	LogProxy getLogger() {
		return mLogger;
	}
}

class UnionOrIntersectionDawgBuilder<LETTER, COLNAMES> {
	
	private final DawgState mUnionInitialState;
	private final DawgStateFactory mDawgStateFactory;
//	private final Map<DawgState, Map<DawgLetter<LETTER, COLNAMES>, DawgState>> mTransitionRelation;
	private final NestedMap2<DawgState, DawgLetter<LETTER, COLNAMES>, DawgState> mTransitionRelation;
	private final Dawg<LETTER, COLNAMES> mFirst;
	private final Dawg<LETTER, COLNAMES> mSecond;
	private final DawgLetterFactory<LETTER, COLNAMES> mDawgLetterFactory;
	private final DawgFactory<LETTER, COLNAMES> mDawgFactory;

	UnionOrIntersectionDawgBuilder(Dawg<LETTER, COLNAMES> first, Dawg<LETTER, COLNAMES> second, 
//			DawgLetterFactory<LETTER, COLNAMES> dlf, DawgStateFactory dsf) {
			DawgFactory<LETTER, COLNAMES> df) {
		assert first.mColNames.equals(second.mColNames) : "signatures don't match!";
		mDawgFactory = df;
		mDawgStateFactory = df.getDawgStateFactory();
		mDawgLetterFactory = df.getDawgLetterFactory();
//		mDawgLetterFactory = dlf;
//		mDawgStateFactory = dsf;
		
		mFirst = first; 
		mSecond = second;
		
//		mTransitionRelation = new HashMap<DawgState, Map<DawgLetter<LETTER,COLNAMES>,DawgState>>();
		mTransitionRelation = new NestedMap2<DawgState, DawgLetter<LETTER,COLNAMES>,DawgState>();

		mUnionInitialState = new PairDawgState(first.mInitialState, second.mInitialState);
		
	}
	
	Dawg<LETTER, COLNAMES> buildUnion() {
		return build(true);
	}
	
	Dawg<LETTER, COLNAMES> buildIntersection() {
		return build(false);
	}
	
	/**
	 * 
	 * @param doUnion if this flag is true, build a dawg that recognizes the union of mFirst and 
	 *   mSecond, otherwise build a dawg that recognizes the intersection of the two
	 * @return
	 */
	private Dawg<LETTER, COLNAMES> build(boolean doUnion) {
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
//								addTransition(cs, intersectionDl, newState);
								mTransitionRelation.put(cs, intersectionDl, newState);
							}

							if (doUnion) {
								Set<DawgLetter<LETTER, COLNAMES>> firstWithoutSecondDls = firstDl.difference(secondDl);
								if (!firstWithoutSecondDls.isEmpty()) {
									PairDawgState fwsDs = mDawgStateFactory.createPairDawgState(firstEn.getValue(), false, true);
									nextStates.add(fwsDs);
									for (DawgLetter<LETTER, COLNAMES> dl : firstWithoutSecondDls) {
//										addTransition(cs, dl, fwsDs);
										mTransitionRelation.put(cs, dl, fwsDs);
									}
								}

								Set<DawgLetter<LETTER, COLNAMES>> secondWithoutFirstDls = secondDl.difference(firstDl);
								if (!secondWithoutFirstDls.isEmpty()) {
									PairDawgState swfDs = new PairDawgState(secondEn.getValue(), true, false);
									nextStates.add(swfDs);
									for (DawgLetter<LETTER, COLNAMES> dl : secondWithoutFirstDls) {
//										addTransition(cs, dl, swfDs);
										mTransitionRelation.put(cs, dl, swfDs);
									}
								}
							}
						}
					}
				} else if (doUnion && cs.mFirstIsSink) {
					Map<DawgLetter<LETTER, COLNAMES>, DawgState> firstLetterToTarget = 
							mFirst.getTransitionRelation().get(cs.getFirst());
					for (Entry<DawgLetter<LETTER, COLNAMES>, DawgState> firstEn : firstLetterToTarget.entrySet()) {
						PairDawgState ds = mDawgStateFactory.createPairDawgState(firstEn.getValue(), true, false);
						nextStates.add(ds);
//						addTransition(cs, firstEn.getKey(), ds);
						mTransitionRelation.put(cs, firstEn.getKey(), ds);
					}
				} else if (doUnion && cs.mSecondIsSink) {
					Map<DawgLetter<LETTER, COLNAMES>, DawgState> secondLetterToTarget = 
							mSecond.getTransitionRelation().get(cs.getSecond());
					for (Entry<DawgLetter<LETTER, COLNAMES>, DawgState> secondEn : secondLetterToTarget.entrySet()) {
						PairDawgState ds = mDawgStateFactory.createPairDawgState(secondEn.getValue(), false, true);
						nextStates.add(ds);
//						addTransition(cs, secondEn.getKey(), ds);
						mTransitionRelation.put(cs, secondEn.getKey(), ds);
					}
				}
			}
			currentStates = nextStates;
		}
		
		return new Dawg<LETTER, COLNAMES>(mFirst.getColnames(), mFirst.getAllConstants(), 
				mFirst.getLogger(),  mTransitionRelation, mDawgFactory);
	}
	
//	private void addTransition(DawgState source, DawgLetter<LETTER, COLNAMES> dawgLetter, DawgState target) {
//		Dawg.addTransition(mTransitionRelation, source, dawgLetter, target);
//	}
}
