/*
 * Copyright (C) 2016-2017 Alexander Nutz (nutz@informatik.uni-freiburg.de)
 * Copyright (C) 2016-2017 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.dawgs;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;
import java.util.SortedSet;
import java.util.TreeSet;

import de.uni_freiburg.informatik.ultimate.smtinterpol.LogProxy;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.EprHelpers;

/**
 * 
 * 
 * Conventions about Dawgs:
 *  <li> The DawgLetters at the outgoing transition of one DawgState are all disjoint. 
 *    i.e. the Dawg is deterministic in the usual sense.
 *    In particular there are no two outgoing edges with the same DawgLetter at any DawgState
 *  
 * 
 * 
 * @author Alexander Nutz (nutz@informatik.uni-freiburg.de)
 *
 * @param <LETTER>
 * @param <COLNAMES>
 */
public class Dawg<LETTER, COLNAMES> extends AbstractDawg<LETTER, COLNAMES> {
	
	/*
	 * convention:
	 * states are just integers
	 * 
	 * the initial state is "0"
	 * the accepting state is <mArity>
	 * the sink state is "-1"
	 */
	
	final DawgState mInitialState;
//	final Set<DawgState> mInitialStates;
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
		
		mTransitionRelation = new NestedMap2<DawgState, DawgLetter<LETTER,COLNAMES>,DawgState>();
		
//		mInitialStates =  Collections.singleton(mDawgStateFactory.createDawgState());
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
		
//		mInitialStates =  Collections.singleton(mDawgStateFactory.createDawgState());
		mInitialState =  mDawgStateFactory.createDawgState();

		mTransitionRelation = new NestedMap2<DawgState, DawgLetter<LETTER,COLNAMES>,DawgState>();
		
//		DawgState currentState = mInitialStates.iterator().next();
		DawgState currentState = mInitialState;

		for (int i = 0; i < colnames.size(); i++) {
			DawgState nextState = mDawgStateFactory.createDawgState();
			mTransitionRelation.put(currentState, mDawgLetterFactory.getUniversalDawgLetter(), nextState);
			currentState = nextState;
		}
		
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
		super(colnames, allConstants, logger);
		
		mDawgFactory = df;
		mDawgStateFactory = df.getDawgStateFactory();
		mDawgLetterFactory = df.getDawgLetterFactory();

		mTransitionRelation = new NestedMap2<DawgState, DawgLetter<LETTER,COLNAMES>,DawgState>();

//		mInitialStates =  Collections.singleton(mDawgStateFactory.createDawgState());
		mInitialState =  mDawgStateFactory.createDawgState();
		
//		DawgState currentState = mInitialStates.iterator().next();
		DawgState currentState = mInitialState;

		for (int i = 0; i < colnames.size(); i++) {
			DawgState nextState =  mDawgStateFactory.createDawgState();
			DawgLetter<LETTER, COLNAMES> dl = mDawgLetterFactory.createSingletonSetDawgLetter(word.get(i));
			mTransitionRelation.put(currentState, dl, nextState);
			currentState = nextState;
		}
		
		mIsUniversal = false;
		mIsEmpty = false;
	}
	
	Dawg(final SortedSet<COLNAMES> colnames, Set<LETTER> allConstants, 
			final LogProxy logger, 
			final NestedMap2<DawgState, DawgLetter<LETTER, COLNAMES>, DawgState> tr, 
//			final Set<DawgState> initialStates,
			final DawgState initialState,
			final DawgFactory<LETTER, COLNAMES> df) {
		super(colnames, allConstants, logger);
		
		mDawgFactory = df;
		mDawgStateFactory = df.getDawgStateFactory();
		mDawgLetterFactory = df.getDawgLetterFactory();
//		mInitialStates = initialStates;
		mInitialState = initialState;
	
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
		final NestedMap2<DawgState, DawgLetter<LETTER, COLNAMES>, DawgState> newTransitionRelation
				= new NestedMap2<DawgState, DawgLetter<LETTER, COLNAMES>, DawgState>();

		
		
		Set<DawgState> currentStates = new HashSet<DawgState>();
//		currentStates.addAll(mInitialStates);
		currentStates.add(mInitialState);
		
		DawgState nextLevelFormerSinkState = null;
		
		
		//TODO:
		// - double check
		
		for (int i = 0; i < this.getColnames().size(); i++) {
			Set<DawgState> nextStates = new HashSet<DawgState>();
			
			DawgState lastLevelFormerSinkState = nextLevelFormerSinkState;
			nextLevelFormerSinkState = mDawgStateFactory.createDawgState();
			nextStates.add(nextLevelFormerSinkState);
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
					newTransitionRelation.put(cs, letterAndState.getKey(), letterAndState.getValue());
				}
				
				/*
				 * collects all the DawgLetters that do not have a transition from the current state
				 * those lead to the "former sink state"
				 */
				Set<DawgLetter<LETTER, COLNAMES>> complementDawgLetters = 
						mDawgLetterFactory.complementDawgLetterSet(outgoingDawgLetters);
				for (DawgLetter<LETTER, COLNAMES> cdl : complementDawgLetters) {
					newTransitionRelation.put(cs, cdl, nextLevelFormerSinkState);
				}
	
			}
			currentStates = nextStates;
		}
		
		return new Dawg<LETTER, COLNAMES>(
				mColNames, mAllConstants, mLogger, newTransitionRelation, mInitialState, mDawgFactory);
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
		assert false : "TODO";
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
			}
			currentColnamesPrestates = newCurrentColnamesPrestates;
		}
		return new Dawg<LETTER, COLNAMES>(mColNames, mAllConstants, mLogger, newTransitionRelation, 
				mInitialState, mDawgFactory);
	}

	@Override
	protected Iterable<List<LETTER>> listPoints() {
		// TODO Auto-generated method stub
		assert false : "TODO - when we need it";
		return null;
	}

	@Override
	public Iterator<List<LETTER>> iterator() {
		// TODO Auto-generated method stub
		assert false : "TODO - when we need it";
		return null;
	}

	@Override
	public boolean isSingleton() {
		// TODO Auto-generated method stub
		assert false : "TODO - when we need it";
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
	
	private Dawg<LETTER, COLNAMES> projectColumnAway(final COLNAMES column) {
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
		Set<DawgState> leftOfColumn = obtainStatesLeftOfColumn(column);
		
		assert !leftOfColumn.contains(mInitialState) : 
			"TODO : treat special case where we project away leftmost column";
		
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
		
		
		final SortedSet<COLNAMES> newColnames = new TreeSet<COLNAMES>(EprHelpers.getColumnNamesComparator());
		newColnames.addAll(mColNames);
		newColnames.remove(column);
		final Dawg<LETTER, COLNAMES> result = new Dawg<LETTER, COLNAMES>(
				newColnames, mAllConstants, mLogger, newTransitionRelation, mInitialState, mDawgFactory);

		return result;
	}

	Set<DawgState> obtainStatesLeftOfColumn(COLNAMES colName) {
		assert mColNameToIndex.get(colName) != null : "column does not exist in this Dawg";
		return obtainStatesLeftOfColumn(mColNameToIndex.get(colName));
	}

	Set<DawgState> obtainStatesLeftOfColumn(int columnIndex) {
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
		Dawg<LETTER, COLNAMES> result = (Dawg<LETTER, COLNAMES>) mDawgFactory.copyDawg(this);
		for (Entry<COLNAMES, COLNAMES> en : renaming.entrySet()) {
//			result = reorderAndRename(en.getKey(), en.getValue());
			result = new ReorderAndRenameDawgBuilder<LETTER, COLNAMES>(mDawgFactory, 
						this, 
						en.getKey(), 
						en.getValue())
					.build();
		}
		return result;
	}


	

	/**
	 * Determines if there is a path from sourceState to targetState in graph.
	 * 
	 * TODO: naive implementation --> optimize (e.g. could be precomputed for whole graph)
	 * 
	 * @param sourceState
	 * @param targetState
	 * @param graph
	 * @return True if there is a path from source to target in graph, false otherwise.
	 */
	static <LETTER, COLNAMES> boolean isReachableFrom(DawgState sourceState, DawgState targetState,
			NestedMap2<DawgState, DawgLetter<LETTER, COLNAMES>, DawgState> graph) {
		Set<DawgState> currentStates = new HashSet<DawgState>();
		currentStates.add(sourceState);
		while(!currentStates.isEmpty()) {
			final Set<DawgState> newCurrentStates = new HashSet<DawgState>();
			for (DawgState state : currentStates) {
				for (Entry<DawgLetter<LETTER, COLNAMES>, DawgState> outgoingEdge : graph.get(state).entrySet()) {
					final DawgState edgeTarget = outgoingEdge.getValue();
					if (edgeTarget.equals(targetState)) {
						return true;
					}
					newCurrentStates.add(edgeTarget);
				}
			}
			currentStates = newCurrentStates;
		}
		return false;
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
	private IDawg<LETTER, COLNAMES> insertColumn(final COLNAMES columnName, 
			final DawgLetter<LETTER, COLNAMES> columnLetter) {

		final NestedMap2<DawgState, DawgLetter<LETTER, COLNAMES>, DawgState> newTransitionRelation
		 	= new NestedMap2<DawgState, DawgLetter<LETTER,COLNAMES>, DawgState>();
		
		/*
		 * find the position in this Dawg's signature where the new column must be inserted
		 */
		COLNAMES rightNeighBourColumn = findRightNeighbourColumn(columnName);
		
		//TODO: debug the above computation
		final Set<DawgState> statesLeftOfColumn = obtainStatesLeftOfColumn(rightNeighBourColumn);
		
		/*
		 * we split each of the states where the column is to be inserted into two
		 * 
		 * there is a transition between the split states with the given letter
		 */
		Map<DawgState, Pair<DawgState, DawgState>> splitOldStateToNewSplitStatePair
			= new HashMap<DawgState, Pair<DawgState,DawgState>>();
		for (DawgState ds : statesLeftOfColumn) {
			DawgState newStateLeft = mDawgStateFactory.createDawgState();
			DawgState newStateRight = mDawgStateFactory.createDawgState();
			splitOldStateToNewSplitStatePair.put(ds, 
					new Pair<DawgState, DawgState>(
							newStateLeft,
							newStateRight));
			newTransitionRelation.put(newStateLeft, columnLetter, newStateRight);
		}
		
		/*
		 * incoming transitions of the old split state now go to its left newState
		 * 
		 * outgoing transitions of the old split state now go to its right newState
		 */
		for (Entry<DawgState, Pair<DawgState, DawgState>> en : splitOldStateToNewSplitStatePair.entrySet()) {
			for (Pair<DawgState, DawgLetter<LETTER, COLNAMES>> incomingTransition : 
				mTransitionRelation.getInverse(en.getKey())) {
				newTransitionRelation.put(incomingTransition.getFirst(), 
						incomingTransition.getSecond(), en.getValue().getFirst());
			}
			for (Entry<DawgLetter<LETTER, COLNAMES>, DawgState> outgoingTransition : 
				mTransitionRelation.get(en.getKey()).entrySet()) {
				newTransitionRelation.put(en.getValue().getSecond(), 
						outgoingTransition.getKey(), outgoingTransition.getValue());
			}
		}
		
		final TreeSet<COLNAMES> newSignature = new TreeSet<COLNAMES>(EprHelpers.getColumnNamesComparator());
		newSignature.addAll(mColNames);
		newSignature.add(columnName);
		return new Dawg<LETTER, COLNAMES>(newSignature, mAllConstants, mLogger, newTransitionRelation, 
				mInitialState, mDawgFactory);
	}

	COLNAMES findRightNeighbourColumn(final COLNAMES columnName) {
		COLNAMES rightNeighBourColumn = null;
		for (COLNAMES col : mColNames) {
			if (mColNames.comparator().compare(columnName, col) > 0) {
				// columName will be inserted directly left from col
				rightNeighBourColumn = col;
				break;
			}
		}
		assert rightNeighBourColumn != null;
		return rightNeighBourColumn;
	}


	@Override
	public IDawg<LETTER, COLNAMES> difference(IDawg<LETTER, COLNAMES> other) {
		// TODO: think about optimizations
		return this.intersect(other.complement());
	}
	
	NestedMap2<DawgState, DawgLetter<LETTER, COLNAMES>, DawgState> getTransitionRelation() {
		return mTransitionRelation;
	}
	
	Set<LETTER> getAllConstants() { 
		return mAllConstants;
	}
	
	LogProxy getLogger() {
		return mLogger;
	}

	public DawgState getInitialState() {
		return mInitialState;
	}
}

