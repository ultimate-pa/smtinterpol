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

import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;
import java.util.SortedSet;
import java.util.TreeSet;

import de.uni_freiburg.informatik.ultimate.smtinterpol.LogProxy;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.BinaryRelation;
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
	
	final DawgState mInitialState;
	
	private boolean mIsEmpty;
	private boolean mIsUniversal;
	
	private final DawgStateFactory<LETTER, COLNAMES> mDawgStateFactory;
	
	/**
	 * Transition relation of the finite automaton as a nested map.
	 */
	private final NestedMap2<DawgState, IDawgLetter<LETTER, COLNAMES>, DawgState> mTransitionRelation;
	
	private final DawgLetterFactory<LETTER, COLNAMES> mDawgLetterFactory;
	private final DawgFactory<LETTER, COLNAMES> mDawgFactory;
	private final Set<DawgState> mFinalStates;

	private final boolean mIsSingleton;
	
	/**
	 * Create an empty dawg
	 * @param logger
	 * @param allConstants
	 * @param colnames
	 */
	public Dawg(DawgFactory<LETTER, COLNAMES> df, LogProxy logger, Set<LETTER> allConstants, 
			SortedSet<COLNAMES> colnames) {
		super(colnames, allConstants, logger);
		mDawgFactory = df;
		mDawgStateFactory = df.getDawgStateFactory();
		mDawgLetterFactory = df.getDawgLetterFactory();
		
//		mTransitionRelation = new NestedMap2<DawgState, IDawgLetter<LETTER,COLNAMES>,DawgState>();
		mTransitionRelation = null;
		
//		mInitialState =  mDawgStateFactory.createDawgState();
		mInitialState =  null;
		
		mFinalStates = Collections.emptySet();
		
		mIsUniversal = false;
		mIsEmpty = true;
		mIsSingleton = false;
	}

	/**
	 * Creates a dawg that accepts all words of the given signature.
	 * @param logger
	 * @param allConstants
	 * @param colnames
	 * @param fullDawg
	 */
	public Dawg(DawgFactory<LETTER, COLNAMES> df, LogProxy logger, Set<LETTER> allConstants, 
			SortedSet<COLNAMES> colnames, boolean fullDawg) {
		super(colnames, allConstants, logger);
		assert fullDawg : "use other constructor for empty dawg";
		mDawgFactory = df;
		mDawgStateFactory = df.getDawgStateFactory();
		mDawgLetterFactory = df.getDawgLetterFactory();
		
		mInitialState =  mDawgStateFactory.createDawgState();

		mTransitionRelation = new NestedMap2<DawgState, IDawgLetter<LETTER,COLNAMES>,DawgState>();
		
		DawgState currentState = mInitialState;

		for (int i = 0; i < colnames.size(); i++) {
			DawgState nextState = mDawgStateFactory.createDawgState();
			mTransitionRelation.put(currentState, mDawgLetterFactory.getUniversalDawgLetter(), nextState);
			currentState = nextState;
		}
		mFinalStates = new HashSet<DawgState>();
		mFinalStates.add(currentState);
		
		mIsUniversal = true;
		mIsEmpty = false;
		mIsSingleton = false;
	}

	/**
	 * Creates a dawg that accepts one word.
	 * @param logger
	 * @param allConstants
	 * @param colnames
	 * @param fullDawg
	 */
	public Dawg(final DawgFactory<LETTER, COLNAMES> df, final LogProxy logger, final Set<LETTER> allConstants, 
			final SortedSet<COLNAMES> colnames, 
			final List<LETTER> word) {
		super(colnames, allConstants, logger);
		
		mDawgFactory = df;
		mDawgStateFactory = df.getDawgStateFactory();
		mDawgLetterFactory = df.getDawgLetterFactory();

		mTransitionRelation = new NestedMap2<DawgState, IDawgLetter<LETTER,COLNAMES>,DawgState>();

		mInitialState =  mDawgStateFactory.createDawgState();
		
		DawgState currentState = mInitialState;

		for (int i = 0; i < colnames.size(); i++) {
			DawgState nextState =  mDawgStateFactory.createDawgState();
			IDawgLetter<LETTER, COLNAMES> dl = mDawgLetterFactory.createSingletonSetDawgLetter(word.get(i));
			mTransitionRelation.put(currentState, dl, nextState);
			currentState = nextState;
		}
		mFinalStates = new HashSet<DawgState>();
		mFinalStates.add(currentState);
		
		mIsUniversal = false;
		mIsEmpty = false;
		mIsSingleton = true;
	}
	
	Dawg(final DawgFactory<LETTER, COLNAMES> df, 
			final LogProxy logger, 
			final Set<LETTER> allConstants, 
			final SortedSet<COLNAMES> colnames, 
			final NestedMap2<DawgState, IDawgLetter<LETTER, COLNAMES>, DawgState> transitionRelation,
			final DawgState initialState) {
		super(colnames, allConstants, logger);
		
		mDawgFactory = df;
		mDawgStateFactory = df.getDawgStateFactory();
		mDawgLetterFactory = df.getDawgLetterFactory();
		
		mInitialState = initialState;
	
		mTransitionRelation = transitionRelation;
		
		mFinalStates = computeFinalStates();

		CheckEmptyUniversalSingleton<LETTER, COLNAMES> ceus = new CheckEmptyUniversalSingleton<LETTER, COLNAMES>(
				mDawgFactory, allConstants, colnames.size(), initialState, transitionRelation);
		mIsEmpty = ceus.isEmpty();
		mIsSingleton = ceus.isSingleton();
		mIsUniversal = ceus.isUniversal();
		
		assert !containsEmptyDawgLetters(mTransitionRelation) : "transition relation contains an emptyDawgLetter"
				+ " -- EmptyDawgLetters should only used in operations on DawgLetters, not in a Dawg";
		assert isDeterministic();
	}

	private boolean containsEmptyDawgLetters(
			NestedMap2<DawgState, IDawgLetter<LETTER, COLNAMES>, DawgState> transitionRelation) {
		for (Triple<DawgState, IDawgLetter<LETTER, COLNAMES>, DawgState> triple : transitionRelation.entrySet()) {
			if (triple.getSecond() instanceof EmptyDawgLetter<?, ?>) {
				return true;
			}
			if (triple.getSecond() instanceof EmptyDawgLetterWithEqualities<?, ?>) {
				return true;
			}
		}
		return false;
	}

//	/**
//	 * algorithmic plan:
//	 *  try to sample two words from the language through a depth first search
//	 * @return
//	 */
//	private boolean checkIsSingleton() {
//		int counter = 0;
//		for (List<LETTER> point : listPoints()) {
//			counter++;
//			if (counter == 2) {
//				return false;
//			}
//		}
//		return counter == 1;
////		return new ArrayList<List<LETTER>>(listPoints()).size() == 1;
////		final Set<DawgState> currentStates = new HashSet<DawgState>();
////		currentStates.add(mInitialState);
//
//		
//		// sample first word
////		List<LETTER> firstWord = null;
////		List<IDawgLetter<LETTER, COLNAMES>> firstPath = null;
////		{
////			DawgState currentState = mInitialState;
////			for (COLNAMES col : mColNames) {
////				Set<Pair<IDawgLetter<LETTER, COLNAMES>, DawgState>> outEdges = 
////						mTransitionRelation.getOutEdgeSet(currentState);
////				outEdges.iterator().next().getSecond();
////				currentState = 
////				firstPath.add(e)
////
////			}
////		}
////
////		// sample another word that is not the first
////		return false;
//	}

//	private boolean checkUniversality() {
//		
//		Set<DawgState> currentStates = new HashSet<DawgState>();
//		currentStates.add(mInitialState);
//		
////		while (!currentStates.isEmpty()) {
//		for (int i = 0; i < mColNames.size(); i++) {
//			final Set<DawgState> newCurrentStates = new HashSet<DawgState>();
//			for (DawgState cs : currentStates) {
//			
//				final Set<IDawgLetter<LETTER, COLNAMES>> outLetters = new HashSet<IDawgLetter<LETTER,COLNAMES>>();
//				for (Pair<IDawgLetter<LETTER, COLNAMES>, DawgState> outEdge : 
//					mTransitionRelation.getOutEdgeSet(cs)) {
//					
//					outLetters.add(outEdge.getFirst());
//					newCurrentStates.add(outEdge.getSecond());
//				}
//				
//				if (!mDawgLetterFactory.isUniversal(outLetters)) {
//					return false;
//				}
//				
//			}
//			currentStates = newCurrentStates;
//		}
//		assert currentStates.equals(mFinalStates);
//		
//		return true;
//	}

	private Set<DawgState> computeFinalStates() {
		Set<DawgState> currentStates = new HashSet<DawgState>();
		currentStates.add(mInitialState);
		for (int i = 0; i < mColNames.size(); i++) {
			final Set<DawgState> newCurrentStates = new HashSet<DawgState>();
			for (DawgState cs : currentStates) {
//				if (mTransitionRelation.get(cs) == null) {
//					continue;
//				}
				for (Pair<IDawgLetter<LETTER, COLNAMES>, DawgState> outEdge : mTransitionRelation.getOutEdgeSet(cs)) {
					newCurrentStates.add(outEdge.getSecond());
				}
			}
			currentStates = newCurrentStates;
		}
		return Collections.unmodifiableSet(currentStates);
	}

	@Override
	public IDawg<LETTER, COLNAMES> intersect(IDawg<LETTER, COLNAMES> other) {
		if (this.isEmpty()) {
			return this;
		}
		if (other.isEmpty()) {
			return other;
		}
		return new UnionOrIntersectionDawgBuilder<LETTER, COLNAMES>(
				this, (Dawg<LETTER, COLNAMES>) other, mDawgFactory).buildIntersection();
	}

	@Override
	public IDawg<LETTER, COLNAMES> union(IDawg<LETTER, COLNAMES> other) {
		if (this.isEmpty()) {
			return other;
		}
		if (other.isEmpty()) {
			return this;
		}
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
		final NestedMap2<DawgState, IDawgLetter<LETTER, COLNAMES>, DawgState> newTransitionRelation
				= new NestedMap2<DawgState, IDawgLetter<LETTER, COLNAMES>, DawgState>();

		
		
		Set<DawgState> currentStates = new HashSet<DawgState>();
		currentStates.add(mInitialState);
		
		DawgState nextLevelFormerSinkState = null;
		
		
		//TODO:
		// - double check
		
		for (int i = 0; i < this.getColnames().size(); i++) {
			Set<DawgState> nextStates = new HashSet<DawgState>();
			
			DawgState lastLevelFormerSinkState = nextLevelFormerSinkState;
			nextLevelFormerSinkState = mDawgStateFactory.createDawgState();
//			nextStates.add(nextLevelFormerSinkState);
			if (i > 0) {
				newTransitionRelation.put(
						lastLevelFormerSinkState, mDawgLetterFactory.getUniversalDawgLetter(), nextLevelFormerSinkState);
			}

			for (DawgState cs : currentStates) {
				final Set<IDawgLetter<LETTER, COLNAMES>> outgoingDawgLetters = new HashSet<IDawgLetter<LETTER,COLNAMES>>();

				/*
				 * the old transitions stay intact (except for the ones leading to the final state
				 */
				for (Pair<IDawgLetter<LETTER, COLNAMES>, DawgState> letterAndState : mTransitionRelation.getOutEdgeSet(cs)) {
//					if (i == this.getColnames().size() - 1) {
//						// we are in the last column
//						// the old transitions lead to the old final state(s)
//						// --> omit those
//						break;
//					}
					outgoingDawgLetters.add(letterAndState.getFirst());
					if (i != this.getColnames().size() - 1) {
						nextStates.add(letterAndState.getSecond());
						newTransitionRelation.put(cs, letterAndState.getFirst(), letterAndState.getSecond());
					}
				}
				
				/*
				 * collects all the DawgLetters that do not have a transition from the current state
				 * those lead to the "former sink state"
				 */
				Set<IDawgLetter<LETTER, COLNAMES>> complementDawgLetters = 
						mDawgLetterFactory.complementDawgLetterSet(outgoingDawgLetters);
				for (IDawgLetter<LETTER, COLNAMES> cdl : complementDawgLetters) {
					newTransitionRelation.put(cs, cdl, nextLevelFormerSinkState);
				}
	
			}
			currentStates = nextStates;
		}
		
		return new Dawg<LETTER, COLNAMES>(
				mDawgFactory, mLogger, mAllConstants, mColNames, newTransitionRelation, mInitialState);
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
		// look for an outgoing edge with a DawgLetter that matches ltr
		for (Pair<IDawgLetter<LETTER, COLNAMES>, DawgState> en : mTransitionRelation.getOutEdgeSet(source)) {
			IDawgLetter<LETTER, COLNAMES> dl = en.getFirst();
			if (dl.matches(ltr, word, mColNameToIndex)) {
				// dl allows a transition with ltr
				return en.getSecond();
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
	public IDawg<LETTER, COLNAMES> add(List<LETTER> arguments) {
		return new AddWordDawgBuilder<LETTER, COLNAMES>(mDawgFactory, this, arguments).build();
	}

	@Override
	public IDawg<LETTER, COLNAMES> select(Map<COLNAMES, LETTER> selectMap) {
		if (this.isEmpty()) {
			return this;
		}
		
		Set<DawgState> currentColnamesPrestates = new HashSet<DawgState>();
		currentColnamesPrestates.add(mInitialState);

		NestedMap2<DawgState, IDawgLetter<LETTER, COLNAMES>, DawgState> newTransitionRelation
			= new NestedMap2<DawgState, IDawgLetter<LETTER,COLNAMES>, DawgState>();

		for (COLNAMES cn : getColnames()) {
			
			Set<DawgState> newCurrentColnamesPrestates = new HashSet<DawgState>();
			for (DawgState ccp : currentColnamesPrestates) {
				for (Pair<IDawgLetter<LETTER, COLNAMES>, DawgState> lts : mTransitionRelation.getOutEdgeSet(ccp)) {
					LETTER selectLetter = selectMap.get(cn);
					if (selectLetter == null) {
						// no select constraint 
						// --> retain all transition and get the states before the next column
//						newLetterToState.put(lts.getKey(), lts.getValue());
						newTransitionRelation.put(ccp, lts.getFirst(), lts.getSecond());
						newCurrentColnamesPrestates.add(lts.getSecond());
					} else {
						// we have a select constraint
						// --> Dawg edges that don't allow the select letter are removed
						// --> Dawg edges that allow the select letter are constrained to only that letter; (un)equals
						//   constraints remain untouched for those
						IDawgLetter<LETTER, COLNAMES> dawgLetter = lts.getFirst();
						
						IDawgLetter<LETTER, COLNAMES> restrictedDL = dawgLetter.restrictToLetter(selectLetter);

						if (restrictedDL == null) {
							// dawgLetter does not allow transitions with selectLetter
							// --> omit transition
						} else {
							// dawgLetter does allow transitions with selectLetter
							// --> replace the label of the transition by the restricted letter
//							newLetterToState.put(restrictedDL, lts.getValue());
							newTransitionRelation.put(ccp, restrictedDL, lts.getSecond());
							newCurrentColnamesPrestates.add(lts.getSecond());
						}
					}
				}
			}
			currentColnamesPrestates = newCurrentColnamesPrestates;
		}
		return new Dawg<LETTER, COLNAMES>(mDawgFactory, mLogger, mAllConstants, mColNames, 
				newTransitionRelation, mInitialState);
	}

	@Override
	public Iterable<List<LETTER>> listPoints() {
		if (isEmpty()) {
			return Collections.emptySet();
		}
		
		if (isUniversal()) {
			return EprHelpers.computeNCrossproduct(getAllConstants(), mColNames.size(), mLogger);
		}
		
		
		Set<List<LETTER>> result = new TreeSet<List<LETTER>>(); // using a TreeSet for nicer (sorted) output
		
		Set<DawgState> currentStates = new HashSet<DawgState>();
		currentStates.add(mInitialState);
		while (!currentStates.equals(getFinalStates())) {
			
			final Set<DawgState> newCurrentStates = new HashSet<DawgState>();
			final Set<List<LETTER>> newResult = new TreeSet<List<LETTER>>();
			
			for (DawgState cs : currentStates) {
				assert !getFinalStates().contains(cs);
				for (Pair<IDawgLetter<LETTER, COLNAMES>, DawgState> outEdge : 
						mTransitionRelation.getOutEdgeSet(cs)) {
					newCurrentStates.add(outEdge.getSecond());
					
					for (List<LETTER> prefix : result) {
						for (LETTER letter : outEdge.getFirst().allLettersThatMatch(prefix, mColNameToIndex)) {
							List<LETTER> newPrefix = new ArrayList<LETTER>(prefix);
							newPrefix.add(letter);
							newResult.add(newPrefix);
						}
					}
				}
			}
			
			result = newResult;
			currentStates = newCurrentStates;
			
		}
		
		return result;
	}

	@Override
	public Iterator<List<LETTER>> iterator() {

		return listPoints().iterator();
//		return new Iterator<List<LETTER>>() {
//
//			Set<DawgState> mVisitedStates = new HashSet<DawgState>();
//			Set<DawgState> mOpenStates = new HashSet<DawgState>();
//			BinaryRelation<DawgState, List<LETTER>> mOpenStateToPrefixes = new BinaryRelation<DawgState, List<LETTER>>();
//			{
//				mOpenStates.add(getInitialState());
//				mOpenStateToPrefixes.addPair(getInitialState(), new ArrayList<LETTER>());
//			}
//
//			@Override
//			public boolean hasNext() {
//				return !mOpenStates.isEmpty();
//			}
//
//			@Override
//			public List<LETTER> next() {
//				final DawgState openState = mOpenStates.iterator().next();
//
//				while (!getFinalStates().contains(openSuccessorState)) {
//					DawgState openSuccessorState = null;
//					for (Entry<IDawgLetter<LETTER, COLNAMES>, DawgState> outEdge : 
//						getTransitionRelation().get(openState).entrySet()) {
//						DawgState targetState = outEdge.getValue();
//						if (!mVisitedStates.contains(targetState)) {
//							openSuccessorState  = targetState;
//							break;
//						}
//					}
//				}
//				return null;
//			}
//
//		};
	}

	@Override
	public boolean isSingleton() {
		return mIsSingleton;
	}

	@Override
	public boolean supSetEq(IDawg<LETTER, COLNAMES> other) {
		// TODO: think about optimizations
		return this.complement().intersect(other).isEmpty();
	}

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
			BinaryRelation<COLNAMES, COLNAMES> translation,
			List<Object> argList, SortedSet<COLNAMES> newSignature) {
		assert argList.size() == newSignature.size();
		
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
			if (!translation.getDomain().contains(colname)) {
				assert !argList.contains(colname);
				result = result.projectColumnAway(colname);
			}
		}
		
		/*
		 * 2. reorder an rename the remaining columns
		 */
		result = result.reorderAndRename(translation);
		
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
//				assert newSigColname == translation.get(arg);
				assert translation.getImage((COLNAMES) arg).contains(newSigColname);
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
		
		NestedMap2<DawgState, IDawgLetter<LETTER, COLNAMES>, DawgState> newTransitionRelation
		 	= new NestedMap2<DawgState, IDawgLetter<LETTER,COLNAMES>, DawgState>();
		
		for (DawgState stateLeft : leftOfColumn) {
			for (Pair<DawgState, IDawgLetter<LETTER, COLNAMES>> edgeLeadingToStateLeft : 
				mTransitionRelation.getInverse(stateLeft)) {
				for (Pair<IDawgLetter<LETTER, COLNAMES>, DawgState> edgeLeadingFromStateLeftToAStateRight : 
					mTransitionRelation.getOutEdgeSet(stateLeft)) {
					newTransitionRelation.put(edgeLeadingToStateLeft.getFirst(), 
							edgeLeadingToStateLeft.getSecond(), 
							edgeLeadingFromStateLeftToAStateRight.getSecond());
				}
			}
		}
		
		/*
		 * add all the edges from the other columns
		 */
		for (Triple<DawgState, IDawgLetter<LETTER, COLNAMES>, DawgState> edge : mTransitionRelation.entrySet()) {
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
				mDawgFactory, mLogger, mAllConstants, newColnames, newTransitionRelation, mInitialState);

		return result;
	}

	Set<DawgState> obtainStatesLeftOfColumn(COLNAMES rightNeighbourColumn) {
		assert mColNameToIndex.get(rightNeighbourColumn) != null : "column does not exist in this Dawg";
		return obtainStatesLeftOfColumn(mColNameToIndex.get(rightNeighbourColumn));
	}

	Set<DawgState> obtainStatesLeftOfColumn(int columnIndex) {
		Set<DawgState> result = new HashSet<DawgState>();
		result.add(mInitialState);
		for (int i = 0; i < columnIndex; i++)  {
			Set<DawgState> newResult = new HashSet<DawgState>();
			for (DawgState state : result) {
				// add all successor states without considering the letter
				if (mTransitionRelation.get(state) != null) {
					newResult.addAll(mTransitionRelation.get(state).values());
				}
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
	private Dawg<LETTER, COLNAMES> reorderAndRename(BinaryRelation<COLNAMES, COLNAMES> renaming) {
		assert !renaming.getDomain().isEmpty();
		
		if (this.isEmpty() || this.isUniversal()) {
			// for an empty or universal dawg we just return a fresh dawg with the new signature
			final SortedSet<COLNAMES> newSignature = EprHelpers.transformSignature(mColNames, renaming);
			if (this.isEmpty()) {
				return (Dawg<LETTER, COLNAMES>) mDawgFactory.getEmptyDawg(newSignature);
			} else {
				return (Dawg<LETTER, COLNAMES>) mDawgFactory.getUniversalDawg(newSignature);
			}
		}

		Dawg<LETTER, COLNAMES> result = null;
		for (COLNAMES oldcol : renaming.getDomain()) {
			Set<COLNAMES> newCols = renaming.getImage(oldcol);
			if (newCols.size() == 1) {
				result = new ReorderAndRenameDawgBuilder<LETTER, COLNAMES>(mDawgFactory, 
						this, 
						oldcol, 
						newCols.iterator().next())
					.build();
			} else {
				/*
				 *  we make the renaming for the first newCol and then trigger "column duplication"
				 *  for the others
				 */
				Iterator<COLNAMES> newColIt = newCols.iterator();
				
				COLNAMES firstCol = newColIt.next();
				result = new ReorderAndRenameDawgBuilder<LETTER, COLNAMES>(mDawgFactory, 
						this, 
						oldcol, 
						firstCol)
					.build();

				while (newColIt.hasNext()) {
					COLNAMES currentNewCol = newColIt.next();
					result = result.duplicateColumn(firstCol, currentNewCol);
				}
			}
		}
		return result;
	}
	

	private Dawg<LETTER, COLNAMES> duplicateColumn(COLNAMES firstCol,
				COLNAMES currentNewCol) {
		if (mDawgLetterFactory.useSimpleDawgLetters()) {
			return new ReorderAndRenameDawgBuilder<LETTER, COLNAMES>(mDawgFactory, 
					this, firstCol, currentNewCol, true)
					.build();
		} else {
			/*
			 * this is the "easy case" as our non-simple dawg-letters allow equality-constraints
			 */
			//TODO
			assert false : "TODO: implement";
			return null;
		}
	}

	/**
	 * Renames columns of the input dawg according to the given renaming.
	 * The reordering is given implicitly through the renaming because the colnames are sorted automatically.
	 * @param other
	 * @param renaming
	 * @return
	 */
	private Dawg<LETTER, COLNAMES> reorderAndRename(Map<COLNAMES, COLNAMES> renaming) {
//		Dawg<LETTER, COLNAMES> result = (Dawg<LETTER, COLNAMES>) mDawgFactory.copyDawg(this);
		
		if (this.isEmpty() || this.isUniversal()) {
			// for an empty or universal dawg we just return a fresh dawg with the new signature
			SortedSet<COLNAMES> newSignature = EprHelpers.transformSignature(mColNames, renaming);
			if (this.isEmpty()) {
				return (Dawg<LETTER, COLNAMES>) mDawgFactory.getEmptyDawg(newSignature);
			} else {
				return (Dawg<LETTER, COLNAMES>) mDawgFactory.getUniversalDawg(newSignature);
			}
		}

		Dawg<LETTER, COLNAMES> result = this;
		for (Entry<COLNAMES, COLNAMES> en : renaming.entrySet()) {
			result = new ReorderAndRenameDawgBuilder<LETTER, COLNAMES>(mDawgFactory, 
						result, 
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
			NestedMap2<DawgState, IDawgLetter<LETTER, COLNAMES>, DawgState> graph) {
		Set<DawgState> currentStates = new HashSet<DawgState>();
		currentStates.add(sourceState);
		while(!currentStates.isEmpty()) {
			final Set<DawgState> newCurrentStates = new HashSet<DawgState>();
			for (DawgState state : currentStates) {
				for (Pair<IDawgLetter<LETTER, COLNAMES>, DawgState> outgoingEdge : graph.getOutEdgeSet(state)) {
					final DawgState edgeTarget = outgoingEdge.getSecond();
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
			final IDawgLetter<LETTER, COLNAMES> columnLetter) {

		final NestedMap2<DawgState, IDawgLetter<LETTER, COLNAMES>, DawgState> newTransitionRelation
		 	= new NestedMap2<DawgState, IDawgLetter<LETTER,COLNAMES>, DawgState>();
		
		/*
		 * find the position in this Dawg's signature where the new column must be inserted
		 */
		COLNAMES rightNeighBourColumn = findRightNeighbourColumn(columnName);

		final Set<DawgState> statesLeftOfColumn;
		if (rightNeighBourColumn == null) {
			statesLeftOfColumn = getFinalStates();
		} else {
			statesLeftOfColumn = obtainStatesLeftOfColumn(rightNeighBourColumn);
		}
		
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
			for (Pair<DawgState, IDawgLetter<LETTER, COLNAMES>> incomingTransition : 
				mTransitionRelation.getInverse(en.getKey())) {
				newTransitionRelation.put(incomingTransition.getFirst(), 
						incomingTransition.getSecond(), en.getValue().getFirst());
			}
			for (Pair<IDawgLetter<LETTER, COLNAMES>, DawgState> outgoingTransition : 
				mTransitionRelation.getOutEdgeSet(en.getKey())) {
				newTransitionRelation.put(en.getValue().getSecond(), 
						outgoingTransition.getFirst(), outgoingTransition.getSecond());
			}
		}
		
		final TreeSet<COLNAMES> newSignature = new TreeSet<COLNAMES>(EprHelpers.getColumnNamesComparator());
		newSignature.addAll(mColNames);
		newSignature.add(columnName);
		return new Dawg<LETTER, COLNAMES>(mDawgFactory, mLogger, mAllConstants, newSignature, 
				newTransitionRelation, mInitialState);
	}

	/**
	 * Computes the smallest column in this Dawg's signature that is bigger than the given column.
	 * Returns null if the given column is bigger or equal than all columns in this Dawg's signature.
	 * 
	 * @param columnName
	 * @return
	 */
	COLNAMES findRightNeighbourColumn(final COLNAMES columnName) {
		COLNAMES rightNeighBourColumn = null;
		for (COLNAMES col : mColNames) {
			if (mColNames.comparator().compare(col, columnName) > 0) {
				// columName will be inserted directly left from col
				rightNeighBourColumn = col;
				break;
			}
		}
		assert rightNeighBourColumn != null || mColNames.comparator().compare(mColNames.last(), columnName) < 0;
		return rightNeighBourColumn;
	}


	@Override
	public IDawg<LETTER, COLNAMES> difference(IDawg<LETTER, COLNAMES> other) {
		if (this.isEmpty()) {
			return this;
		}
		if (other.isEmpty()) {
			return this;
		}
		if (other.isUniversal()) {
			return mDawgFactory.getEmptyDawg(getColnames());
		}
		return this.intersect(other.complement());
	}
	
	NestedMap2<DawgState, IDawgLetter<LETTER, COLNAMES>, DawgState> getTransitionRelation() {
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

	public Set<DawgState> getFinalStates() {
		assert mFinalStates != null;
		return mFinalStates;
	}
	
	@Override
	public String toString() {
		if (isEmpty()) {
			return "EmptyDawg";
		}
		if (isUniversal()) {
			return "UniversalDawg";
		}
	
		final StringBuilder sb = new StringBuilder();
		sb.append("Dawg:\n");
		sb.append(mTransitionRelation);
		
		return sb.toString();
	}
	
	/**
	 * Returns true iff in this dawg all the outgoing dawgLetters of one state are disjoint.
	 * @return
	 */
	private boolean isDeterministic() {
		for (DawgState state : mTransitionRelation.keySet()) {
			List<Pair<IDawgLetter<LETTER, COLNAMES>, DawgState>> outEdges = 
					new ArrayList<Pair<IDawgLetter<LETTER, COLNAMES>, DawgState>>(mTransitionRelation.getOutEdgeSet(state));
			for (int i = 0; i < outEdges.size(); i++) {
				Pair<IDawgLetter<LETTER, COLNAMES>, DawgState> edge1 = outEdges.get(i);
				for (int j = 0; j < i; j++) {
					Pair<IDawgLetter<LETTER, COLNAMES>, DawgState> edge2 = outEdges.get(j);
					
					if (!(edge1.getFirst().intersect(edge2.getFirst()) instanceof EmptyDawgLetter)) {
						return false;
					}
				}
			}
		}
		return true;
	}
	

}

