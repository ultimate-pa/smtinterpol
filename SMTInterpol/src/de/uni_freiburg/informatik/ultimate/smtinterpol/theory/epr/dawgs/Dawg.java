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

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Collections;
import java.util.Deque;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;
import java.util.SortedSet;
import java.util.Stack;
import java.util.TreeSet;

import de.uni_freiburg.informatik.ultimate.smtinterpol.LogProxy;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.BinaryRelation;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.EprHelpers;

/**
 * 
 * 
 * Conventions about Dawgs:
 * <li>The DawgLetters at the outgoing transition of one DawgState are all
 * disjoint. i.e. the Dawg is deterministic in the usual sense. In particular
 * there are no two outgoing edges with the same DawgLetter at any DawgState
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
	private final DeterministicDawgTransitionRelation<DawgState, IDawgLetter<LETTER, COLNAMES>, DawgState> mTransitionRelation;

	private final DawgLetterFactory<LETTER, COLNAMES> mDawgLetterFactory;
	private final DawgFactory<LETTER, COLNAMES> mDawgFactory;
	private final Set<DawgState> mFinalStates;

	private final boolean mIsSingleton;

	/**
	 * Create an empty dawg
	 * 
	 * @param logger
	 * @param allConstants
	 * @param colnames
	 */
	public Dawg(DawgFactory<LETTER, COLNAMES> df, LogProxy logger,
			SortedSet<COLNAMES> colnames) {
		super(colnames, logger);
		mDawgFactory = df;
		mDawgStateFactory = df.getDawgStateFactory();
		mDawgLetterFactory = df.getDawgLetterFactory();

		mTransitionRelation = null;

		mInitialState = null;

		mFinalStates = Collections.emptySet();

		mIsUniversal = false;
		mIsEmpty = true;
		mIsSingleton = false;
	}

	/**
	 * Creates a dawg that accepts all words of the given signature.
	 * 
	 * @param logger
	 * @param allConstants
	 * @param colnames
	 * @param fullDawg
	 */
	public Dawg(DawgFactory<LETTER, COLNAMES> df, LogProxy logger,
			SortedSet<COLNAMES> colnames, boolean fullDawg) {
		super(colnames, logger);
		assert fullDawg : "use other constructor for empty dawg";
		mDawgFactory = df;
		mDawgStateFactory = df.getDawgStateFactory();
		mDawgLetterFactory = df.getDawgLetterFactory();

		mInitialState = mDawgStateFactory.createDawgState();

		mTransitionRelation = new DeterministicDawgTransitionRelation<DawgState, IDawgLetter<LETTER, COLNAMES>, DawgState>();

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
	 * 
	 * @param logger
	 * @param allConstants
	 * @param colnames
	 * @param fullDawg
	 */
	public Dawg(final DawgFactory<LETTER, COLNAMES> df, final LogProxy logger,// final Set<LETTER> allConstants,
			final SortedSet<COLNAMES> colnames, final List<LETTER> word) {
		super(colnames, logger);

		mDawgFactory = df;
		mDawgStateFactory = df.getDawgStateFactory();
		mDawgLetterFactory = df.getDawgLetterFactory();

		mTransitionRelation = new DeterministicDawgTransitionRelation<DawgState, IDawgLetter<LETTER, COLNAMES>, DawgState>();

		mInitialState = mDawgStateFactory.createDawgState();

		DawgState currentState = mInitialState;

		for (int i = 0; i < colnames.size(); i++) {
			DawgState nextState = mDawgStateFactory.createDawgState();
			IDawgLetter<LETTER, COLNAMES> dl = mDawgLetterFactory.getSingletonSetDawgLetter(word.get(i));
			mTransitionRelation.put(currentState, dl, nextState);
			currentState = nextState;
		}
		mFinalStates = new HashSet<DawgState>();
		mFinalStates.add(currentState);

		mIsUniversal = false;
		mIsEmpty = false;
		mIsSingleton = true;
	}

	Dawg(final DawgFactory<LETTER, COLNAMES> df, final LogProxy logger, 
			final SortedSet<COLNAMES> colnames,
			final DeterministicDawgTransitionRelation<DawgState, IDawgLetter<LETTER, COLNAMES>, DawgState> transitionRelation,
			final DawgState initialState) {
		super(colnames, logger);

		mDawgFactory = df;
		mDawgStateFactory = df.getDawgStateFactory();
		mDawgLetterFactory = df.getDawgLetterFactory();

		mInitialState = initialState;

		mTransitionRelation = transitionRelation;

		mFinalStates = computeFinalStates();

		CheckEmptyUniversalSingleton<LETTER, COLNAMES> ceus = new CheckEmptyUniversalSingleton<LETTER, COLNAMES>(
				mDawgFactory, colnames.size(), initialState, transitionRelation);
		mIsEmpty = ceus.isEmpty();
		mIsSingleton = ceus.isSingleton();
		mIsUniversal = ceus.isUniversal();

		assert !containsEmptyDawgLetters(mTransitionRelation) : "transition relation contains an emptyDawgLetter"
				+ " -- EmptyDawgLetters should only used in operations on DawgLetters, not in a Dawg";
		assert EprHelpers.isDeterministic(mTransitionRelation);
		assert !EprHelpers.hasDisconnectedTransitions(transitionRelation, initialState);
	}

	private boolean containsEmptyDawgLetters(
			DeterministicDawgTransitionRelation<DawgState, IDawgLetter<LETTER, COLNAMES>, DawgState> transitionRelation) {
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

	private Set<DawgState> computeFinalStates() {
		Set<DawgState> currentStates = new HashSet<DawgState>();
		currentStates.add(mInitialState);
		for (int i = 0; i < mColNames.size(); i++) {
			final Set<DawgState> newCurrentStates = new HashSet<DawgState>();
			for (DawgState cs : currentStates) {
				// if (mTransitionRelation.get(cs) == null) {
				// continue;
				// }
				for (Pair<IDawgLetter<LETTER, COLNAMES>, DawgState> outEdge : mTransitionRelation.getOutEdgeSet(cs)) {
					newCurrentStates.add(outEdge.getSecond());
				}
			}
			currentStates = newCurrentStates;
		}
		assert finalStatesHaveNoOutgoingEdges(currentStates) == null : String.format(
				"computed %s as a final state but it has outgoing edges",
				finalStatesHaveNoOutgoingEdges(currentStates));
		return Collections.unmodifiableSet(currentStates);
	}

	/**
	 * 
	 * @param finalStates
	 * @return a final state that has at least one outgoing edge, null if there
	 *         is none
	 */
	private DawgState finalStatesHaveNoOutgoingEdges(Set<DawgState> finalStates) {
		for (DawgState finalState : finalStates) {
			if (mTransitionRelation.get(finalState) != null && !mTransitionRelation.get(finalState).isEmpty()) {
				return finalState;
			}
		}
		return null;
	}

	@Override
	public IDawg<LETTER, COLNAMES> intersect(IDawg<LETTER, COLNAMES> other) {
		assert other.getColnames().equals(this.getColnames());
		if (this.isEmpty()) {
			return this;
		}
		if (other.isEmpty()) {
			return other;
		}
		return new UnionOrIntersectionDawgBuilder<LETTER, COLNAMES>(this, (Dawg<LETTER, COLNAMES>) other, mDawgFactory)
				.buildIntersection();
	}

	@Override
	public IDawg<LETTER, COLNAMES> union(IDawg<LETTER, COLNAMES> other) {
		assert other.getColnames().equals(this.getColnames());
		if (this.isEmpty()) {
			return other;
		}
		if (other.isEmpty()) {
			return this;
		}
		return new UnionOrIntersectionDawgBuilder<LETTER, COLNAMES>(this, (Dawg<LETTER, COLNAMES>) other, mDawgFactory)
				.buildUnion();
	}

	/**
	 * Compute and return a Dawg that represents the complement of the input
	 * dawg's language. (in Sigma^n, where Sigma = allConstants and n =
	 * |colnames|)
	 */
	@Override
	public IDawg<LETTER, COLNAMES> complement() {
		/*
		 * algorithmic plan: - as usual: iterate through state "level by level"
		 * (or column by column) - in principle this performs a completion of
		 * the automaton viewed as a DFA, with some changes: -- the complement
		 * we want to compute is the complement in Sigma^|colnames|, not Sigma^*
		 * -- thus we do not introduce loops, instead we have a sink state
		 * (which is no more sink after complementation) for each level the sink
		 * state to each level has a UniversalDawgLetter-transition to the sink
		 * state in the next level -- only the "sink state" for the last level
		 * becomes an accepting state through complementation
		 */
		final DeterministicDawgTransitionRelation<DawgState, IDawgLetter<LETTER, COLNAMES>, DawgState> newTransitionRelation = new DeterministicDawgTransitionRelation<DawgState, IDawgLetter<LETTER, COLNAMES>, DawgState>();

		Set<DawgState> currentStates = new HashSet<DawgState>();
		currentStates.add(mInitialState);

		DawgState nextLevelFormerSinkState = null;

		/*
		 * the "formersinkstates" are reachable as soon as there is a state in
		 * the previous column whose outgoing transitions are not total
		 */
		boolean formerSinkStatesAreReachable = false;

		for (int i = 0; i < this.getColnames().size(); i++) {
			final Set<DawgState> nextStates = new HashSet<DawgState>();

			final DawgState lastLevelFormerSinkState = nextLevelFormerSinkState;
			nextLevelFormerSinkState = mDawgStateFactory.createDawgState();

			// if (i > 0) {
			if (formerSinkStatesAreReachable) {
				newTransitionRelation.put(lastLevelFormerSinkState, mDawgLetterFactory.getUniversalDawgLetter(),
						nextLevelFormerSinkState);
			}

			for (DawgState cs : currentStates) {
				final Set<IDawgLetter<LETTER, COLNAMES>> outgoingDawgLetters = new HashSet<IDawgLetter<LETTER, COLNAMES>>();

				/*
				 * the old transitions stay intact (except for the ones leading
				 * to the final state
				 */
				for (Pair<IDawgLetter<LETTER, COLNAMES>, DawgState> letterAndState : mTransitionRelation
						.getOutEdgeSet(cs)) {
					outgoingDawgLetters.add(letterAndState.getFirst());
					if (i != this.getColnames().size() - 1) {
						nextStates.add(letterAndState.getSecond());
						newTransitionRelation.put(cs, letterAndState.getFirst(), letterAndState.getSecond());
					}
				}

				/*
				 * collects all the DawgLetters that do not have a transition
				 * from the current state those lead to the "former sink state"
				 */
				final Set<IDawgLetter<LETTER, COLNAMES>> complementDawgLetters = mDawgLetterFactory
						.complementDawgLetterSet(outgoingDawgLetters);
				for (IDawgLetter<LETTER, COLNAMES> cdl : complementDawgLetters) {
					newTransitionRelation.put(cs, cdl, nextLevelFormerSinkState);
					formerSinkStatesAreReachable = true;
				}

			}
			currentStates = nextStates;
		}

		return new Dawg<LETTER, COLNAMES>(mDawgFactory, mLogger, mColNames, newTransitionRelation,
				mInitialState);
	}

	@Override
	public boolean accepts(List<LETTER> word) {
		assert word.size() == mColNames.size() : "word length does not match this graphs signature length";
		DawgState currentState = mInitialState;
		for (LETTER ltr : word) {
			DawgState nextState = makeTransition(currentState, ltr, word);
			if (nextState == null) {
				return false;
			}
			currentState = nextState;
		}
		// we have read the complete word
		assert mFinalStates.contains(
				currentState) : "word has been read fully but we are not in a final state?? this should not happen";
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

		DeterministicDawgTransitionRelation<DawgState, IDawgLetter<LETTER, COLNAMES>, DawgState> newTransitionRelation = new DeterministicDawgTransitionRelation<DawgState, IDawgLetter<LETTER, COLNAMES>, DawgState>();

		for (COLNAMES cn : getColnames()) {

			Set<DawgState> newCurrentColnamesPrestates = new HashSet<DawgState>();
			for (DawgState ccp : currentColnamesPrestates) {
				for (Pair<IDawgLetter<LETTER, COLNAMES>, DawgState> lts : mTransitionRelation.getOutEdgeSet(ccp)) {
					LETTER selectLetter = selectMap.get(cn);
					if (selectLetter == null) {
						// no select constraint
						// --> retain all transition and get the states before
						// the next column
						// newLetterToState.put(lts.getKey(), lts.getValue());
						newTransitionRelation.put(ccp, lts.getFirst(), lts.getSecond());
						newCurrentColnamesPrestates.add(lts.getSecond());
					} else {
						// we have a select constraint
						// --> Dawg edges that don't allow the select letter are
						// removed
						// --> Dawg edges that allow the select letter are
						// constrained to only that letter; (un)equals
						// constraints remain untouched for those
						IDawgLetter<LETTER, COLNAMES> dawgLetter = lts.getFirst();

						IDawgLetter<LETTER, COLNAMES> restrictedDL = dawgLetter.restrictToLetter(selectLetter);

						if (restrictedDL == null || restrictedDL instanceof EmptyDawgLetter<?, ?>) {
							// dawgLetter does not allow transitions with
							// selectLetter
							// --> omit transition
						} else {
							// dawgLetter does allow transitions with
							// selectLetter
							// --> replace the label of the transition by the
							// restricted letter
							// newLetterToState.put(restrictedDL,
							// lts.getValue());
							newTransitionRelation.put(ccp, restrictedDL, lts.getSecond());
							newCurrentColnamesPrestates.add(lts.getSecond());
						}
					}
				}
			}
			currentColnamesPrestates = newCurrentColnamesPrestates;
		}
		return new Dawg<LETTER, COLNAMES>(mDawgFactory, mLogger, mColNames, newTransitionRelation,
				mInitialState);
	}

	@Override
	public Iterable<List<LETTER>> getAllPointsSorted() {
		if (isEmpty()) {
			return Collections.emptySet();
		}

		if (isUniversal()) {
			return EprHelpers.computeNCrossproduct(getAllConstants(), mColNames.size(), mLogger);
		}

		Set<List<LETTER>> result = new TreeSet<List<LETTER>>(); // using a
																// TreeSet for
																// nicer
																// (sorted)
																// output
		for (List<LETTER> point : this) {
			result.add(point);
		}
		return result;
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
	public IDawg<LETTER, COLNAMES> translatePredSigToClauseSig(Map<COLNAMES, COLNAMES> translationVariables,
			Map<COLNAMES, LETTER> translationConstants, SortedSet<COLNAMES> targetSignature) {
		/*
		 * algorithmic plan: - basic operations: reorder & rename select &
		 * project blowup (or: multiple insert column operations..)
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

		/*
		 * 4. columns that are still missing from the signature are "don't care"
		 */
		SortedSet<COLNAMES> remainingColumns = new TreeSet<COLNAMES>(EprHelpers.getColumnNamesComparator());
		remainingColumns.addAll(targetSignature);
		remainingColumns.removeAll(translationVariables.values());
		for (COLNAMES col : remainingColumns) {
			result = (Dawg<LETTER, COLNAMES>) result.insertColumn(col, mDawgLetterFactory.getUniversalDawgLetter());
		}

		assert result.getColnames().equals(targetSignature);
		return result;
	}

	@Override
	public IDawg<LETTER, COLNAMES> translateClauseSigToPredSig(BinaryRelation<COLNAMES, COLNAMES> translation,
			List<Object> argList, SortedSet<COLNAMES> newSignature) {
		assert argList.size() == newSignature.size();

		/*
		 * algorithmic plan: - basic operations: insert column (for constants in
		 * argList) reorder & rename (match order from argList to order in
		 * newSignature)
		 */

		Class<? extends Object> colNamesType = newSignature.iterator().next().getClass();
		Dawg<LETTER, COLNAMES> result = (Dawg<LETTER, COLNAMES>) mDawgFactory.copyDawg(this);

		// assert new
		// TreeSet<COLNAMES>(translation.values()).equals(newSignature); -->
		// this assertion is wrong
		// because translation does not account for constants (LETTERs) in the
		// argList

		/*
		 * 1. project away all columns that we do not need (we only need those
		 * that occur in the ClauseLiteral
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
		 * 3. for the constants in argList: insert a column into the dawg where
		 * precisely that constant is accepted.
		 */
		Iterator<COLNAMES> newSigIt = newSignature.iterator();
		for (int i = 0; i < argList.size(); i++) {
			Object arg = argList.get(i);
			COLNAMES newSigColname = newSigIt.next();
			if (colNamesType.isInstance(arg)) {
				// arg is a COLNAME (typically a TermVariable)
				// assert newSigColname == translation.get(arg);
				// assert translation.getImage((COLNAMES)
				// arg).contains(newSigColname);
			} else {
				// arg must be a LETTER (typically a constant 0-ary
				// ApplicationTerm)
				insertColumn(newSigColname, mDawgLetterFactory.getSingletonSetDawgLetter((LETTER) arg));
			}
		}

		return result;
	}

	private Dawg<LETTER, COLNAMES> projectColumnAway(final COLNAMES column) {
		if (!mColNames.contains(column)) {
			return this;
		}

		final SortedSet<COLNAMES> newColnames = new TreeSet<COLNAMES>(EprHelpers.getColumnNamesComparator());
		newColnames.addAll(mColNames);
		newColnames.remove(column);

		if (this.isEmpty()) {
			return (Dawg<LETTER, COLNAMES>) mDawgFactory.getEmptyDawg(newColnames);
		}
		/*
		 * algorithmic plan: 1. obtain DawgStates directly before (set L) and
		 * after (set R) the given column 2. merge the states as if there were
		 * epsilon transitions, i.e. every edge that leads to a state l in L now
		 * leads to all the states from R that have an edge coming from l.
		 * 
		 */
		Set<DawgState> leftOfColumn = obtainStatesLeftOfColumn(column);

		final DeterministicDawgTransitionRelation<DawgState, IDawgLetter<LETTER, COLNAMES>, DawgState> newTransitionRelation = new DeterministicDawgTransitionRelation<DawgState, IDawgLetter<LETTER, COLNAMES>, DawgState>();

		final Set<DawgState> statesWhoseConnectingEdgesHaveBeenTreated;
		if (leftOfColumn.contains(mInitialState)) {
			assert leftOfColumn.size() == 1;
			/*
			 * this is a special case -- the normal procedure could give us
			 * several initial states we just merge all the states right of the
			 * projected away column into one, which is the new initial state
			 * (we reuse the old initial state for this)
			 */
			final Set<DawgState> statesRightOfColumn = obtainStatesLeftOfColumn(mColNameToIndex.get(column) + 1);
			for (DawgState sroc : statesRightOfColumn) {
				for (Pair<IDawgLetter<LETTER, COLNAMES>, DawgState> outEdge : mTransitionRelation.getOutEdgeSet(sroc)) {
					newTransitionRelation.put(mInitialState, outEdge.getFirst(), outEdge.getSecond());
				}
			}

			statesWhoseConnectingEdgesHaveBeenTreated = statesRightOfColumn;

		} else {
			/*
			 * merge states left and right of the projected away column .. by
			 * connecting the edges from the column before to the states right
			 * of the projected away column
			 */
			for (DawgState stateLeft : leftOfColumn) {
				for (Pair<DawgState, IDawgLetter<LETTER, COLNAMES>> edgeLeadingToStateLeft : mTransitionRelation
						.getInverse(stateLeft)) {
					for (Pair<IDawgLetter<LETTER, COLNAMES>, DawgState> edgeLeadingFromStateLeftToAStateRight : mTransitionRelation
							.getOutEdgeSet(stateLeft)) {
						newTransitionRelation.put(edgeLeadingToStateLeft.getFirst(), edgeLeadingToStateLeft.getSecond(),
								edgeLeadingFromStateLeftToAStateRight.getSecond());
					}
				}
			}
			statesWhoseConnectingEdgesHaveBeenTreated = leftOfColumn;
		}

		/*
		 * add all the edges from the other columns
		 */
		for (Triple<DawgState, IDawgLetter<LETTER, COLNAMES>, DawgState> edge : mTransitionRelation.entrySet()) {
			// if (leftOfColumn.contains(edge.getFirst()) ||
			// leftOfColumn.contains(edge.getThird())) {
			if (statesWhoseConnectingEdgesHaveBeenTreated.contains(edge.getFirst())
					|| statesWhoseConnectingEdgesHaveBeenTreated.contains(edge.getThird())) {
				// we have added a replacement for this edge above
				continue;
			}
			newTransitionRelation.put(edge.getFirst(), edge.getSecond(), edge.getThird());
		}

		final Dawg<LETTER, COLNAMES> result = new Dawg<LETTER, COLNAMES>(mDawgFactory, mLogger, 
				newColnames, newTransitionRelation, mInitialState);

		return result;
	}

	Set<DawgState> obtainStatesLeftOfColumn(COLNAMES rightNeighbourColumn) {
		assert !this.isEmpty() : "empty dawg has not transitionrelation and no states";
		assert mColNameToIndex.get(rightNeighbourColumn) != null : "column does not exist in this Dawg";
		return obtainStatesLeftOfColumn(mColNameToIndex.get(rightNeighbourColumn));
	}

	Set<DawgState> obtainStatesLeftOfColumn(int columnIndex) {
		Set<DawgState> result = new HashSet<DawgState>();
		result.add(mInitialState);
		for (int i = 0; i < columnIndex; i++) {
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
	 * Renames columns of the input dawg according to the given renaming. The
	 * reordering is given implicitly through the renaming because the colnames
	 * are sorted automatically.
	 * 
	 * @param other
	 * @param renaming
	 * @return
	 */
	private Dawg<LETTER, COLNAMES> reorderAndRename(BinaryRelation<COLNAMES, COLNAMES> renaming) {
		assert !renaming.getDomain().isEmpty();

		if (this.isEmpty() || this.isUniversal()) {
			// for an empty or universal dawg we just return a fresh dawg with
			// the new signature
			final SortedSet<COLNAMES> newSignature = EprHelpers.transformSignature(mColNames, renaming);
			if (this.isEmpty()) {
				return (Dawg<LETTER, COLNAMES>) mDawgFactory.getEmptyDawg(newSignature);
			} else {
				return (Dawg<LETTER, COLNAMES>) mDawgFactory.getUniversalDawg(newSignature);
			}
		}

		Dawg<LETTER, COLNAMES> result = (Dawg<LETTER, COLNAMES>) mDawgFactory.copyDawg(this);
		for (COLNAMES oldcol : renaming.getDomain()) {
			Set<COLNAMES> newCols = renaming.getImage(oldcol);
			if (newCols.size() == 1) {
				final COLNAMES newCol = newCols.iterator().next();
				// we currently assume that merging can only happen when there
				// is only one newCol
				if (result.getColnames().contains(newCol)) {
					// merge case
					result = new ReorderAndRenameDawgBuilder<LETTER, COLNAMES>(mDawgFactory, result, oldcol, newCol,
							false, true).build();
				} else {
					// normal (i.e. move column) case
					result = new ReorderAndRenameDawgBuilder<LETTER, COLNAMES>(mDawgFactory, result, oldcol, newCol)
							.build();
				}
			} else {
				/*
				 * we make the renaming for the first newCol and then trigger
				 * "column duplication" for the others
				 */
				Iterator<COLNAMES> newColIt = newCols.iterator();

				COLNAMES firstNewCol = newColIt.next();
				assert !result.getColnames().contains(firstNewCol) : "do we mix merge and duplication??";
				result = new ReorderAndRenameDawgBuilder<LETTER, COLNAMES>(mDawgFactory, result, oldcol, firstNewCol)
						.build();

				while (newColIt.hasNext()) {
					COLNAMES currentNewCol = newColIt.next();
					assert !result.getColnames().contains(currentNewCol) : "do we mix merge and duplication??";
					result = result.duplicateColumn(firstNewCol, currentNewCol);
				}
			}
		}
		return result;
	}

	/**
	 * Renames columns of the input dawg according to the given renaming. The
	 * reordering is given implicitly through the renaming because the colnames
	 * are sorted automatically.
	 * 
	 * @param other
	 * @param renaming
	 * @return
	 */
	private Dawg<LETTER, COLNAMES> reorderAndRename(Map<COLNAMES, COLNAMES> renaming) {
		return reorderAndRename(new BinaryRelation<COLNAMES, COLNAMES>(renaming));
		// // Dawg<LETTER, COLNAMES> result = (Dawg<LETTER, COLNAMES>)
		// mDawgFactory.copyDawg(this);
		//
		// if (this.isEmpty() || this.isUniversal()) {
		// // for an empty or universal dawg we just return a fresh dawg with
		// the new signature
		// SortedSet<COLNAMES> newSignature =
		// EprHelpers.transformSignature(mColNames, renaming);
		// if (this.isEmpty()) {
		// return (Dawg<LETTER, COLNAMES>)
		// mDawgFactory.getEmptyDawg(newSignature);
		// } else {
		// return (Dawg<LETTER, COLNAMES>)
		// mDawgFactory.getUniversalDawg(newSignature);
		// }
		// }
		//
		// Dawg<LETTER, COLNAMES> result = this;
		// for (Entry<COLNAMES, COLNAMES> en : renaming.entrySet()) {
		// if (result.getColnames().contains(en.getValue())) {
		// /*
		// * the renaming target column is already contained in the dawg's
		// signature
		// * this means we have to "merge" the columns, i.e., delete the old
		// column and
		// * leave only tuples in the language where the two agreed on the same
		// letter
		// */
		//
		//
		// } else {
		// // normal renaming case
		// result = new ReorderAndRenameDawgBuilder<LETTER,
		// COLNAMES>(mDawgFactory,
		// result,
		// en.getKey(),
		// en.getValue())
		// .build();
		// }
		// }
		// return result;
	}

	private Dawg<LETTER, COLNAMES> duplicateColumn(COLNAMES firstCol, COLNAMES currentNewCol) {
		if (mDawgLetterFactory.useSimpleDawgLetters()) {
			return new ReorderAndRenameDawgBuilder<LETTER, COLNAMES>(mDawgFactory, this, firstCol, currentNewCol, true)
					.build();
		} else {
			/*
			 * this is the "easy case" as our non-simple dawg-letters allow
			 * equality-constraints
			 */
			// TODO
			assert false : "TODO: implement";
			return null;
		}
	}

	/**
	 * Determines if there is a path from sourceState to targetState in graph.
	 * 
	 * TODO: naive implementation --> optimize (e.g. could be precomputed for
	 * whole graph)
	 * 
	 * @param sourceState
	 * @param targetState
	 * @param graph
	 * @return True if there is a path from source to target in graph, false
	 *         otherwise.
	 */
	static <LETTER, COLNAMES> boolean isReachableFrom(DawgState sourceState, DawgState targetState,
			DeterministicDawgTransitionRelation<DawgState, IDawgLetter<LETTER, COLNAMES>, DawgState> graph) {
		Set<DawgState> currentStates = new HashSet<DawgState>();
		currentStates.add(sourceState);
		while (!currentStates.isEmpty()) {
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
	 * We insert a column into the dawg. In that column, by convention, only one
	 * DawgLetter labels all the edges. (Should be enough for our purposes..)
	 * 
	 * @param other
	 * @param columnName
	 *            the name of the fresh column
	 * @param columnLetter
	 *            the letter that is accepted in the fresh column
	 * @return
	 */
	private IDawg<LETTER, COLNAMES> insertColumn(final COLNAMES columnName,
			final IDawgLetter<LETTER, COLNAMES> columnLetter) {

		final TreeSet<COLNAMES> newSignature = new TreeSet<COLNAMES>(EprHelpers.getColumnNamesComparator());
		newSignature.addAll(mColNames);
		newSignature.add(columnName);

		if (this.isEmpty()) {
			/*
			 * this case is special because we don't keep a transition relation
			 * for the empty dawg the empty dawg remains empty (intuitively the
			 * insert operation inserts something into every word in the
			 * language, thus does nothing if the language is empty)
			 */
			return mDawgFactory.getEmptyDawg(newSignature);
		}

		final DeterministicDawgTransitionRelation<DawgState, IDawgLetter<LETTER, COLNAMES>, DawgState> newTransitionRelation = new DeterministicDawgTransitionRelation<DawgState, IDawgLetter<LETTER, COLNAMES>, DawgState>();

		/*
		 * find the position in this Dawg's signature where the new column must
		 * be inserted
		 */
		COLNAMES rightNeighBourColumn = findRightNeighbourColumn(columnName);

		final Set<DawgState> statesLeftOfColumn;
		if (rightNeighBourColumn == null) {
			statesLeftOfColumn = getFinalStates();
		} else {
			statesLeftOfColumn = obtainStatesLeftOfColumn(rightNeighBourColumn);
		}

		/*
		 * we split each of the states where the column is to be inserted into
		 * two
		 * 
		 * there is a transition between the split states with the given letter
		 */
		Map<DawgState, Pair<DawgState, DawgState>> splitOldStateToNewSplitStatePair = new HashMap<DawgState, Pair<DawgState, DawgState>>();
		for (DawgState ds : statesLeftOfColumn) {
			DawgState newStateLeft = mDawgStateFactory.createDawgState();
			DawgState newStateRight = mDawgStateFactory.createDawgState();
			splitOldStateToNewSplitStatePair.put(ds, new Pair<DawgState, DawgState>(newStateLeft, newStateRight));
			newTransitionRelation.put(newStateLeft, columnLetter, newStateRight);
		}

		final DawgState newInitialState;
		if (statesLeftOfColumn.size() == 1 && statesLeftOfColumn.iterator().next().equals(mInitialState)) {
			// we are splitting the leftmost column --> the initial state needs
			// to be changed
			newInitialState = splitOldStateToNewSplitStatePair.get(mInitialState).getFirst();
		} else {
			// we are splitting a non-leftmost coolumn --> the initial state
			// remains unchanged
			newInitialState = mInitialState;
		}

		/*
		 * incoming transitions of the old split state now go to its left
		 * newState
		 * 
		 * outgoing transitions of the old split state now go to its right
		 * newState
		 */
		for (Entry<DawgState, Pair<DawgState, DawgState>> en : splitOldStateToNewSplitStatePair.entrySet()) {
			for (Pair<DawgState, IDawgLetter<LETTER, COLNAMES>> incomingTransition : mTransitionRelation
					.getInverse(en.getKey())) {
				newTransitionRelation.put(incomingTransition.getFirst(), incomingTransition.getSecond(),
						en.getValue().getFirst());
			}
			for (Pair<IDawgLetter<LETTER, COLNAMES>, DawgState> outgoingTransition : mTransitionRelation
					.getOutEdgeSet(en.getKey())) {
				newTransitionRelation.put(en.getValue().getSecond(), outgoingTransition.getFirst(),
						outgoingTransition.getSecond());
			}
		}

		/*
		 * For all columns other than the one we are splitting we need to copy
		 * the transitions from the original dawg's (this) transition relation.
		 */
		final Integer newColIndex = rightNeighBourColumn == null ? newSignature.size() - 1
				: mColNameToIndex.get(rightNeighBourColumn);
		Set<DawgState> currentStates = new HashSet<DawgState>();
		currentStates.add(mInitialState);
		for (int i = 0; i < mColNames.size(); i++) {
			final Set<DawgState> nextStates = new HashSet<DawgState>();

			for (DawgState cs : currentStates) {
				for (Pair<IDawgLetter<LETTER, COLNAMES>, DawgState> edge : mTransitionRelation.getOutEdgeSet(cs)) {
					nextStates.add(edge.getSecond());
					// if (newColIndex <= i - 1 && i <= newColIndex) {
					if (statesLeftOfColumn.contains(cs) || statesLeftOfColumn.contains(edge.getSecond())) {
						// around the inserted column we don't need to do
						// anything here
						continue;
					}
					newTransitionRelation.put(cs, edge.getFirst(), edge.getSecond());
				}
			}
			currentStates = nextStates;
		}

		return new Dawg<LETTER, COLNAMES>(mDawgFactory, mLogger, newSignature, newTransitionRelation,
				newInitialState);
	}

	@Override
	public IDawg<LETTER, COLNAMES> difference(IDawg<LETTER, COLNAMES> other) {
		assert other.getColnames().equals(this.getColnames());
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

	DeterministicDawgTransitionRelation<DawgState, IDawgLetter<LETTER, COLNAMES>, DawgState> getTransitionRelation() {
		return mTransitionRelation;
	}

	Set<LETTER> getAllConstants() {
		return mDawgFactory.getAllConstants();
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
		sb.append("Dawg, initial state: " + mInitialState + ", transitionrelation:\n");
		sb.append(mTransitionRelation.toString());

		return sb.toString();
	}

	/**
	 * Computes the smallest column in this Dawg's signature that is bigger than
	 * the given column. Returns null if the given column is bigger or equal
	 * than all columns in this Dawg's signature.
	 * 
	 * @param columnName
	 * @return
	 */
	public COLNAMES findRightNeighbourColumn(final COLNAMES columnName) {
		COLNAMES rightNeighBourColumn = null;
		for (COLNAMES col : mColNames) {
			if (mColNames.comparator().compare(col, columnName) > 0) {
				// columName will be inserted directly left from col
				rightNeighBourColumn = col;
				break;
			}
		}
		assert rightNeighBourColumn != null || mColNames.comparator().compare(mColNames.last(), columnName) <= 0;
		return rightNeighBourColumn;
	}

	/**
	 * 
	 * Returns null if the given column is lower or equal than all columns in
	 * this Dawg's signature.
	 * 
	 * @param newColname
	 * @return
	 */
	public COLNAMES findLeftNeighbourColumn(COLNAMES newColname) {
		COLNAMES rightNeighbour = findRightNeighbourColumn(newColname);
		if (rightNeighbour == null) {
			return mColNames.last();
		}
		if (mColNames.first().equals(rightNeighbour)) {
			return null;
		}
		return mColNames.headSet(rightNeighbour).last();
	}

	@Override
	public Iterator<List<LETTER>> iterator() {
		return new DawgIterator<LETTER, COLNAMES>(mColNames.size(), mTransitionRelation, mInitialState);
	}
}
