package de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.dawgs;

import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.Map;
import java.util.Set;
import java.util.SortedSet;
import java.util.TreeSet;
import java.util.Map.Entry;

import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.EprHelpers;

public class ReorderAndRenameDawgBuilder<LETTER, COLNAMES> {
	
	private final Dawg<LETTER, COLNAMES> mInputDawg;
	private final DawgFactory<LETTER, COLNAMES> mDawgFactory;
	private final DawgStateFactory mDawgStateFactory;
	private final DawgLetterFactory<LETTER, COLNAMES> mDawgLetterFactory;
	private final COLNAMES mOldColname;
	private final COLNAMES mNewColname;

//	private DawgState mResultInitialState;
	private Set<DawgState> mResultInitialStates;
	private NestedMap2<DawgState, DawgLetter<LETTER, COLNAMES>, DawgState> mResultTransitionRelation;
	private SortedSet<COLNAMES> mResultColnames;

	public ReorderAndRenameDawgBuilder(DawgFactory<LETTER, COLNAMES> dawgFactory, Dawg<LETTER, COLNAMES> dawg,
			COLNAMES oldColumn, COLNAMES newColumn) {
		mInputDawg = dawg;
		mDawgFactory = dawgFactory;
		mDawgStateFactory = dawgFactory.getDawgStateFactory();
		mDawgLetterFactory = dawgFactory.getDawgLetterFactory();
		mOldColname = oldColumn;
		mNewColname = newColumn;
		reorderAndRename();
	}

	private void reorderAndRename() {
		/*
		 * case 0:
		 *   oldColName == newColName
		 *   --> nothing to do
		 */
		if(mOldColname.equals(mNewColname)) {
			mResultTransitionRelation = mInputDawg.getTransitionRelation();
			mResultInitialStates = Collections.singleton(mInputDawg.getInitialState());
			mResultColnames = mInputDawg.getColnames();
			return;
		}

		COLNAMES oldRightNeighbour = mInputDawg.findRightNeighbourColumn(mOldColname);
		COLNAMES newRightNeighbour = mInputDawg.findRightNeighbourColumn(mNewColname);

		/*
		 * case 1: the renaming does not move the column 
		 *  --> we just need to rename the column and are done
		 */
		if (newRightNeighbour.equals(oldRightNeighbour)) {
			SortedSet<COLNAMES> newColNames = new TreeSet<COLNAMES>(EprHelpers.getColumnNamesComparator());
			newColNames.addAll(mInputDawg.getColnames());
			newColNames.remove(mOldColname);
			newColNames.add(mNewColname);
			mResultColnames = newColNames;
			mResultTransitionRelation = mInputDawg.getTransitionRelation().copy(); 
			mResultInitialStates = Collections.singleton(mInputDawg.getInitialState());
			return;
		}
		
		/*
		 * case 2: the renaming does move the column
		 *  2a: the column moves left (i.e. towards the initial state)
		 *  2b: the column moves right (i.e. towards the final state)
		 *  
		 *  cases 2a and 2b are treated by the same code, parameterized in the direction the column moves
		 *   our algorithm will "move through the graph" in the same direction as the column
		 */
		assert EprHelpers.getColumnNamesComparator().compare(oldRightNeighbour, newRightNeighbour) != 0 :
			"something wrong with the comparator -- not compatible with equals!";
		boolean movesToTheRight = 
				EprHelpers.getColumnNamesComparator().compare(oldRightNeighbour, newRightNeighbour) < 0;
		
		
		
		
		NestedMap2<DawgState, DawgLetter<LETTER, COLNAMES>, DawgState> newTransitionRelation = 
				new NestedMap2<DawgState, DawgLetter<LETTER,COLNAMES>, DawgState>();
		/*
		 * step 1:
		 *  build the new transition relation as a copy of the old transition relation until we hit
		 *  the states just before the oldColumn, don't add the edges to these states
		 */
		
		/**
		 * the states one column before the states directly left of oldColumn
		 *  the algorithm in step 2 start on these states
		 */
		Set<DawgState> statesBeforeOldColumnLeftStates = null;
		{
			final Iterator<COLNAMES> oldColIterator;
			if (movesToTheRight) {
				oldColIterator = mInputDawg.getColnames().iterator();
			} else {
				oldColIterator = new LinkedList<COLNAMES>(mInputDawg.getColnames()).descendingIterator();
			}
			boolean hitStatesBeforeOldColumn = false;

			final COLNAMES nextColName0 = oldColIterator.next();
			if (nextColName0.equals(mOldColname)) {
				// when oldColum is the first column, this is a special case
				// we mark this by setting statesBeforeOldColumnLeftStates to null
				
				statesBeforeOldColumnLeftStates = null;
			} else {
				mResultInitialStates = Collections.singleton(mInputDawg.getInitialState());
				Set<DawgState> currentStates = new HashSet<DawgState>();
				if (movesToTheRight) {
					currentStates.add(mInputDawg.getInitialState());
				} else {
					// TODO: add all final states
					assert false : "TODO";
				}

				while (true) {

					// nextColName is updated before currentStates 
					//  --> it points to the column after the one we are adding edges for
					final COLNAMES nextColName = oldColIterator.next();
					hitStatesBeforeOldColumn = nextColName.equals(mOldColname);
					if (hitStatesBeforeOldColumn) {
						// when currentColumn has arrived at oldColumn, we don't copy the edges (as they
						// will be redirected to fresh states in step 2
						statesBeforeOldColumnLeftStates = currentStates;
						break;
					}

					final Set<DawgState> newCurrentStates = new HashSet<DawgState>();
					// add the edges from the old graph in the column before currentColumn
					for (DawgState currentState : currentStates) {
						for (Entry<DawgLetter<LETTER, COLNAMES>, DawgState> outGoingEdge : 
							mInputDawg.getTransitionRelation().get(currentState).entrySet()) {
							newCurrentStates.add(outGoingEdge.getValue());
							newTransitionRelation.put(currentState, outGoingEdge.getKey(), outGoingEdge.getValue());
						}
					}
					currentStates = newCurrentStates;
				}
			}
			
		}
		
		/*
		 * step 2:
		 *  build the graph between the oldColumn and the insertion point of the new
		 *  column as follows.
		 * 
		 *  pseudocode:
		 *  input: source column src, target column trg (insert to the right of trg)
         *    for each edge (s, l, t) in src:
         *      create a fresh state ("s,t")
         *      each edge that led to s now leads to ("s,t")
         *    
         *      for each state q right of the target column:
         *        create a fresh state ("s,t,q")
         *        connect the states ("s,t") and ("s,t,q") through a copy the subgraph between t and q
         *        connect the states ("s,t,q") and q through an edge labelled l
		 */
		
		/*
		 * step 2a:
		 *  create the ("s,t")-states (also called mergedStates because they stand for two states connected by
		 *   and edge in oldColumn that are now one state), 
		 *  add the edges leading to them, store them 
		 */
		final Set<PairDawgState> mergedStates = new HashSet<PairDawgState>();
		if (statesBeforeOldColumnLeftStates == null) {
			// special case: the oldColumn is the first column
			for (Entry<DawgLetter<LETTER, COLNAMES>, DawgState> edgeFromInitialToNextState : 
				mInputDawg.getTransitionRelation().get(mInputDawg.getInitialState()).entrySet()) {
				final PairDawgState mergedState = 
						new PairDawgState(mInputDawg.getInitialState(), edgeFromInitialToNextState.getValue());
				mergedStates.add(mergedState);
				mResultInitialStates.add(mergedState);
			}
		} else {
			for (DawgState leftLeftState : statesBeforeOldColumnLeftStates) {
				for (Entry<DawgLetter<LETTER, COLNAMES>, DawgState> edgeFromLeftLeftStateToLeftState : 
					mInputDawg.getTransitionRelation().get(leftLeftState).entrySet()) {

					final DawgState stateLeft = edgeFromLeftLeftStateToLeftState.getValue();

					for (Entry<DawgLetter<LETTER, COLNAMES>, DawgState> edgeInOldColumn : 
						mInputDawg.getTransitionRelation().get(stateLeft).entrySet()) {

						final PairDawgState newEdgeTarget =  // the state ("s, t")
								mDawgStateFactory.getOrCreatePairDawgState(stateLeft, edgeInOldColumn.getValue());
						mergedStates.add(newEdgeTarget);

						newTransitionRelation.put(leftLeftState, edgeFromLeftLeftStateToLeftState.getKey(), newEdgeTarget);
					}
				}
			}
		}
	
		/*
		 * step 2b:
		 * - Create the "tripleStates" ("s,t,q"), each from a mergedState and a "splitState"
		 *   a splitState is a state in the state-column left of the "newRightNeighbour"-column.
		 * - connect each mergedState ("s,t") with its tripleState ("s,t,q") through a copy of the the subgraph that 
		 *   connects t and q in the original Dawg
		 * - collect all the tripleStates"
		 *  
		 */
		final Set<PairDawgState> tripleStates = new HashSet<PairDawgState>();
		for (PairDawgState mergedState : mergedStates) {
			for (DawgState splitState : mInputDawg.obtainStatesLeftOfColumn(newRightNeighbour)) {
				final PairDawgState tripleState = mDawgStateFactory.getOrCreatePairDawgState(mergedState, splitState);
				tripleStates.add(tripleState);
				
				if (!Dawg.isReachableFrom(mergedState.getSecond(), tripleState.getSecond(), mInputDawg.getTransitionRelation())) {
					// TODO treat this case
					assert false : "TODO";
				}
				connectThroughCopiedSubDawg(mergedState, tripleState, mInputDawg.getTransitionRelation(), newTransitionRelation);
			}
		}
		
		/*
		 * step 2c:
		 *  - connect each tripleState ((s,t),q) with its last entry q through an edge labelled with the letter
		 *    that labelled the edge (s,t) in the original graph
		 *  - collect the states q, also called the splitRightStates, (the tripleStates would be the splitLeftStates
		 *    in that logic) in order to go on from there
		 */
		final Set<DawgState> splitRightStates = new HashSet<DawgState>();
		for (PairDawgState tripleState : tripleStates) {
			final PairDawgState mergedState = (PairDawgState) tripleState.getFirst();
			final Set<DawgLetter<LETTER, COLNAMES>> connectingLetters = 
					getConnectingLetters(mergedState.getFirst(), mergedState.getSecond(), mInputDawg.getTransitionRelation());
			final DawgState splitRightState = tripleState.getSecond();
			splitRightStates.add(splitRightState);
			for (DawgLetter<LETTER, COLNAMES> connectingLetter : connectingLetters) {
				newTransitionRelation.put(tripleState, connectingLetter, splitRightState);
			}
		}
		
		/*
		 * step 3:
		 *  - construct the rest of the new graph as a copy of the old graph from the splitRightStates to the end
		 */
		{
			Set<DawgState> currentStates = new HashSet<DawgState>(splitRightStates);
			while(!currentStates.isEmpty()) {
				final Set<DawgState> newCurrentStates = new HashSet<DawgState>();
				
				for (DawgState state : currentStates) {
					for (Entry<DawgLetter<LETTER, COLNAMES>, DawgState> outgoingEdge : 
							mInputDawg.getTransitionRelation().get(state).entrySet()) {
						newTransitionRelation.put(state, outgoingEdge.getKey(), outgoingEdge.getValue());
						newCurrentStates.add(outgoingEdge.getValue());
					}
				}
				currentStates = newCurrentStates;
			}
		}
		
		/*
		 * step 4: compute new signature
		 */
		SortedSet<COLNAMES> newColNames = new TreeSet<COLNAMES>(EprHelpers.getColumnNamesComparator());
		newColNames.addAll(mInputDawg.getColnames());
		newColNames.remove(mOldColname);
		newColNames.add(mNewColname);
		
		
		mResultColnames = newColNames;
		mResultTransitionRelation = newTransitionRelation;
	}

	private static <LETTER, COLNAMES> Set<DawgLetter<LETTER, COLNAMES>> getConnectingLetters(DawgState first, DawgState second,
			NestedMap2<DawgState, DawgLetter<LETTER, COLNAMES>, DawgState> transitionRelation) {
		final Set<DawgLetter<LETTER, COLNAMES>> result = new HashSet<DawgLetter<LETTER,COLNAMES>>();
		for (Entry<DawgLetter<LETTER, COLNAMES>, DawgState> outEdge : transitionRelation.get(first).entrySet()) {
			if (outEdge.getValue().equals(second)) {
				result.add(outEdge.getKey());
			}
		}
		return result;
	}

	/**
	 * Consider the last entries of mergedState and tripleState, t and q.
	 * Compute the SubDawg that connects t and q in oldTransitionRelation.
	 * Make a copy of that SubDawg (with all new states) and connect mergedState and tripleState
	 * by it in newTransitionRelation.
	 * 
	 * @param mergedState
	 * @param tripleState
	 * @param oldTransitionRelation
	 * @param newTransitionRelation This is the graph that is updated in this method.
	 */
	private void connectThroughCopiedSubDawg(PairDawgState mergedState, PairDawgState tripleState,
			NestedMap2<DawgState, DawgLetter<LETTER, COLNAMES>, DawgState> oldTransitionRelation,
			NestedMap2<DawgState, DawgLetter<LETTER, COLNAMES>, DawgState> newTransitionRelation) {
		
		final DawgState subDawgSourceInOldGraph = mergedState.getSecond();
		
		final DawgState subDawgTargetInOldGraph = tripleState.getSecond();
		
		Set<DawgState> currentStatesInOldGraph = new HashSet<DawgState>();
		currentStatesInOldGraph.add(subDawgSourceInOldGraph);

		final Map<DawgState, DawgState> oldStateToNewState = new HashMap<DawgState, DawgState>();
		oldStateToNewState.put(subDawgSourceInOldGraph, mergedState);
		oldStateToNewState.put(subDawgTargetInOldGraph, tripleState);

		boolean hasReachedSubDawgTarget = false;

		while (!hasReachedSubDawgTarget) { // moves through the columns
			final Set<DawgState> newCurrentStatesInOldGraph = new HashSet<DawgState>();

			for (DawgState state : currentStatesInOldGraph) {
				final DawgState newSourceState = oldStateToNewState.get(state);
				assert newSourceState != null;
				
				for (Entry<DawgLetter<LETTER, COLNAMES>, DawgState> outgoingEdge : 
						oldTransitionRelation.get(state).entrySet()) {

					final DawgState oldTargetState = outgoingEdge.getValue();
					if (!Dawg.isReachableFrom(oldTargetState, subDawgTargetInOldGraph, oldTransitionRelation)) {
						// the target state of the subDawg cannot be reached if we take the current outgoingEdge
						//  --> don't add the edge to the new subDawg
						continue;
					}

					newCurrentStatesInOldGraph.add(oldTargetState);

					if (oldTargetState.equals(subDawgTargetInOldGraph)) {
						hasReachedSubDawgTarget = true;
					}

					// we only want one copy for each old state
					DawgState newTargetState = 
							oldStateToNewState.get(oldTargetState);
					if (newTargetState == null) {
						newTargetState = mDawgStateFactory.createDawgState();
						oldStateToNewState.put(outgoingEdge.getValue(), newTargetState);
					}
					
					// create the new transition
					newTransitionRelation.put(newSourceState, outgoingEdge.getKey(), newTargetState);
				}
			
			
			}
			currentStatesInOldGraph = newCurrentStatesInOldGraph;
		}
	}

	public Dawg<LETTER, COLNAMES> build() {
		assert mResultColnames != null;
		assert mResultTransitionRelation != null;
		assert mResultInitialStates != null;
		return new DeterminizeDawg<LETTER, COLNAMES>(mResultColnames, 
				mInputDawg.getAllConstants(), 
				mInputDawg.getLogger(), 
				mResultTransitionRelation,
				mResultInitialStates,
				mDawgFactory).build();
	}



}
