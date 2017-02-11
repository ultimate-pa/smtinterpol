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

/**
 * Builds a dawg from an input dawg according to a rule.
 * 
 * Has two modes 
 *  - reorderAndRename: renames a column in the dawg and, if its position moves, transforms the Dawg accordingly
 *    to accept the corresponding permutation language
 *  - duplication mode: duplicates a column, i.e. inserts a new column into the dawg that accepts the same letter
 *     as the duplicated column in each word
 * 
 * @author Alexander Nutz (nutz@informatik.uni-freiburg.de)
 *
 * @param <LETTER>
 * @param <COLNAMES>
 */
public class ReorderAndRenameDawgBuilder<LETTER, COLNAMES> {
	
	private final Dawg<LETTER, COLNAMES> mInputDawg;
	private final DawgFactory<LETTER, COLNAMES> mDawgFactory;
	private final DawgStateFactory<LETTER, COLNAMES> mDawgStateFactory;
	private final DawgLetterFactory<LETTER, COLNAMES> mDawgLetterFactory;
	private final COLNAMES mOldColname;
	private final COLNAMES mNewColname;
	private final boolean mDuplicationMode;

//	private DawgState mResultInitialState;
	private Set<DawgState> mResultInitialStates;
	private NestedMap2<DawgState, IDawgLetter<LETTER, COLNAMES>, DawgState> mResultTransitionRelation;
	private SortedSet<COLNAMES> mResultColnames;

	public ReorderAndRenameDawgBuilder(DawgFactory<LETTER, COLNAMES> dawgFactory, Dawg<LETTER, COLNAMES> dawg,
			COLNAMES oldColumn, COLNAMES newColumn, boolean duplicationMode) {
		mInputDawg = dawg;
		mDawgFactory = dawgFactory;
		mDawgStateFactory = dawgFactory.getDawgStateFactory();
		mDawgLetterFactory = dawgFactory.getDawgLetterFactory();
		mOldColname = oldColumn;
		mNewColname = newColumn;
		mDuplicationMode = duplicationMode;
		reorderAndRename();
	}

	public ReorderAndRenameDawgBuilder(DawgFactory<LETTER, COLNAMES> dawgFactory, Dawg<LETTER, COLNAMES> dawg,
			COLNAMES oldColumn, COLNAMES newColumn) {
		this(dawgFactory, dawg, oldColumn, newColumn, false);
	}

//	public ReorderAndRenameDawgBuilder(DawgFactory<LETTER, COLNAMES> dawgFactory, Dawg<LETTER, COLNAMES> dawg,
//			COLNAMES oldColumn, COLNAMES newColumn, boolean) {
//
//	}

	private void reorderAndRename() {
		/*
		 * case 0:
		 *   oldColName == newColName
		 *   --> nothing to do
		 */
		if(mOldColname.equals(mNewColname)) {
			
			assert !mDuplicationMode : "does this make sense?";
			
			mResultTransitionRelation = mInputDawg.getTransitionRelation();
			mResultInitialStates = Collections.singleton(mInputDawg.getInitialState());
			mResultColnames = mInputDawg.getColnames();
			return;
		}

		final COLNAMES oldRightNeighbour = mInputDawg.findRightNeighbourColumn(mOldColname);
		final COLNAMES newRightNeighbour = mInputDawg.findRightNeighbourColumn(mNewColname);

		/*
		 * case 1: the renaming does not move the column 
		 *  --> we just need to rename the column and are done
		 */
		if (!mDuplicationMode // in duplication mode we don't need a special case for this
				&& (newRightNeighbour == oldRightNeighbour // we need "=="-check for the null case
					|| (newRightNeighbour != null && newRightNeighbour.equals(oldRightNeighbour)))) {
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
		assert oldRightNeighbour == null || newRightNeighbour == null 
				|| EprHelpers.getColumnNamesComparator().compare(oldRightNeighbour, newRightNeighbour) != 0 :
			"something wrong with the comparator -- not compatible with equals!";
		
		assert oldRightNeighbour != null || newRightNeighbour != null : "should be ensured by above code";

		final boolean movesToTheRight;
		if (oldRightNeighbour == null) {
			movesToTheRight = false;
		} else if (newRightNeighbour == null) {
			movesToTheRight = true;
		} else {
			movesToTheRight = EprHelpers.getColumnNamesComparator().compare(oldRightNeighbour, newRightNeighbour) < 0;
		}
		
		final NestedMap2<DawgState, IDawgLetter<LETTER, COLNAMES>, DawgState> newTransitionRelation = 
				new NestedMap2<DawgState, IDawgLetter<LETTER,COLNAMES>, DawgState>();
	
		final Iterator<COLNAMES> oldColIterator;
		if (movesToTheRight) {
			oldColIterator = mInputDawg.getColnames().iterator();
		} else {
			oldColIterator = new LinkedList<COLNAMES>(mInputDawg.getColnames()).descendingIterator();
		}

		/*
		 * step 1:
		 *  build the new transition relation as a copy of the old transition relation until we hit
		 *  the states just before the oldColumn, don't add the edges to these states
		 */
		final Set<DawgState> statesBeforeOldColumnPreStates = reconstructUntilOldColumn(movesToTheRight, 
				newTransitionRelation, oldColIterator);
		
		/*
		 * Step 2:
		 *  algorithmic plan:
		 *   until we hit the newColumn (where the moved column is inserted)
		 *    for each letter l that can be taken in oldColumn and each state s that can be reached from an edge with that letter:
		 *      create a state saying "we're at state s and will read letter l in newColumn"
		 */
	
		/*
		 * step 2a:
		 * create the first column of RenameAndReorderDawgStates
		 */
		final Set<RenameAndReorderDawgState<LETTER, COLNAMES>> firstRnRStates;
		if (mDuplicationMode) {
			firstRnRStates = createFirstRnRStatesInDuplicationMode(newRightNeighbour,
					movesToTheRight, newTransitionRelation, statesBeforeOldColumnPreStates);
		} else {
			firstRnRStates = createFirstRnRStates(newRightNeighbour,
					movesToTheRight, newTransitionRelation, statesBeforeOldColumnPreStates);
		}
	
		/*
		 * Step 2b
		 *  add transitions for the columns between oldColumn and newColumn based on the old transition relation
		 *  and the rnrStates
		 */
		final Set<DawgState> splitPostStates = constructRnrPart(newRightNeighbour, movesToTheRight, newTransitionRelation, 
				oldColIterator, firstRnRStates);

		/*
		 * step 3:
		 *  - construct the rest of the new graph as a copy of the old graph from the splitRightStates to the end
		 */
		{
			Set<DawgState> currentStates = new HashSet<DawgState>(splitPostStates);
			while(!currentStates.isEmpty()) {
				final Set<DawgState> newCurrentStates = new HashSet<DawgState>();
				
				for (DawgState state : currentStates) {
					if (movesToTheRight) {
						for (Pair<IDawgLetter<LETTER, COLNAMES>, DawgState> outgoingEdge : 
							mInputDawg.getTransitionRelation().getOutEdgeSet(state)) {
							newTransitionRelation.put(state, outgoingEdge.getFirst(), outgoingEdge.getSecond());
							newCurrentStates.add(outgoingEdge.getSecond());
						}
					} else {
						for (Pair<DawgState, IDawgLetter<LETTER, COLNAMES>> incomingEdge : 
							mInputDawg.getTransitionRelation().getInverse(state)) {
							newTransitionRelation.put(incomingEdge.getFirst(), incomingEdge.getSecond(), state);
							newCurrentStates.add(incomingEdge.getFirst());
						}
					}
				}
				currentStates = newCurrentStates;
			}
			if (!movesToTheRight) {
				mResultInitialStates = Collections.unmodifiableSet(currentStates);
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
		
		if (!mDawgLetterFactory.useSimpleDawgLetters()) {
			// TODO
			assert false : "TODO: the equals-colnames of the DawgLetters may need updating";
		}
		
	}

	private Set<DawgState> constructRnrPart(final COLNAMES newRightNeighbour, 
			final boolean movesToTheRight,
			final NestedMap2<DawgState, IDawgLetter<LETTER, COLNAMES>, DawgState> newTransitionRelation,
			final Iterator<COLNAMES> oldColIterator,
			final Set<RenameAndReorderDawgState<LETTER, COLNAMES>> firstRnRStates) {
		final Set<DawgState> splitPostStates;
		{
			splitPostStates = new HashSet<DawgState>();
			
			// oldColIterator will give us the column directly after the moved column at this point
			COLNAMES currentColNameInOldSignature = oldColIterator.next();
			
			Set<RenameAndReorderDawgState<LETTER, COLNAMES>> currentRnRStates = 
					firstRnRStates;
			while (true) {
				if (!oldColIterator.hasNext()) {
					// the split states are the final states.
					assert newRightNeighbour == null;
					splitColumn(movesToTheRight, newTransitionRelation, splitPostStates, currentRnRStates);
					break;
				}
				
				currentColNameInOldSignature = oldColIterator.next();

				if (currentColNameInOldSignature.equals(newRightNeighbour)) {
					splitColumn(movesToTheRight, newTransitionRelation, splitPostStates, currentRnRStates);
					break;
				}
				
				final Set<RenameAndReorderDawgState<LETTER, COLNAMES>> newCurrentRnRStates = 
						new HashSet<RenameAndReorderDawgState<LETTER,COLNAMES>>();
				
				for (RenameAndReorderDawgState<LETTER, COLNAMES> rnrState : currentRnRStates) {
					if (movesToTheRight) {
						for (Pair<IDawgLetter<LETTER, COLNAMES>, DawgState> outEdgeOfInnerState : 
							mInputDawg.getTransitionRelation().getOutEdgeSet(rnrState.getInnerState())) {
							final RenameAndReorderDawgState<LETTER, COLNAMES> newTargetState = 
									mDawgStateFactory.getReorderAndRenameDawgState(
											rnrState.getLetter(), rnrState.getColumn(), outEdgeOfInnerState.getSecond());
							newCurrentRnRStates.add(newTargetState);
							newTransitionRelation.put(rnrState, outEdgeOfInnerState.getFirst(), newTargetState);
						}
					} else {
						for (Pair<DawgState, IDawgLetter<LETTER, COLNAMES>> inEdgeOfInnerState : 
							mInputDawg.getTransitionRelation().getInverse(rnrState.getInnerState())) {
							final RenameAndReorderDawgState<LETTER, COLNAMES> newSourceState = 
									mDawgStateFactory.getReorderAndRenameDawgState(
											rnrState.getLetter(), rnrState.getColumn(), inEdgeOfInnerState.getFirst());
							newCurrentRnRStates.add(newSourceState);
							newTransitionRelation.put(newSourceState, inEdgeOfInnerState.getSecond(), rnrState);
						}
					}
				}
				currentRnRStates = newCurrentRnRStates;
			}
		}
		return splitPostStates;
	}

	private void splitColumn(final boolean movesToTheRight,
			final NestedMap2<DawgState, IDawgLetter<LETTER, COLNAMES>, DawgState> newTransitionRelation,
			final Set<DawgState> splitPostStates, Set<RenameAndReorderDawgState<LETTER, COLNAMES>> currentRnRStates) {
		/*
		 * split the states in this column and insert the letter of the corresponding
		 * rnrState
		 */
		for (RenameAndReorderDawgState<LETTER, COLNAMES> rnrState : currentRnRStates) {
			final DawgState normalTargetState = rnrState.getInnerState();
			if (movesToTheRight) {
				newTransitionRelation.put(rnrState, rnrState.getLetter(), normalTargetState);
			} else {
				newTransitionRelation.put(normalTargetState, rnrState.getLetter(), rnrState);
			}
			splitPostStates.add(normalTargetState);
		}
	}

	/**
	 * create the first column of RenameAndReorderDawgStates
	 * 
	 * Note that this method does not call the oldColIterator.next() (which rests on the 
	 *  column after the moved column at this point).
	 */
	private Set<RenameAndReorderDawgState<LETTER, COLNAMES>> createFirstRnRStates(final COLNAMES newRightNeighbour,
			final boolean movesToTheRight,
			final NestedMap2<DawgState, IDawgLetter<LETTER, COLNAMES>, DawgState> newTransitionRelation,
			final Set<DawgState> statesBeforeOldColumnPreStates) {

		final Set<RenameAndReorderDawgState<LETTER,COLNAMES>> firstRnRStates = 
				new HashSet<RenameAndReorderDawgState<LETTER,COLNAMES>>();
		if (statesBeforeOldColumnPreStates == null) {
			/*
			 *  special case: the oldColumn is the first column
			 *   this means we may have more than one initial state in the result
			 */
			mResultInitialStates = new HashSet<DawgState>();
			if (movesToTheRight) {
				for (Pair<IDawgLetter<LETTER, COLNAMES>, DawgState> edgeFromInitialToNextState : 
					mInputDawg.getTransitionRelation().getOutEdgeSet(mInputDawg.getInitialState())) {
					final RenameAndReorderDawgState<LETTER, COLNAMES> rnrState = 
							mDawgStateFactory.getReorderAndRenameDawgState(
											edgeFromInitialToNextState.getFirst(), 
											newRightNeighbour, 
											edgeFromInitialToNextState.getSecond());
					firstRnRStates.add(rnrState);
					mResultInitialStates.add(rnrState);
				}
			} else {
				for (DawgState finalState : mInputDawg.getFinalStates()) {
					for (Pair<DawgState, IDawgLetter<LETTER, COLNAMES>> edgeFromFinalToBeforeState : 
						mInputDawg.getTransitionRelation().getInverse(finalState)) {
						final RenameAndReorderDawgState<LETTER, COLNAMES> rnrState = 
								mDawgStateFactory.getReorderAndRenameDawgState(
										edgeFromFinalToBeforeState.getSecond(), 
										newRightNeighbour, 
										edgeFromFinalToBeforeState.getFirst());
						firstRnRStates.add(rnrState);
					}
				}
			}
		} else {
			if (movesToTheRight) {
				for (DawgState prePreState : statesBeforeOldColumnPreStates) {
					for (Pair<IDawgLetter<LETTER, COLNAMES>, DawgState> edgeFromPrePreStateToPreState : 
						mInputDawg.getTransitionRelation().getOutEdgeSet(prePreState)) {

						final DawgState stateLeft = edgeFromPrePreStateToPreState.getSecond();

						for (Pair<IDawgLetter<LETTER, COLNAMES>, DawgState> edgeInOldColumn : 
							mInputDawg.getTransitionRelation().getOutEdgeSet(stateLeft)) {

							final RenameAndReorderDawgState<LETTER, COLNAMES> newEdgeTarget =
									mDawgStateFactory.getReorderAndRenameDawgState(
											edgeInOldColumn.getFirst(), newRightNeighbour, edgeInOldColumn.getSecond());
							firstRnRStates.add(newEdgeTarget);

							newTransitionRelation.put(prePreState, edgeFromPrePreStateToPreState.getFirst(), newEdgeTarget);
						}
					}
				}
			} else {
				for (DawgState prePreState : statesBeforeOldColumnPreStates) {
					for (Pair<DawgState, IDawgLetter<LETTER, COLNAMES>> edgeFromPrePreStateToPreState : 
						mInputDawg.getTransitionRelation().getInverse(prePreState)) {

						final DawgState stateRight = edgeFromPrePreStateToPreState.getFirst();

						for (Entry<IDawgLetter<LETTER, COLNAMES>, DawgState> edgeInOldColumn : 
							mInputDawg.getTransitionRelation().get(stateRight).entrySet()) {

							final RenameAndReorderDawgState<LETTER, COLNAMES> newEdgeSource =
									mDawgStateFactory.getReorderAndRenameDawgState(
											edgeInOldColumn.getKey(), newRightNeighbour, edgeInOldColumn.getValue());
							firstRnRStates.add(newEdgeSource);

							newTransitionRelation.put(newEdgeSource, edgeFromPrePreStateToPreState.getSecond(), prePreState);
						}
					}
				}

			}
		}
		return firstRnRStates;
	}


	private Set<RenameAndReorderDawgState<LETTER, COLNAMES>> createFirstRnRStatesInDuplicationMode(
		final COLNAMES newRightNeighbour, 
		final boolean movesToTheRight,
		final NestedMap2<DawgState, IDawgLetter<LETTER, COLNAMES>, DawgState> newTransitionRelation,
		final Set<DawgState> statesBeforeOldColumnPreStates) {
		
		/*
		 *  reconstruct one more column
		 */
		final Set<DawgState> statesBeforeDuplicatedColumn = new HashSet<DawgState>();
		if (movesToTheRight) {
			for (DawgState preState : statesBeforeOldColumnPreStates) {
				for (Pair<IDawgLetter<LETTER, COLNAMES>, DawgState> outEdge : 
						mInputDawg.getTransitionRelation().getOutEdgeSet(preState)) {
					newTransitionRelation.put(preState, outEdge.getFirst(), outEdge.getSecond());
					statesBeforeDuplicatedColumn.add(outEdge.getSecond());
				}
			}
		} else {
			for (DawgState preState : statesBeforeOldColumnPreStates) {
				for (Pair<DawgState, IDawgLetter<LETTER, COLNAMES>> inEdge : 
						mInputDawg.getTransitionRelation().getInverse(preState)) {
					newTransitionRelation.put(inEdge.getFirst(), inEdge.getSecond(), preState);
					statesBeforeDuplicatedColumn.add(inEdge.getFirst());
				}
			}		
		}
		
		/*
		 * leave the edges in the duplicated column as they are but replace the states with 
		 * the appropriate "RenameAndReorderStates"
		 */
		final Set<RenameAndReorderDawgState<LETTER, COLNAMES>> firstRnrStates = 
				new HashSet<RenameAndReorderDawgState<LETTER,COLNAMES>>();
		if (movesToTheRight) {
			for (DawgState preState : statesBeforeDuplicatedColumn) {
				for (Pair<IDawgLetter<LETTER, COLNAMES>, DawgState> outEdge : 
						mInputDawg.getTransitionRelation().getOutEdgeSet(preState)) {
					
					RenameAndReorderDawgState<LETTER, COLNAMES> rnrState = mDawgStateFactory.getReorderAndRenameDawgState(
							outEdge.getFirst(), newRightNeighbour, outEdge.getSecond());
					newTransitionRelation.put(preState, outEdge.getFirst(), rnrState);
					firstRnrStates.add(rnrState);
				}
			}
		} else {
			for (DawgState preState : statesBeforeDuplicatedColumn) {
				for (Pair<DawgState, IDawgLetter<LETTER, COLNAMES>> inEdge : 
						mInputDawg.getTransitionRelation().getInverse(preState)) {

					RenameAndReorderDawgState<LETTER, COLNAMES> rnrState = mDawgStateFactory.getReorderAndRenameDawgState(
							inEdge.getSecond(), newRightNeighbour, inEdge.getFirst());
					newTransitionRelation.put(rnrState, inEdge.getSecond(), preState);
					firstRnrStates.add(rnrState);
				}
			}
		}
		return firstRnrStates;
	}

	/**
	 *  builds the new transition relation as a copy of the old transition relation until we hit
	 *  the states just before the oldColumn, returns the last column of states before the old column
	 */
	private Set<DawgState> reconstructUntilOldColumn(boolean movesToTheRight,
			NestedMap2<DawgState, IDawgLetter<LETTER, COLNAMES>, DawgState> newTransitionRelation, 
			Iterator<COLNAMES> oldColIterator) {
		/**
		 * the states one column before the states directly left of oldColumn
		 *  the algorithm in step 2 start on these states
		 */
		Set<DawgState> statesBeforeOldColumnPreStates = null;
		{
			boolean hitStatesBeforeOldColumn = false;

			final COLNAMES nextColName0 = oldColIterator.next();
			if (nextColName0.equals(mOldColname)) {
				// when oldColum is the first column, this is a special case
				// we mark this by setting statesBeforeOldColumnLeftStates to null
				
				statesBeforeOldColumnPreStates = null;
			} else {
				mResultInitialStates = Collections.singleton(mInputDawg.getInitialState());
				Set<DawgState> currentStates = new HashSet<DawgState>();
				if (movesToTheRight) {
					currentStates.add(mInputDawg.getInitialState());
				} else {
					currentStates.addAll(mInputDawg.getFinalStates());
				}

				while (true) {

					// nextColName is updated before currentStates 
					//  --> it points to the column after the one we are adding edges for
					final COLNAMES nextColName = oldColIterator.next();
					hitStatesBeforeOldColumn = nextColName.equals(mOldColname);
					if (hitStatesBeforeOldColumn) {
						// when currentColumn has arrived at oldColumn, we don't copy the edges (as they
						// will be redirected to fresh states in step 2)
						statesBeforeOldColumnPreStates = currentStates;
						break;
					}

					final Set<DawgState> newCurrentStates = new HashSet<DawgState>();
					// add the edges from the old graph in the column before currentColumn
					for (DawgState currentState : currentStates) {

						if (movesToTheRight) {
							/*
							 * obtain outgoing edges from currentState
							 */
							final Set<Pair<IDawgLetter<LETTER, COLNAMES>, DawgState>> edgeSet = 
								new HashSet<Pair<IDawgLetter<LETTER,COLNAMES>,DawgState>>();
							for (Pair<IDawgLetter<LETTER, COLNAMES>, DawgState> en : 
								mInputDawg.getTransitionRelation().getOutEdgeSet(currentState)) {
								edgeSet.add(new Pair<IDawgLetter<LETTER,COLNAMES>, DawgState>(en.getFirst(), en.getSecond()));
							}
							
							/*
							 * update new transition relation and currentStates
							 */
							for (Pair<IDawgLetter<LETTER, COLNAMES>, DawgState> outGoingEdge : edgeSet) {
								newCurrentStates.add(outGoingEdge.getSecond());
								newTransitionRelation.put(currentState, outGoingEdge.getFirst(), outGoingEdge.getSecond());
							}
						} else {
							/*
							 * obtain incoming edges to currentState
							 */
							final Set<Pair<IDawgLetter<LETTER, COLNAMES>, DawgState>> edgeSet = 
								new HashSet<Pair<IDawgLetter<LETTER,COLNAMES>,DawgState>>();
							for (Pair<DawgState, IDawgLetter<LETTER, COLNAMES>> p : 
								mInputDawg.getTransitionRelation().getInverse(currentState)) {
								edgeSet.add(
										new Pair<IDawgLetter<LETTER,COLNAMES>, DawgState>(p.getSecond(), p.getFirst()));
							}

							/*
							 * update new transition relation and currentStates
							 */
							for (Pair<IDawgLetter<LETTER, COLNAMES>, DawgState> outGoingEdge : edgeSet) {
								newCurrentStates.add(outGoingEdge.getSecond());
								newTransitionRelation.put(outGoingEdge.getSecond(), outGoingEdge.getFirst(), currentState);
							}
						}


					}
					currentStates = newCurrentStates;
				}
			}
			
		}
		return statesBeforeOldColumnPreStates;
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
