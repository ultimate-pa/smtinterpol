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
import java.util.HashSet;
import java.util.Map.Entry;
import java.util.Set;
import java.util.SortedSet;

import de.uni_freiburg.informatik.ultimate.smtinterpol.LogProxy;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.BinaryRelation;

/**
 * 
 * @author Alexander Nutz (nutz@informatik.uni-freiburg.de)
 *
 * @param <LETTER>
 * @param <COLNAMES>
 */
public class DeterminizeDawg<LETTER, COLNAMES> {
	
	private final DawgFactory<LETTER, COLNAMES> mDawgFactory;
	private final DawgStateFactory<LETTER, COLNAMES> mDawgStateFactory;
	private final DawgLetterFactory<LETTER, COLNAMES> mDawgLetterFactory;

	private SetDawgState mResultInitialState;
	private NestedMap2<DawgState, IDawgLetter<LETTER, COLNAMES>, DawgState> mResultTransitionRelation;
	private SortedSet<COLNAMES> mColnames;
	private Set<LETTER> mAllConstants;
	private LogProxy mLogger;
	private NestedMap2<DawgState, IDawgLetter<LETTER, COLNAMES>, DawgState> mInputTransitionRelation;
	private Set<DawgState> mInputInitialStates;



	/**
	 * The input here are the constituents of a normal Dawg except that the transition relation need not 
	 * be deterministic and there may be more than one initial state.
	 * 
	 * @param colnames
	 * @param allConstants
	 * @param logger
	 * @param transitionRelation
	 * @param initialStates
	 * @param dawgFactory
	 */
	public DeterminizeDawg(SortedSet<COLNAMES> colnames, 
			Set<LETTER> allConstants, 
			LogProxy logger,
			NestedMap2<DawgState, IDawgLetter<LETTER, COLNAMES>, DawgState> transitionRelation,
			Set<DawgState> initialStates, 
			DawgFactory<LETTER, COLNAMES> dawgFactory) {
		this.mColnames = colnames;
		this.mAllConstants = allConstants;
		this.mLogger = logger;
		this.mInputTransitionRelation = transitionRelation;
		this.mInputInitialStates = initialStates;
		this.mDawgFactory = dawgFactory;
		this.mDawgLetterFactory = dawgFactory.getDawgLetterFactory();
		this.mDawgStateFactory = dawgFactory.getDawgStateFactory();
		determinize();
	}
	
	private void determinize() {
		mResultInitialState = mDawgStateFactory.getOrCreateSetDawgState(mInputInitialStates);
		
		mResultTransitionRelation = new NestedMap2<DawgState, IDawgLetter<LETTER,COLNAMES>, DawgState>();
		
		ArrayDeque<SetDawgState> worklist = new ArrayDeque<SetDawgState>();
		worklist.add(mResultInitialState);
		while (true) {
			final SetDawgState currentSetState = worklist.pop();
		
			BinaryRelation<IDawgLetter<LETTER, COLNAMES>, IDawgLetter<LETTER, COLNAMES>> occuringDawgLetterToDividedDawgLetters =
					divideDawgLetters(currentSetState.getInnerStates());
			
			
			BinaryRelation<IDawgLetter<LETTER, COLNAMES>, DawgState> dividedDawgLetterToTargetStates =
					new BinaryRelation<IDawgLetter<LETTER,COLNAMES>, DawgState>();
			
			
			for (IDawgLetter<LETTER, COLNAMES> odl : occuringDawgLetterToDividedDawgLetters.getDomain()) {
				for (DawgState state : currentSetState.getInnerStates()) {
					final DawgState targetState = mInputTransitionRelation.get(state, odl);
					for (IDawgLetter<LETTER, COLNAMES> ddl : occuringDawgLetterToDividedDawgLetters.getImage(odl)) {
						dividedDawgLetterToTargetStates.addPair(ddl, targetState);
					}
				}
			}
			
			for (IDawgLetter<LETTER, COLNAMES> ddl : dividedDawgLetterToTargetStates.getDomain()) {
				 final SetDawgState targetSetState = mDawgStateFactory.getOrCreateSetDawgState(
						 dividedDawgLetterToTargetStates.getImage(ddl));
				 mResultTransitionRelation.put(currentSetState, ddl, targetSetState);
			}
		}
	}

	/**
	 * The input DawgStates are to be merged into one SetDawgState.
	 * Problem: their outgoing DawgLetters may partially overlap.
	 * 
	 * This methods splits all the outgoing dawgLetters into sub-DawgLetters that are disjoint. 
	 * Its result associates every outgoing DawgLetter with a set of subdawgLetters that are 
	 * disjoint (or identical) to the outgoing DawgLetters of all other states in the input set.
	 * 
	 * @param dawgStates
	 * @return
	 */
	private BinaryRelation<IDawgLetter<LETTER, COLNAMES>, IDawgLetter<LETTER, COLNAMES>> divideDawgLetters(
			Set<DawgState> dawgStates) {
		
		/*
		 * In this relation we keep the mapping between the original states and the (partially) split states.
		 */
		final BinaryRelation<IDawgLetter<LETTER, COLNAMES>, IDawgLetter<LETTER, COLNAMES>> result = 
				new BinaryRelation<IDawgLetter<LETTER,COLNAMES>, IDawgLetter<LETTER,COLNAMES>>();
	
		
		final Set<IDawgLetter<LETTER, COLNAMES>> originalDawgLetters = new HashSet<IDawgLetter<LETTER,COLNAMES>>();
		for (DawgState state : dawgStates) {
			for (Entry<IDawgLetter<LETTER, COLNAMES>, DawgState> outEdge : mInputTransitionRelation.get(state).entrySet()) {
				final IDawgLetter<LETTER, COLNAMES> originalDawgLetter = outEdge.getKey();
				originalDawgLetters.add(originalDawgLetter);
				result.addPair(originalDawgLetter, originalDawgLetter);
			}
		}
		
		
	
		/*
		 * algorithmic plan:
		 *  worklist algorithm where the worklist is the set of letters
		 *  in each iteration: 
		 *   - search for two intersecting letters l1, l2, break if there are none
		 *   - remove l1, l2, add the letters l1\l2, l1 \cap l2, l2\l1 to the worklist
		 */
		Set<IDawgLetter<LETTER, COLNAMES>> worklist = new HashSet<IDawgLetter<LETTER, COLNAMES>>(originalDawgLetters);
		while (true) {
			Pair<IDawgLetter<LETTER, COLNAMES>, IDawgLetter<LETTER, COLNAMES>> intersectingPair = 
					findIntersectingPair(worklist);
			if (intersectingPair == null) {
				// all DawgLetters in worklist are pairwise disjoint or identical --> we're done
				break;
			}
			worklist.remove(intersectingPair.getFirst());
			worklist.remove(intersectingPair.getSecond());
			

			/*
			 * update the worklist
			 */
			final IDawgLetter<LETTER, COLNAMES> intersection = intersectingPair.getFirst().intersect(intersectingPair.getSecond());
			assert !intersection.equals(mDawgLetterFactory.getEmptyDawgLetter());
			worklist.add(intersection);
			
			final Set<IDawgLetter<LETTER, COLNAMES>> difference1 = 
					intersectingPair.getFirst().difference(intersectingPair.getSecond());
			worklist.addAll(difference1);

			final Set<IDawgLetter<LETTER, COLNAMES>> difference2 = 
					intersectingPair.getSecond().difference(intersectingPair.getFirst());
			worklist.addAll(difference2);

			/*
			 * update the result map
			 */
			Set<IDawgLetter<LETTER, COLNAMES>> firstPreImage = result.getPreImage(intersectingPair.getFirst());
			Set<IDawgLetter<LETTER, COLNAMES>> secondPreImage = result.getPreImage(intersectingPair.getSecond());
			
			for (IDawgLetter<LETTER, COLNAMES> originalLetter : firstPreImage) {
				result.removePair(originalLetter, intersectingPair.getFirst());
				result.addPair(originalLetter, intersection);
				for (IDawgLetter<LETTER, COLNAMES> dl : difference1) {
					assert dl != null;
					assert !dl.equals(mDawgLetterFactory.getEmptyDawgLetter()) : "TODO: treat this case";
					result.addPair(originalLetter, dl);
				}
			}
			for (IDawgLetter<LETTER, COLNAMES> originalLetter : secondPreImage) {
				result.removePair(originalLetter, intersectingPair.getSecond());
				result.addPair(originalLetter, intersection);
				for (IDawgLetter<LETTER, COLNAMES> dl : difference2) {
					assert dl != null;
					assert !dl.equals(mDawgLetterFactory.getEmptyDawgLetter()) : "TODO: treat this case";
					result.addPair(originalLetter, dl);
				}
			}
		}
		
//		final BinaryRelation<DawgLetter<LETTER, COLNAMES>, DawgLetter<LETTER, COLNAMES>> 
//			originalLetterToIntersectingNonIdenticalLetters = 
//				new BinaryRelation<DawgLetter<LETTER,COLNAMES>, DawgLetter<LETTER,COLNAMES>>();

//		final List<DawgState> dawgStateList = new ArrayList<DawgState>(dawgStates);
//		for (int i = 0; i < dawgStateList.size(); i++) {
//			final DawgState dawgState1 = dawgStateList.get(i);
//			for (int j = 0; j < i; j++) {
//				final DawgState dawgState2 = dawgStateList.get(j);
//				for (DawgLetter<LETTER, COLNAMES> outgoingLetter1 : mInputTransitionRelation.get(dawgState1).keySet()) {
//					for (DawgLetter<LETTER, COLNAMES> outgoingLetter2 : mInputTransitionRelation.get(dawgState2).keySet()) {
//						if (outgoingLetter1.equals(outgoingLetter2)) {
//							// the letters are identical --> no need to do anything
//							continue;
//						}
//						final DawgLetter<LETTER, COLNAMES> intersection = outgoingLetter1.intersect(outgoingLetter2);
//						if (intersection.equals(mDawgLetterFactory.getEmptyDawgLetter())) {
//							// the letters don't intersect --> no need to do anything
//							continue;
//						}
////						originalLetterToIntersectingNonIdenticalLetters.addPair(outgoingLetter1, outgoingLetter2);
//						/*
//						 * Essentially, we have two sets that intersect. Say the sets are A and B, and the intersection 
//						 * is I.
//						 * Add to the result for the original DawgLetter (corresponding to A) the sets A\I and I.
//						 */
//						result.addPair(outgoingLetter1, intersection);
//						final Set<DawgLetter<LETTER, COLNAMES>> difference = outgoingLetter1.difference(outgoingLetter2);
//						for (DawgLetter<LETTER, COLNAMES> letter : difference) {
//							result.addPair(outgoingLetter1, letter);
//						}
//					}
//				}
//			}
//		}

		return result;
	}

	/**
	 * Looks in the given set of letters for a pair of letters that is non-identical and has a non-empty
	 * intersection.
	 * Returns the first such pair it finds. Returns null iff there is no such pair.
	 * 
	 * @param letters
	 * @return
	 */
	private Pair<IDawgLetter<LETTER, COLNAMES>, IDawgLetter<LETTER, COLNAMES>> findIntersectingPair(
			Set<IDawgLetter<LETTER, COLNAMES>> letters) {
		for (IDawgLetter<LETTER, COLNAMES> l1 : letters) {
			for (IDawgLetter<LETTER, COLNAMES> l2 : letters) {
				if (l1.equals(l2)) {
					continue;
				}
				if (l1.intersect(l2).equals(mDawgLetterFactory.getEmptyDawgLetter())) {
					continue;
				}
				return new Pair<IDawgLetter<LETTER,COLNAMES>, IDawgLetter<LETTER,COLNAMES>>(l1, l2);
			}
		}
		return null;
	}

	public Dawg<LETTER, COLNAMES> build() {
		assert mResultTransitionRelation != null;
		assert mResultInitialState != null;
		return new Dawg<LETTER, COLNAMES>(mDawgFactory, mLogger, 
				mAllConstants, mColnames, mResultTransitionRelation, mResultInitialState);
	}


}
