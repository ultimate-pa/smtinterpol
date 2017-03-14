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
package de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.dawgs.dawgbuilders;

import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.BinaryRelation;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.EprHelpers;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.dawgs.Dawg;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.dawgs.DawgFactory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.dawgs.DeterministicDawgTransitionRelation;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.dawgs.dawgletters.DawgLetterFactory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.dawgs.dawgletters.IDawgLetter;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.dawgs.dawgstates.DawgState;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.dawgs.dawgstates.DawgStateFactory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.dawgs.dawgstates.PairDawgState;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.util.Pair;

import java.util.Map.Entry;

/**
 * 
 * @author Alexander Nutz (nutz@informatik.uni-freiburg.de)
 *
 * @param <LETTER>
 * @param <COLNAMES>
 */
public class UnionOrIntersectionDawgBuilder<LETTER, COLNAMES> {
	
	private final DawgState mResultInitialState;
	private final DawgStateFactory<LETTER, COLNAMES> mDawgStateFactory;
	private final DeterministicDawgTransitionRelation<DawgState, IDawgLetter<LETTER, COLNAMES>, DawgState> mResultTransitionRelation;
	private final Dawg<LETTER, COLNAMES> mFirstInputDawg;
	private final Dawg<LETTER, COLNAMES> mSecondInputDawg;
	private final DawgLetterFactory<LETTER, COLNAMES> mDawgLetterFactory;
	private final DawgFactory<LETTER, COLNAMES> mDawgFactory;

	public UnionOrIntersectionDawgBuilder(Dawg<LETTER, COLNAMES> first, Dawg<LETTER, COLNAMES> second, 
			DawgFactory<LETTER, COLNAMES> df) {
		assert first.getSignature().equals(second.getSignature()) : "signatures don't match!";
		mDawgFactory = df;
		mDawgStateFactory = df.getDawgStateFactory();
		mDawgLetterFactory = df.getDawgLetterFactory();
		
		mFirstInputDawg = first; 
		mSecondInputDawg = second;
		
		mResultTransitionRelation = new DeterministicDawgTransitionRelation<DawgState, IDawgLetter<LETTER,COLNAMES>,DawgState>();

		mResultInitialState = new PairDawgState(first.getInitialState(), second.getInitialState());
		
	}
	
	public Dawg<LETTER, COLNAMES> buildUnion() {
		return build(true);
	}
	
	public Dawg<LETTER, COLNAMES> buildIntersection() {
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
		currentStates.add((PairDawgState) mResultInitialState);
		
		for (int i = 0; i < mFirstInputDawg.getColNames().size(); i++) {
			final Set<PairDawgState> nextStates = new HashSet<PairDawgState>();
			
			for (PairDawgState cs : currentStates) {
				
				if (!cs.isFirstSink() && !cs.isSecondSink()) {
					
					final BinaryRelation<IDawgLetter<LETTER, COLNAMES>, IDawgLetter<LETTER, COLNAMES>> dividedDawgLetters = 
							EprHelpers.divideDawgLetters(mDawgLetterFactory, 
									cs.getFirst(), 
									cs.getSecond(),
									mFirstInputDawg.getTransitionRelation(), 
									mSecondInputDawg.getTransitionRelation());
					
					for (IDawgLetter<LETTER, COLNAMES> origDl : dividedDawgLetters.getDomain()) {
						final DawgState firstTargetWithOrigDl = mFirstInputDawg.getTransitionRelation().get(cs.getFirst(), origDl);
						final DawgState secondTargetWithOrigDl = mSecondInputDawg.getTransitionRelation().get(cs.getSecond(), origDl);
						assert firstTargetWithOrigDl != null || secondTargetWithOrigDl != null;

						for (IDawgLetter<LETTER, COLNAMES> dividedDl : dividedDawgLetters.getImage(origDl)) {
							
							if (firstTargetWithOrigDl != null && secondTargetWithOrigDl != null) {
								final PairDawgState newState = mDawgStateFactory.getOrCreatePairDawgState(
										firstTargetWithOrigDl, secondTargetWithOrigDl);
								nextStates.add(newState);
								mResultTransitionRelation.put(cs, dividedDl, newState);
							} else if (doUnion && firstTargetWithOrigDl == null && secondTargetWithOrigDl != null) {
								final PairDawgState newState = mDawgStateFactory.getOrCreatePairDawgState(
										secondTargetWithOrigDl, true, false);
								nextStates.add(newState);
								mResultTransitionRelation.put(cs, dividedDl, newState);
							} else if (doUnion && firstTargetWithOrigDl != null && secondTargetWithOrigDl == null) {
								final PairDawgState newState = mDawgStateFactory.getOrCreatePairDawgState(
										firstTargetWithOrigDl, false, true);
								nextStates.add(newState);
								mResultTransitionRelation.put(cs, dividedDl, newState);
							}
						}
					}
				} else if (doUnion && cs.isSecondSink()) {
					for (Pair<IDawgLetter<LETTER, COLNAMES>, DawgState> firstOutEdge : 
						mFirstInputDawg.getTransitionRelation().getOutEdgeSet(cs.getFirst())) {

						final PairDawgState ds = mDawgStateFactory.getOrCreatePairDawgState(firstOutEdge.getSecond(), false, true);
						nextStates.add(ds);
						mResultTransitionRelation.put(cs, firstOutEdge.getFirst(), ds);
						assert !EprHelpers.areStatesUnreachable(mResultTransitionRelation, mResultInitialState, nextStates);
						assert EprHelpers.isDeterministic(mResultTransitionRelation);
						assert !EprHelpers.hasDisconnectedTransitions(mResultTransitionRelation, 
								mResultInitialState);
					}
				} else if (doUnion && cs.isFirstSink()) {
					for (Pair<IDawgLetter<LETTER, COLNAMES>, DawgState> secondOutEdge : 
						mSecondInputDawg.getTransitionRelation().getOutEdgeSet(cs.getSecond())) {
						final PairDawgState ds = mDawgStateFactory.getOrCreatePairDawgState(secondOutEdge.getSecond(), true, false);
						nextStates.add(ds);
						mResultTransitionRelation.put(cs, secondOutEdge.getFirst(), ds);
						assert !EprHelpers.areStatesUnreachable(mResultTransitionRelation, mResultInitialState, nextStates);
						assert EprHelpers.isDeterministic(mResultTransitionRelation);
						assert !EprHelpers.hasDisconnectedTransitions(mResultTransitionRelation, 
								mResultInitialState);
					}
				}
			}
			currentStates = nextStates;
		}
		
		return new Dawg<LETTER, COLNAMES>(mDawgFactory, mFirstInputDawg.getLogger(), 
				 mFirstInputDawg.getColNames(), mResultTransitionRelation, mResultInitialState);
	}
}
