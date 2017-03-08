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

import java.util.Iterator;
import java.util.List;
import java.util.Map.Entry;

/**
 * 
 * 
 * 
 * @author Alexander Nutz (nutz@informatik.uni-freiburg.de)
 *
 * @param <LETTER>
 * @param <COLNAMES>
 */
@Deprecated
public class AddWordDawgBuilder<LETTER, COLNAMES> {

	private final DawgFactory<LETTER, COLNAMES> mDawgFactory;
	private final Dawg<LETTER, COLNAMES> mInputDawg;
	private final List<LETTER> mWordToAdd;
	private IDawg<LETTER, COLNAMES> mResultDawg;

	public AddWordDawgBuilder(DawgFactory<LETTER, COLNAMES> dawgFactory, Dawg<LETTER, COLNAMES> dawg,
			List<LETTER> word) {
		/*
		 * as is this algorithm only works for a very restricted set of graphs.
		 */
		assert false : "TODO: rework this!";
			
		mDawgFactory = dawgFactory;
		mInputDawg = dawg;
		mWordToAdd = word;
		addWord();
	}

	private void addWord() {
		if (mInputDawg.isEmpty()) {
			mResultDawg = mDawgFactory.createOnePointDawg(mInputDawg.getColNames(), mWordToAdd);
		} else {
			final DeterministicDawgTransitionRelation<DawgState, IDawgLetter<LETTER, COLNAMES>, DawgState> newTransitionRelation = 
					mInputDawg.getTransitionRelation().copy();
			DawgState currentState = mInputDawg.getInitialState();
			Iterator<Object> columnSortIt = mInputDawg.getColumnSorts().iterator();
			for (LETTER letter : mWordToAdd) {
				Object currentColumnSort = columnSortIt.next();
//				for (Entry<IDawgLetter<LETTER, COLNAMES>, DawgState> outEdge : 
//					mInputDawg.getTransitionRelation().get(currentState).entrySet()) {
				boolean foundAMatchingEdge = false;
				for (Pair<IDawgLetter<LETTER, COLNAMES>, DawgState> outEdge : 
					newTransitionRelation.getOutEdgeSet(currentState)) {
					if (outEdge.getFirst().matches(letter, mWordToAdd, mInputDawg.getColNameToIndex())) {
						// we already have a transition for the current letter
						// (assumption: the Dawg is deterministic in the sense that outgoing DawgLetters of one 
						//  state don't intersect)
						currentState = outEdge.getSecond();
						foundAMatchingEdge = true;
						break;
					}
				}
				
				if (!foundAMatchingEdge) {
					// we need a fresh transition (effectively building one fresh "tail" for the dawg for
					// the given word suffix..
					

					/*
					 * we may need to edit another edge here to keep the automaton deterministic, right?..
					 *  --> say we have automaton s1 -{a, b}-> s2 -{a, b}_(=1)-> s3 (accepting aa, bb)
					 *      and we add word ab
					 *      then we should get s1 -{a, b}-> s2 -
					 *     
					 * 
					 */
					assert false : "TODO";



					final DawgState newState = mDawgFactory.getDawgStateFactory().createDawgState();
					final IDawgLetter<LETTER, COLNAMES> newLetter = mDawgFactory.getDawgLetterFactory()
							.getSingletonSetDawgLetter(letter, currentColumnSort);
					newTransitionRelation.put(currentState, newLetter, newState);
					currentState = newState;
				}
			}
			assert !columnSortIt.hasNext();

			mResultDawg = new Dawg<LETTER, COLNAMES>(mDawgFactory, mInputDawg.getLogger(),
					mInputDawg.getColNames(), newTransitionRelation, mInputDawg.getInitialState());

		}
	}

	public IDawg<LETTER, COLNAMES> build() {
		assert mResultDawg != null;
		return mResultDawg;
	}

}
