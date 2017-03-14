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

import java.util.ArrayDeque;
import java.util.HashSet;
import java.util.Map.Entry;
import java.util.Set;
import java.util.SortedSet;

import de.uni_freiburg.informatik.ultimate.smtinterpol.LogProxy;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.BinaryRelation;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.EprHelpers;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.dawgs.Dawg;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.dawgs.DawgFactory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.dawgs.DeterministicDawgTransitionRelation;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.dawgs.dawgletters.DawgLetterFactory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.dawgs.dawgletters.IDawgLetter;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.dawgs.dawgstates.DawgState;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.dawgs.dawgstates.DawgStateFactory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.dawgs.dawgstates.SetDawgState;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.util.HashRelation3;

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
	private DeterministicDawgTransitionRelation<DawgState, IDawgLetter<LETTER, COLNAMES>, DawgState> mResultTransitionRelation;
	private SortedSet<COLNAMES> mColnames;
	private LogProxy mLogger;
	private HashRelation3<DawgState,IDawgLetter<LETTER,COLNAMES>,DawgState> mInputTransitionRelation;
	private Set<DawgState> mInputInitialStates;



	/**
	 * The input here are the constituents of a normal Dawg except that the transition relation need not 
	 * be deterministic and there may be more than one initial state.
	 * 
	 * @param colnames
	 * @param allConstants
	 * @param logger
	 * @param inputTransitionRelation
	 * @param inputInitialStates
	 * @param dawgFactory
	 */
	public DeterminizeDawg(SortedSet<COLNAMES> colnames, 
			LogProxy logger,
			HashRelation3<DawgState, IDawgLetter<LETTER, COLNAMES>, DawgState> inputTransitionRelation,
			Set<DawgState> inputInitialStates, 
			DawgFactory<LETTER, COLNAMES> dawgFactory) {
		this.mColnames = colnames;
		this.mLogger = logger;
		this.mInputTransitionRelation = inputTransitionRelation;
		this.mInputInitialStates = inputInitialStates;
		this.mDawgFactory = dawgFactory;
		this.mDawgLetterFactory = dawgFactory.getDawgLetterFactory();
		this.mDawgStateFactory = dawgFactory.getDawgStateFactory();
		determinize();
	}
	
	private void determinize() {
		mResultInitialState = mDawgStateFactory.getOrCreateSetDawgState(mInputInitialStates);
		
		mResultTransitionRelation = new DeterministicDawgTransitionRelation<DawgState, IDawgLetter<LETTER,COLNAMES>, DawgState>();
		
		ArrayDeque<SetDawgState> worklist = new ArrayDeque<SetDawgState>();
		worklist.add(mResultInitialState);
		while (!worklist.isEmpty()) {
			final SetDawgState currentSetState = worklist.pop();
		
			BinaryRelation<IDawgLetter<LETTER, COLNAMES>, IDawgLetter<LETTER, COLNAMES>> occuringDawgLetterToDividedDawgLetters =
					EprHelpers.divideDawgLetters(mDawgLetterFactory, currentSetState.getInnerStates(), mInputTransitionRelation);
			
			
			BinaryRelation<IDawgLetter<LETTER, COLNAMES>, DawgState> dividedDawgLetterToTargetStates =
					new BinaryRelation<IDawgLetter<LETTER,COLNAMES>, DawgState>();
			
			
			for (IDawgLetter<LETTER, COLNAMES> odl : occuringDawgLetterToDividedDawgLetters.getDomain()) {
				for (DawgState state : currentSetState.getInnerStates()) {
					final Set<DawgState> targetStates = mInputTransitionRelation.projectToTrd(state, odl);
					for (DawgState targetState : targetStates) {
						for (IDawgLetter<LETTER, COLNAMES> ddl : occuringDawgLetterToDividedDawgLetters.getImage(odl)) {
							dividedDawgLetterToTargetStates.addPair(ddl, targetState);
						}
					}
				}
			}
			
			for (IDawgLetter<LETTER, COLNAMES> ddl : dividedDawgLetterToTargetStates.getDomain()) {
				 final SetDawgState targetSetState = mDawgStateFactory.getOrCreateSetDawgState(
						 dividedDawgLetterToTargetStates.getImage(ddl));
				 mResultTransitionRelation.put(currentSetState, ddl, targetSetState);
				 worklist.addFirst(targetSetState);
			}
		}
	}


	public Dawg<LETTER, COLNAMES> build() {
		assert mResultTransitionRelation != null;
		assert mResultInitialState != null;
		return new Dawg<LETTER, COLNAMES>(mDawgFactory, mLogger, 
				mColnames, mResultTransitionRelation, mResultInitialState);
	}


}
