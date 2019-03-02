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
	private final DawgLetterFactory<LETTER> mDawgLetterFactory;

	private SetDawgState mResultInitialState;
	private DeterministicDawgTransitionRelation<DawgState, IDawgLetter<LETTER>, DawgState> mResultTransitionRelation;
	private final SortedSet<COLNAMES> mColnames;
	private final LogProxy mLogger;
	private final HashRelation3<DawgState, IDawgLetter<LETTER>, DawgState> mInputTransitionRelation;
	private final Set<DawgState> mInputInitialStates;



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
	public DeterminizeDawg(final SortedSet<COLNAMES> colnames,
			final LogProxy logger,
			final HashRelation3<DawgState, IDawgLetter<LETTER>, DawgState> inputTransitionRelation,
			final Set<DawgState> inputInitialStates,
			final DawgFactory<LETTER, COLNAMES> dawgFactory) {
		this.mColnames = colnames;
		this.mLogger = logger;
		mInputTransitionRelation = inputTransitionRelation;
		this.mInputInitialStates = inputInitialStates;
		this.mDawgFactory = dawgFactory;
		mDawgLetterFactory = dawgFactory.getDawgLetterFactory();
		this.mDawgStateFactory = dawgFactory.getDawgStateFactory();
		determinize();
	}

	private void determinize() {
		mResultInitialState = mDawgStateFactory.getOrCreateSetDawgState(mInputInitialStates);

		mResultTransitionRelation =
				new DeterministicDawgTransitionRelation<DawgState, IDawgLetter<LETTER>, DawgState>();

		final ArrayDeque<SetDawgState> worklist = new ArrayDeque<SetDawgState>();
		worklist.add(mResultInitialState);
		while (!worklist.isEmpty()) {
			final SetDawgState currentSetState = worklist.pop();

			final BinaryRelation<IDawgLetter<LETTER>, IDawgLetter<LETTER>> occuringDawgLetterToDividedDawgLetters =
					EprHelpers.divideDawgLetters(mDawgLetterFactory, currentSetState.getInnerStates(), mInputTransitionRelation);


			final BinaryRelation<IDawgLetter<LETTER>, DawgState> dividedDawgLetterToTargetStates =
					new BinaryRelation<IDawgLetter<LETTER>, DawgState>();


			for (final IDawgLetter<LETTER> odl : occuringDawgLetterToDividedDawgLetters.getDomain()) {
				for (final DawgState state : currentSetState.getInnerStates()) {
					final Set<DawgState> targetStates = mInputTransitionRelation.projectToTrd(state, odl);
					for (final DawgState targetState : targetStates) {
						for (final IDawgLetter<LETTER> ddl : occuringDawgLetterToDividedDawgLetters.getImage(odl)) {
							dividedDawgLetterToTargetStates.addPair(ddl, targetState);
						}
					}
				}
			}

			for (final IDawgLetter<LETTER> ddl : dividedDawgLetterToTargetStates.getDomain()) {
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

		final DeterministicDawgTransitionRelation<DawgState, IDawgLetter<LETTER>, DawgState> flattenedTransitionRelation
			= EprHelpers.flattenDawgStates(mResultTransitionRelation);
		final DawgState flattenedResultInitialState = mResultInitialState.getFlatReplacement();

		return new Dawg<LETTER, COLNAMES>(mDawgFactory, mLogger,
				mColnames, flattenedTransitionRelation, flattenedResultInitialState);
	}


}
