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
package de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.dawgs.dawgstates;

import java.util.Map;

import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.dawgs.dawgletters.DawgLetter;
import de.uni_freiburg.informatik.ultimate.util.datastructures.UnifyHash;

/**
 *
 * Manages DawgStates
 * <li>creates fresh states
 * <li>creates and manages PairDawgStates (keeps them unique)
 *
 * @author Alexander Nutz, Jochen Hoenicke
 */
public class DawgStateFactory<LETTER> {
	final UnifyHash<DawgState<LETTER, ?>> mExistingStates = new UnifyHash<>();

	@SuppressWarnings("unchecked")
	public <VALUE> DawgState<LETTER, VALUE> createFinalState(final VALUE value) {
		final int hash = value.hashCode();
		for (final DawgState<LETTER, ?> previous : mExistingStates.iterateHashCode(hash)) {
			if (previous.isFinal() && previous.getFinalValue().equals(value)) {
				return (DawgState<LETTER, VALUE>) previous;
			}
		}
		final DawgState<LETTER, VALUE> result = new DawgState<>(value);
		mExistingStates.put(hash, result);
		// assert result.checkState();
		return result;
	}

	@SuppressWarnings("unchecked")
	public <VALUE> DawgState<LETTER, VALUE>
			createIntermediateState(final Map<DawgState<LETTER, VALUE>, DawgLetter<LETTER>> transitions) {
		final int hash = transitions.hashCode();
		for (final DawgState<LETTER, ?> previous : mExistingStates.iterateHashCode(hash)) {
			if (previous.mTransitions.equals(transitions)) {
				return (DawgState<LETTER, VALUE>) previous;
			}
		}
		final DawgState<LETTER, VALUE> result = new DawgState<>(transitions);
		mExistingStates.put(hash, result);
		// assert result.checkState();
		return result;
	}
}
