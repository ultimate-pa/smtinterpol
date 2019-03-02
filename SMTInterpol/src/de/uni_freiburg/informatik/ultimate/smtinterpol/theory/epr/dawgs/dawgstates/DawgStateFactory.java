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

import java.util.HashMap;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.dawgs.dawgletters.IDawgLetter;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.util.NestedMap3;

/**
 *
 * Manages DawgStates
 *  <li> creates fresh states
 *  <li> creates and manages PairDawgStates (keeps them unique)
 *
 * @author Alexander Nutz (nutz@informatik.uni-freiburg.de)
 *
 */
public class DawgStateFactory<LETTER, COLNAMES> {

	Map<DawgState, Map<DawgState, PairDawgState>> mDSToDSToPDS =
			new HashMap<DawgState, Map<DawgState,PairDawgState>>();

	/**
	 * the first state is the sink state
	 */
	Map<DawgState, PairDawgState> mFirstHalfSinkStates = new HashMap<DawgState, PairDawgState>();

	/**
	 * the second state is teh sink state
	 */
	private final Map<DawgState, PairDawgState> mSecondHalfSinkStates = new HashMap<DawgState, PairDawgState>();

	private Map<Set<DawgState>, SetDawgState> mDawgStateSetToSetDawgState = new HashMap<Set<DawgState>, SetDawgState>();

	private final NestedMap3<IDawgLetter<LETTER, COLNAMES>, COLNAMES, DawgState, RenameAndReorderDawgState<LETTER, COLNAMES>>
		mLetterToColNameToDawgStateToRenameAndReorderDawgState =
		new NestedMap3<IDawgLetter<LETTER, COLNAMES>, COLNAMES, DawgState, RenameAndReorderDawgState<LETTER,COLNAMES>>();

	public PairDawgState getOrCreatePairDawgState(DawgState first, DawgState second) {

		Map<DawgState, PairDawgState> dsToPds = mDSToDSToPDS.get(first);

		if (dsToPds == null) {
			dsToPds = new HashMap<DawgState, PairDawgState>();
			mDSToDSToPDS.put(first, dsToPds);
		}

		PairDawgState pds = dsToPds.get(second);

		if (pds == null) {
			pds = new PairDawgState(first, second, createDawgState());
			dsToPds.put(second, pds);
		}

		return pds;
	}

	public PairDawgState getOrCreatePairDawgState(DawgState value, boolean firstIsSink, boolean secondIsSink) {
		assert firstIsSink != secondIsSink;

		if (firstIsSink) {
			PairDawgState ds = mFirstHalfSinkStates.get(value);
			if (ds == null) {
				ds = new PairDawgState(value, true, false, createDawgState());
				mFirstHalfSinkStates.put(value, ds);
			}
			return ds;
		} else {
			PairDawgState ds = mSecondHalfSinkStates.get(value);
			if (ds == null) {
				ds = new PairDawgState(value, false, true, createDawgState());
				mSecondHalfSinkStates.put(value, ds);
			}
			return ds;
		}
	}

	public SetDawgState getOrCreateSetDawgState(Set<DawgState> dawgStates) {
		SetDawgState result = mDawgStateSetToSetDawgState.get(dawgStates);
		if (result == null) {
			result = new SetDawgState(dawgStates, createDawgState());
			mDawgStateSetToSetDawgState.put(dawgStates, result);
		}
		return result;
	}

	public DawgState createDawgState() {
		return new DawgState();
	}

	public RenameAndReorderDawgState<LETTER, COLNAMES> getReorderAndRenameDawgState(IDawgLetter<LETTER, COLNAMES> key,
			COLNAMES newRightNeighbour,	DawgState value) {
		RenameAndReorderDawgState<LETTER, COLNAMES> result =
				mLetterToColNameToDawgStateToRenameAndReorderDawgState.get(key, newRightNeighbour, value);
		if (result == null) {
			result = new RenameAndReorderDawgState<LETTER, COLNAMES>(key, newRightNeighbour, value, createDawgState());
			mLetterToColNameToDawgStateToRenameAndReorderDawgState.put(key, newRightNeighbour, value, result);
		}
		return result;
	}

}
