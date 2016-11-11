package de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.dawgs;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

public class DawgStateFactory {
	
	Map<DawgState, Map<DawgState, PairDawgState>> mDSToDSToPDS = 
			new HashMap<DawgState, Map<DawgState,PairDawgState>>();
	
	/**
	 * the first state is the sink state
	 */
	Map<DawgState, PairDawgState> mFirstHalfSinkStates = new HashMap<DawgState, PairDawgState>();

	/**
	 * the second state is teh sink state
	 */
	Map<DawgState, PairDawgState> mSecondHalfSinkStates = new HashMap<DawgState, PairDawgState>();

	PairDawgState createPairDawgState(DawgState first, DawgState second) {
		
		Map<DawgState, PairDawgState> dsToPds = mDSToDSToPDS.get(first);
	
		if (dsToPds == null) {
			dsToPds = new HashMap<DawgState, PairDawgState>();
			mDSToDSToPDS.put(first, dsToPds);
		}
		
		PairDawgState pds = dsToPds.get(second);
		
		if (pds == null) {
			pds = new PairDawgState(first, second);
			dsToPds.put(second, pds);
		}
		
		return pds;
	}

	PairDawgState createPairDawgState(DawgState value, boolean firstIsSink, boolean secondIsSink) {
		assert firstIsSink != secondIsSink;
		
		if (firstIsSink) {
			PairDawgState ds = mFirstHalfSinkStates.get(value);
			if (ds == null) {
				ds = new PairDawgState(value, true, false);
				mFirstHalfSinkStates.put(value, ds);
			}
			return ds;
		} else {
			PairDawgState ds = mSecondHalfSinkStates.get(value);
			if (ds == null) {
				ds = new PairDawgState(value, false, true);
				mSecondHalfSinkStates.put(value, ds);
			}
			return ds;
		}
	}

	public DawgState createDawgState() {
		return new DawgState();
	}

}
