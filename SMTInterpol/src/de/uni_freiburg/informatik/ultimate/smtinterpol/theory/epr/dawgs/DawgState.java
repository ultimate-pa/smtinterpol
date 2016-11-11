package de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.dawgs;

public class DawgState {
	
	public DawgState() {
		
	}

}

class PairDawgState extends DawgState {

	final DawgState mFirst;
	final DawgState mSecond;
	
	boolean mFirstIsSink;
	boolean mSecondIsSink;
	
	PairDawgState(DawgState s, boolean firstIsSink, boolean secondIsSink) {
		assert firstIsSink != secondIsSink;
		
		if (firstIsSink) {
			mFirst = null;
			mSecond = s;
		} else {
			mFirst = s;
			mSecond = null;
		}
	}

	PairDawgState(DawgState f, DawgState s) {
		mFirst = f;
		mSecond = s;
	}
	
	DawgState getFirst() {
		return mFirst;
	}
	
	DawgState getSecond() {
		return mSecond;
	}
}
