package de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.dawgs;

public class DawgState {

}

class PairDawgState extends DawgState {

	final DawgState mFirst;
	final DawgState mSecond;
	
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
