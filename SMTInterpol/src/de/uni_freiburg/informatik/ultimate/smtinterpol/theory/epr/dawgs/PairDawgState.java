package de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.dawgs;

public class PairDawgState extends DawgState {

	final DawgState mFirst;
	final DawgState mSecond;
	
	final boolean mFirstIsSink;
	final boolean mSecondIsSink;
	
	PairDawgState(DawgState s, boolean firstIsSink, boolean secondIsSink) {
		assert firstIsSink != secondIsSink;
		
		if (firstIsSink) {
			mFirst = null;
			mSecond = s;
			mFirstIsSink = true;
			mSecondIsSink = false;
		} else {
			mFirst = s;
			mSecond = null;
			mFirstIsSink = false;
			mSecondIsSink = true;
		}
	}

	PairDawgState(DawgState f, DawgState s) {
		assert f != null && s != null;
		mFirstIsSink = false;
		mSecondIsSink = false;
		mFirst = f;
		mSecond = s;
	}
	
	DawgState getFirst() {
		return mFirst;
	}
	
	DawgState getSecond() {
		return mSecond;
	}
	
	@Override
	public String toString() {
		return String.format("PairDawgState%d(#%d,#%d)", 
				this.hashCode() % 10000,
				mFirstIsSink ? -1 : mFirst.hashCode() % 10000,
				mSecondIsSink ? -1 : mSecond.hashCode() % 10000);
	}
}