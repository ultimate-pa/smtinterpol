package de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.dawgs;

import java.util.Set;

class SetDawgState extends DawgState {
	
	private final Set<DawgState> mDawgStates;
	
	SetDawgState(Set<DawgState> dawgStates) {
		mDawgStates = dawgStates;
	}
	
	Set<DawgState> getInnerStates() {
		return mDawgStates;
	}

	@Override
	public String toString() {
		final StringBuilder innerDawgStateHashCodes = new StringBuilder();
		String comma = "";
		for (DawgState ds : mDawgStates) {
			innerDawgStateHashCodes.append(comma);
			comma = ", ";
			innerDawgStateHashCodes.append(ds.hashCode() % 10000);
		}
		
		return String.format("SetDawgState%d:%s", this.hashCode() % 10000, innerDawgStateHashCodes);
	}
}