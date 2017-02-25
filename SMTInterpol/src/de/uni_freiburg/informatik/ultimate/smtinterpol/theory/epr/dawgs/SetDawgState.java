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
		return String.format("SetDawgState%d:%s", this.hashCode() % 10000, mDawgStates);
	}
}