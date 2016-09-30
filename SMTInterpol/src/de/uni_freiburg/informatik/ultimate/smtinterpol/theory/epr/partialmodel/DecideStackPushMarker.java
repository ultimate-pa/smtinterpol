package de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.partialmodel;

public class DecideStackPushMarker extends DecideStackEntry {
	
	public DecideStackPushMarker(int index) {
		super(index);
	}

	@Override
	public String toString() {
		return "pushMarker" + nr;
	}
}
