package de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.partialmodel;

/**
 * An entry on the epr decide stack that marks a smtlib push() operation.
 * 
 * @author Alexander Nutz
 */
public class DecideStackPushMarker extends DecideStackEntry {
	
	public DecideStackPushMarker(int index) {
		super(index);
	}

	@Override
	public String toString() {
		return "pushMarker" + nr;
	}
}
