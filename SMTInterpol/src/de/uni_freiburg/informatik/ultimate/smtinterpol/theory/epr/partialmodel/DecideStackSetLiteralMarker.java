package de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.partialmodel;

import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.Literal;

public class DecideStackSetLiteralMarker extends DecideStackEntry {

	final Literal mLiteral;
	
	public DecideStackSetLiteralMarker(Literal l, int index) {
		super(index);
		mLiteral = l;
	}
	
	@Override
	public String toString() {
		return "(literalMarker: " + mLiteral + " " + nr + ")";
	}
}
