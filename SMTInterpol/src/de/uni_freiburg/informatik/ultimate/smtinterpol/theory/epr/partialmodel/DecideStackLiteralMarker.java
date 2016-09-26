package de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.partialmodel;

import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.Literal;

public class DecideStackLiteralMarker extends DecideStackEntry {

	final Literal mLiteral;
	final int mIndex;
	
	public DecideStackLiteralMarker(Literal l, int index) {
		mLiteral = l;
		mIndex = index;
	}
	
	@Override
	public String toString() {
		return "(literalMarker: " + mLiteral + " " + mIndex + ")";
	}
}
