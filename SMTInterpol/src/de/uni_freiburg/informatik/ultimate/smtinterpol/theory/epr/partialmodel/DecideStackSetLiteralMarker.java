package de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.partialmodel;

import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.Literal;

/**
 * Represents an entry in the epr decide stack which marks the setting of a literal through the dpll engine
 * at that point.
 *  
 * @author Alexander Nutz
 */
public class DecideStackSetLiteralMarker extends DecideStackEntry {

	private final Literal mLiteral;
	
	public DecideStackSetLiteralMarker(Literal l, int index) {
		super(index);
		mLiteral = l;
	}
	
	@Override
	public String toString() {
		return "(literalMarker: " + mLiteral + " " + nr + ")";
	}
}
