package de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.partialmodel;

import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.atoms.EprQuantifiedPredicateAtom;

/**
 * A DecideStackLiteral that talks about a set of points
 * 
 * @author nutz
 */
public class DecideStackQuantifiedLiteral extends DecideStackLiteral {


	/**
	 * Stores all the groundings for which this.atom is decided with this.polarity
	 * by this DecideStackLiteral
	 */
	IDawg mDawg;
	
	public DecideStackQuantifiedLiteral(boolean polarity, EprQuantifiedPredicateAtom atom, IDawg dawg) {
		super(polarity, atom);
		mDawg = dawg;
	}
	
	
}
