package de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.partialmodel;

import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.TermTuple;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.atoms.EprGroundPredicateAtom;

/**
 * A DecideStackLiteral that talks about just one point.
 * 
 * @author nutz
 */
public class DecideStackGroundLiteral extends DecideStackLiteral {
	
	TermTuple mPoint;

	public DecideStackGroundLiteral(boolean polarity, EprGroundPredicateAtom atom) {
		super(polarity, atom);
		mPoint = atom.getArgumentsAsTermTuple();
	}

}
