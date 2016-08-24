package de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.partialmodel;

import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.TermTuple;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.atoms.EprGroundPredicateAtom;

/**
 * A DecideStackLiteral that talks about just one point.
 * 
 * TODO: it is not clear at the moment if this is needed 
 *    -- an alternative would be to have all ground literals managed by the DPLLEngine, also the EprGroundPredicateAtoms..
 *     for now: don't use this class but only its quantified sibling
 * 
 * @author nutz
 */
@Deprecated
public class DecideStackGroundLiteral extends DecideStackLiteral {
	
	TermTuple mPoint;

	public DecideStackGroundLiteral(boolean polarity, EprGroundPredicateAtom atom) {
		super(polarity, atom);
		mPoint = atom.getArgumentsAsTermTuple();
	}

}
