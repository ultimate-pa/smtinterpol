package de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.partialmodel;

import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.EprPredicate;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.atoms.EprQuantifiedPredicateAtom;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.dawgs.IDawg;

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

	public DecideStackQuantifiedLiteral(boolean polarity, EprPredicate eprPredicate, IDawg dawg) {
		super(polarity, eprPredicate);
		// TODO do something about eprPredicate and dawg
	}

	public IDawg getDawg() {
		return mDawg;
	}
	
}
