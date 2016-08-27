package de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.partialmodel;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.EprPredicate;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.atoms.EprQuantifiedPredicateAtom;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.dawgs.IDawg;

/**
 * A DecideStackLiteral that talks about a set of points
 * 
 * @author nutz
 */
public abstract class DecideStackQuantifiedLiteral extends DecideStackLiteral {


	/**
	 * Stores all the groundings for which this.atom is decided with this.polarity
	 * by this DecideStackLiteral
	 */
	IDawg<ApplicationTerm, TermVariable> mDawg;
	
	public DecideStackQuantifiedLiteral(boolean polarity, 
			EprQuantifiedPredicateAtom atom, IDawg<ApplicationTerm, TermVariable> dawg) {
		super(polarity, atom);
		mDawg = dawg;
	}

	public DecideStackQuantifiedLiteral(boolean polarity, EprPredicate eprPredicate, IDawg dawg) {
		super(polarity, eprPredicate);
		// TODO do something about eprPredicate and dawg
	}

	public IDawg<ApplicationTerm, TermVariable> getDawg() {
		return mDawg;
	}
	
}
