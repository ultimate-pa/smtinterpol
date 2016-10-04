package de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.atoms;

import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.Theory;

/**
 * Atom representing a ground equality.
 * Maybe this is just a dummy until it gets replaced by CCEquality in all places,
 * maybe we want not-shared ground equalities in the Epr theory --> not sure yet..
 * 
 * Note that this does not extend EprEqualityAtom because that is assumed to represent
 * a quantified equality.
 * 
 * @author Alexander Nutz
 *
 */
public class EprGroundEqualityAtom extends EprAtom {

	public EprGroundEqualityAtom(Term term, int hash, int assertionstacklevel) {
		super(term, hash, assertionstacklevel);
	}

	@Override
	public Term getSMTFormula(Theory smtTheory, boolean quoted) {
		return mTerm;
	}
}
