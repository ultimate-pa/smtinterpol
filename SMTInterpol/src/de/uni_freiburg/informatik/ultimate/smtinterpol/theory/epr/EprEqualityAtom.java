package de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;

public class EprEqualityAtom extends EprAtom {

	public EprEqualityAtom(ApplicationTerm term, int hash, int assertionstacklevel) {
		super(term, hash, assertionstacklevel);
		assert term.getFunction().getName().equals("=");

		this.isQuantified = true;
	}

}
