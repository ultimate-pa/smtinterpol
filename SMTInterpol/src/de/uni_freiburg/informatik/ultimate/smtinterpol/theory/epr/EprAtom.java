package de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.Theory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.convert.SharedTerm;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.DPLLAtom;

public class EprAtom extends DPLLAtom {
	
	ApplicationTerm at;

	public EprAtom(ApplicationTerm term, int hash, int assertionstacklevel) {
		super(hash, assertionstacklevel);
		this.at = term;
		// TODO Auto-generated constructor stub
	}

	@Override
	public Term getSMTFormula(Theory smtTheory, boolean quoted) {
		// TODO Auto-generated method stub
//		return null;
		return at;
	}

	@Override
	public String toString() {
		return at.toStringDirect();
	}
}
