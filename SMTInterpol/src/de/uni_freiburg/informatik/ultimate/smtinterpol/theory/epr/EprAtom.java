package de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.Theory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.convert.SharedTerm;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.DPLLAtom;

/**
 * Represents an Atom that is known to the EprTheory.
 * Note that, although this class inherits from DPLLAtom, only some EprAtoms are known to 
 * the DPLLEngine, namely those that are of the form "(P c_1 ... c_n)" where P is an 
 * uninterpreted predicate and the c_i are constants. In contrast, every EprAtom that contains
 * a TermVariable is only known to the EprTheory.
 * 
 * @author Alexander Nutz
 *
 */
public abstract class EprAtom extends DPLLAtom {
	
	protected final Term mTerm;
	public boolean isQuantified;

	public EprAtom(Term term, int hash, int assertionstacklevel) {
		super(hash, assertionstacklevel);
		this.mTerm = term;
	}

	@Override
	public Term getSMTFormula(Theory smtTheory, boolean quoted) {
		// TODO Auto-generated method stub
//		return null;
		return mTerm;
	}

	@Override
	public String toString() {
		return mTerm.toStringDirect();
	}
	
	
}
