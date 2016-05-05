package de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.atoms;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.logic.Theory;

public class EprQuantifiedEqualityAtom extends EprAtom {
	
	private final Term lhs;
	private final Term rhs;
	private final boolean bothQuantified;

	public EprQuantifiedEqualityAtom(ApplicationTerm term, int hash, int assertionstacklevel) {
		super(term, hash, assertionstacklevel);
		assert term.getFunction().getName().equals("=");
		assert term.getFreeVars().length > 0;

//		this.isQuantified = true;
		
		this.lhs = term.getParameters()[0];
		this.rhs = term.getParameters()[1];
		
		this.bothQuantified = term.getParameters()[0] instanceof TermVariable 
				&& term.getParameters()[1] instanceof TermVariable ;
	}

	public Term getLhs() {
		return lhs;
	}

	public Term getRhs() {
		return rhs;
	}
	
	/**
	 * 
	 * @return true iff both sides of the equality are quantified variables
	 */
	public boolean areBothQuantified() {
		return bothQuantified;
	}

	@Override
	public Term getSMTFormula(Theory smtTheory, boolean quoted) {
		// TODO Auto-generated method stub
//		return null;
		return mTerm;
	}
	
	@Override
	public String toString() {
		return mTerm.toString();
	}
}
