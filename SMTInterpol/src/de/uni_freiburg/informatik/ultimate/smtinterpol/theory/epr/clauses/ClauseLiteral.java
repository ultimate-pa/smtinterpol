package de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.clauses;

import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.DPLLAtom;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.Literal;

/**
 * Represents a literal that occurs in an EprClause.
 * This may be a ground literal or a quantified literal.
 * 
 * In contrast to the Literal class DPLLEngine uses, a 
 * ClauseLiteral has a decide state that also depends on the
 * EprStateManagers decide stack.
 * 
 * @author nutz
 */
public abstract class ClauseLiteral {


	final Literal mEngineLiteral;
	final boolean mPolarity;
	
	/**
	 * The clause that this ClauseLiteral is part of
	 */
	EprClause mEprClause;
	
	public ClauseLiteral(boolean polarity, DPLLAtom atom, EprClause clause) {
		mEngineLiteral = polarity ? atom : atom.negate();
		mPolarity = polarity;
		mEprClause = clause;
	}
	
	
	public boolean getPolarity() {
		return mPolarity;
	}
	
	public Literal getLiteral() {
		return mEngineLiteral;
	}
	
//	public DPLLAtom getAtom() {
//		return mAtom;
//	}
}
