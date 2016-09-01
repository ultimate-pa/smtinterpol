package de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.clauses;

import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.DPLLAtom;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.Literal;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.EprTheory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.partialmodel.DecideStackLiteral;

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
	final DPLLAtom mAtom;
	final boolean mPolarity;
	final EprTheory mEprTheory;
	
	/**
	 * The clause that this ClauseLiteral is part of
	 */
	EprClause mEprClause;
	
	public ClauseLiteral(boolean polarity, DPLLAtom atom, EprClause clause, EprTheory eprTheory) {
		mAtom = atom;
		mEngineLiteral = polarity ? atom : atom.negate();
		mPolarity = polarity;
		mEprClause = clause;
		mEprTheory = eprTheory;
	}
	
	
	public boolean getPolarity() {
		return mPolarity;
	}
	
	public Literal getLiteral() {
		return mEngineLiteral;
	}


//	public abstract boolean isFulfillable();
//
//	public abstract boolean isFulfilled();
	
	public boolean isFulfillable() {
		return determineState() == ClauseLiteralState.Fulfillable;
	}

	public boolean isFulfilled() {
		return determineState() == ClauseLiteralState.Fulfilled;
	}
	
	protected abstract ClauseLiteralState determineState();

//	public DPLLAtom getAtom() {
//		return mAtom;
//	}
	
	/**
	 * For ground clause literals this has the usual meanings wrt. the current decide state:
	 *  - fulfilled: set to true
	 *  - fulfillable: undecided
	 *  - refuted: set to false
	 *  
	 *  For quantified clause literals fulfilled/refuted means that it is true/false on all points.
	 *  Fulfillable means everything in between..
	 */
	enum ClauseLiteralState {
		Fulfilled, Fulfillable, Refuted;
	}

	public EprClause getClause() {
		return mEprClause;
	}


	public boolean conflictsWith(DecideStackLiteral reason) {
		// TODO Auto-generated method stub
		return false;
	}
	
}
