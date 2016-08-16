package de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.clauses;

import java.util.Set;

import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.Literal;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.EprTheory;

/**
 * Represents a clause that is only known to the EprTheory.
 * This means that the clause contains at least one free 
 * (implicitly quantified) variable.
 * 
 * @author nutz
 */
public class EprClause {

	public EprClause(Set<Literal> newLits, EprTheory mEprTheory) {
		// TODO Auto-generated constructor stub
	}

	Set<ClauseLiteral> literals;

	/**
	 * This clause is informed that the DPLLEngine has set literal.
	 * The fulfillmentState of this clause may have to be updated because of this.
	 * 
	 * @param literal ground Epr Literal that has been set by DPLLEngine
	 */
	public void updateStateWrtDpllLiteral(Literal literal) {
		assert false : "TODO: implement";
	}

	public void backtrackStateWrtDpllLiteral(Literal literal) {
		assert false : "TODO: implement";
	}
}
