package de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.clauses;

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


	Literal rawLiteral;
	
	/**
	 * The clause that this ClauseLiteral is part of
	 */
	EprClause clause;
}
