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
}
