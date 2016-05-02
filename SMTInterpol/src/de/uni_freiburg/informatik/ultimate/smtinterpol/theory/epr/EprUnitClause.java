package de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr;

import de.uni_freiburg.informatik.ultimate.logic.Theory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.Literal;

public abstract class EprUnitClause extends EprClause {

	public EprUnitClause(Literal[] literals, Theory theory, EprStateManager stateManager, Object explanation) {
		super(literals, theory, stateManager, explanation);
		assert (eprQuantifiedPredicateLiterals.length == 1 && groundLiterals.length == 0)
		  	|| (eprQuantifiedPredicateLiterals.length == 0 && groundLiterals.length == 1) :
		  		"not a unit clause";
	}

}
