package de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.clauses;

import de.uni_freiburg.informatik.ultimate.logic.Theory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.Literal;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.EprStateManager;

public abstract class EprUnitClause extends EprClause {
	
	/**
	 * The eprClause this clause has been instantiated from.
	 * TODO: currently this field is duplicate code with EprDerivedClause..
	 */
	EprClause mExplanation;

	public EprUnitClause(Literal[] literals, Theory theory, EprStateManager stateManager, 
			EprClause explanation, boolean freshAlphaRenaming) {
		super(literals, theory, stateManager, freshAlphaRenaming);
		assert (eprQuantifiedPredicateLiterals.length == 1 && groundLiterals.length == 0)
		  	|| (eprQuantifiedPredicateLiterals.length == 0 && groundLiterals.length == 1) :
		  		"not a unit clause";
		mExplanation = explanation;
	}
	
	public EprClause getExplanation() {
		return mExplanation;
	}
}
