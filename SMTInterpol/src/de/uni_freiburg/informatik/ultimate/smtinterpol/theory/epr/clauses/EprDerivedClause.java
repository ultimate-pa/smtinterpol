package de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.clauses;

import de.uni_freiburg.informatik.ultimate.logic.Theory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.Literal;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.EprStateManager;

public class EprDerivedClause extends EprNonUnitClause {
	
	
	/**
	 * The eprClause this clause has been instantiated from.
	 */
	Object mExplanation;

	public EprDerivedClause(Literal[] literals, Theory theory, EprStateManager stateManager, Object explanation) {
		super(literals, theory, stateManager);
		mExplanation = explanation;
	}

}
