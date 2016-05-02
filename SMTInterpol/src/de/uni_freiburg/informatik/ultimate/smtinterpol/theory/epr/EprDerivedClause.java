package de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr;

import de.uni_freiburg.informatik.ultimate.logic.Theory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.Literal;

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
