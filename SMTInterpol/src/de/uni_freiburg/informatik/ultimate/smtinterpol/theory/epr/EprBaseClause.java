package de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr;

import de.uni_freiburg.informatik.ultimate.logic.Theory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.Literal;

public class EprBaseClause extends EprNonUnitClause {

	public EprBaseClause(Literal[] literals, Theory theory, EprStateManager stateManager) {
		super(literals, theory, stateManager);
	}

}
