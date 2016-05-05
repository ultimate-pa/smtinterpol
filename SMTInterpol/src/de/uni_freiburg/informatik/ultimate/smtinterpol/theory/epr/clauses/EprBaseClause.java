package de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.clauses;

import de.uni_freiburg.informatik.ultimate.logic.Theory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.Literal;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.EprStateManager;

public class EprBaseClause extends EprNonUnitClause {

	public EprBaseClause(Literal[] literals, Theory theory, EprStateManager stateManager) {
		this(literals, theory, stateManager, false);
	}
	
	public EprBaseClause(Literal[] literals, Theory theory, 
			EprStateManager stateManager, boolean freshAlpharenamed) {
		super(literals, theory, stateManager, freshAlpharenamed);
	}


}
