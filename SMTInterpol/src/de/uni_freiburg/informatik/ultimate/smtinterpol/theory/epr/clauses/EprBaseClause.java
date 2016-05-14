package de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.clauses;

import java.util.ArrayList;

import de.uni_freiburg.informatik.ultimate.logic.Theory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.Literal;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.EprStateManager;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.EprTheory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.TTSubstitution;

public class EprBaseClause extends EprNonUnitClause {

	public EprBaseClause(Literal[] literals, EprTheory eprTheory) {
		this(literals, eprTheory, false, null, null);
	}
	
	public EprBaseClause(Literal[] literals, EprTheory eprTheory, 
			boolean freshAlpharenamed, TTSubstitution freshAlphaRen, EprBaseClause clauseThisIsAFreshAlphaRenamingof) {
		super(literals, eprTheory, freshAlpharenamed, freshAlphaRen, clauseThisIsAFreshAlphaRenamingof);
	}

	@Override
	public EprClause getFreshAlphaRenamedVersion() {
		TTSubstitution sub = new TTSubstitution();
		ArrayList<Literal> newLits = getFreshAlphaRenamedLiterals(sub);
		return new EprBaseClause(newLits.toArray(new Literal[newLits.size()]), 
					mEprTheory, true, sub, this);
	}
}
