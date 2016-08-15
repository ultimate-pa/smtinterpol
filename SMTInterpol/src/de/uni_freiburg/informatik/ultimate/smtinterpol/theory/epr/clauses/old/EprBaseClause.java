package de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.clauses.old;

import java.util.ArrayList;

import de.uni_freiburg.informatik.ultimate.logic.Theory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.Literal;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.EprTheory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.TTSubstitution;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.partialmodel.EprStateManager;

public class EprBaseClause extends EprNonUnitClause {

	public EprBaseClause(Literal[] literals, EprTheory eprTheory) {
		this(literals, eprTheory, false, null, null);
	}
	
	public EprBaseClause(Literal[] literals, EprTheory eprTheory, 
			boolean freshAlpharenamed, TTSubstitution freshAlphaRen, EprBaseClause clauseThisIsAFreshAlphaRenamingof) {
		super(literals, eprTheory, freshAlpharenamed, freshAlphaRen, clauseThisIsAFreshAlphaRenamingof);
	}

	@Override
	public EprClauseOld getFreshAlphaRenamedVersion() {
		TTSubstitution sub = new TTSubstitution();
		ArrayList<Literal> newLits = getFreshAlphaRenamedLiterals(sub);
		return new EprBaseClause(newLits.toArray(new Literal[newLits.size()]), 
					mEprTheory, true, sub, this);
	}
}
