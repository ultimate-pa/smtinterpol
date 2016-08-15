package de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.clauses.old;

import java.util.ArrayList;

import de.uni_freiburg.informatik.ultimate.logic.Theory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.Literal;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.EprTheory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.TTSubstitution;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.partialmodel.EprStateManager;

public class EprDerivedClause extends EprNonUnitClause {
	
	
	/**
	 * The eprClause this clause has been instantiated from.
	 */
	Object mExplanation;

	public EprDerivedClause(Literal[] literals, EprTheory eprTheory, 
			Object explanation) {
		this(literals, eprTheory, explanation, false, null, null);
	}

	public EprDerivedClause(Literal[] literals, EprTheory eprTheory, 
			Object explanation, 
			boolean freshAlphaRenamed, TTSubstitution freshAlphaRen, EprDerivedClause clauseThisIsAFreshAlphaRenamingof) {
		super(literals, eprTheory, freshAlphaRenamed, freshAlphaRen, clauseThisIsAFreshAlphaRenamingof);
//		if (freshAlphaRenamed && explanation instanceof EprClause) {
//			mExplanation = ((EprClause) explanation).instantiateClause(freshAlphaRen);
//		} else {
			mExplanation = explanation;
//		}
	}

	@Override
	public EprClauseOld getFreshAlphaRenamedVersion() {
		TTSubstitution sub = new TTSubstitution();
		ArrayList<Literal> newLits = getFreshAlphaRenamedLiterals(sub);
		return new EprDerivedClause(newLits.toArray(new Literal[newLits.size()]), 
					mEprTheory, mExplanation, true, sub, this);
	}
}
