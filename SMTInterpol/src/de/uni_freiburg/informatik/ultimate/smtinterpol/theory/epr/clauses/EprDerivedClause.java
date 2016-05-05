package de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.clauses;

import java.util.ArrayList;

import de.uni_freiburg.informatik.ultimate.logic.Theory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.Literal;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.EprStateManager;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.TTSubstitution;

public class EprDerivedClause extends EprNonUnitClause {
	
	
	/**
	 * The eprClause this clause has been instantiated from.
	 */
	Object mExplanation;

	public EprDerivedClause(Literal[] literals, Theory theory, 
			EprStateManager stateManager, Object explanation) {
		this(literals, theory, stateManager, explanation, false, null, null);
	}

	public EprDerivedClause(Literal[] literals, Theory theory, 
			EprStateManager stateManager, Object explanation, 
			boolean freshAlphaRenamed, TTSubstitution freshAlphaRen, EprDerivedClause clauseThisIsAFreshAlphaRenamingof) {
		super(literals, theory, stateManager, freshAlphaRenamed, freshAlphaRen, clauseThisIsAFreshAlphaRenamingof);
//		if (freshAlphaRenamed && explanation instanceof EprClause) {
//			mExplanation = ((EprClause) explanation).instantiateClause(freshAlphaRen);
//		} else {
			mExplanation = explanation;
//		}
	}

	@Override
	public EprClause getFreshAlphaRenamedVersion() {
		TTSubstitution sub = new TTSubstitution();
		ArrayList<Literal> newLits = getFreshAlphaRenamedLiterals(sub);
		return new EprDerivedClause(newLits.toArray(new Literal[newLits.size()]), 
					mTheory, mStateManager, mExplanation, true, sub, this);
	}
}
