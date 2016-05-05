package de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.clauses;

import de.uni_freiburg.informatik.ultimate.logic.Theory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.Literal;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.EprStateManager;

public class EprGroundUnitClause extends EprUnitClause {

	public EprGroundUnitClause(Literal literal, Theory theory, 
			EprStateManager stateManager, EprClause explanation) {
		this(literal, theory, stateManager, explanation, false);
	}
	
	public EprGroundUnitClause(Literal literal, Theory theory, 
			EprStateManager stateManager, EprClause explanation,
			boolean freshAlphaRenaming) {
		super(new Literal[] { literal }, theory, stateManager, explanation, freshAlphaRenaming);
		assert eprQuantifiedPredicateLiterals.length == 0;
		assert groundLiterals.length == 1;
	}

	public Literal getLiteral() {
		return groundLiterals[0];
	}

	@Override
	public boolean isConflictClause() {
		assert false : "TODO";
		return false;
	}

	@Override
	public EprUnitClause getUnitClauseLiteral() {
		assert false : "TODO";
		return null;
	}

	@Override
	public EprClause getAlphaRenamedVersion() {
		//TODO: not so nice, somehow
		return new EprGroundUnitClause(getLiteral(), mTheory, 
				mStateManager, mExplanation, true);
	}
}
