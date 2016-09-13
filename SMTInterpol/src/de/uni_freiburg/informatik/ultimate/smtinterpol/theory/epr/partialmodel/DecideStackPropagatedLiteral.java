package de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.partialmodel;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.Clause;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.Literal;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.EprPredicate;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.atoms.EprQuantifiedPredicateAtom;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.clauses.ClauseEprLiteral;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.clauses.ClauseLiteral;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.clauses.EprClause;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.dawgs.IDawg;

/**
 * Represents a literal on the epr decide stack that was set because of a unit propagation.
 * 
 * @author nutz
 *
 */
public class DecideStackPropagatedLiteral extends DecideStackLiteral {
	
	/**
	 * the clause literal whose clause, together with the prefix of the decide stack is responsible
	 * for the setting of this literal
	 * It is always an Epr literal because it contradicts something on the epr decide stack
	 */
	ClauseEprLiteral mUnitClauseLiteral;

	public DecideStackPropagatedLiteral(boolean polarity, EprPredicate eprPred,
			IDawg<ApplicationTerm, TermVariable> dawg, ClauseEprLiteral unitClauseLiteral) {
		super(polarity, eprPred, dawg);
		mUnitClauseLiteral = unitClauseLiteral;
	}

	/**
	 * Returns the unit clause that was the reason for setting this propagated decide stack literal.
	 * @return unit clause
	 */
	public ClauseEprLiteral getReasonClauseLit() {
		return mUnitClauseLiteral;
	}

//	/**
//	 * Returns a grounding of the Epr unit clause that is the reason for this propagated decide stack literal.
//	 * The grounding is a reason for the earlier propagation of the argument ground literal (that the DPLLEngine
//	 * understands..).
//	 * @param literal
//	 * @return
//	 */
//	public Clause getGroundedReasonUnitClause(Literal literal) {
//		EprClause unitClause = getReasonClauseLit().getClause();
//		return unitClause.getUnitGrounding(literal);
//	}

	@Override
	public String toString() {
		return "(DSPL: " + (mPolarity ? "" : "~").toString() + mPred.toString() +  ")";
	}	
}
