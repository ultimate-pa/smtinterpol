package de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.partialmodel;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.EprPredicate;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.clauses.ClauseEprLiteral;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.dawgs.IDawg;

/**
 * Represents a literal on the epr decide stack that was set because of a unit propagation.
 * 
 * @author Alexander Nutz
 *
 */
public class DecideStackPropagatedLiteral extends DecideStackLiteral {
	
	/**
	 * The clause literal whose clause, together with the prefix of the decide stack is responsible
	 * for the setting of this literal
	 * It is always an Epr literal because it contradicts something on the epr decide stack
	 */
	private final ClauseEprLiteral mReasonUnitClauseLiteral;
	
	private final IDawg<ApplicationTerm, TermVariable> mReasonClauseDawg;

	public DecideStackPropagatedLiteral(boolean polarity, EprPredicate eprPred,
			IDawg<ApplicationTerm, TermVariable> predDawg,
			ClauseEprLiteral unitClauseLiteral,	IDawg<ApplicationTerm, TermVariable> clauseDawg, 
			int index) {
		super(polarity, eprPred, predDawg, index);
		mReasonUnitClauseLiteral = unitClauseLiteral;
		mReasonClauseDawg = clauseDawg;
	}
	
	/**
	 * Returns the dawg that contains those groundings of the clause that was the reason for propagation of this literal, which
	 * correspond to the point where this dsl sets its predicate.
	 *  -- i.e. the dawg that was the preimage of the renameProjectAndSelect operation that yielded this dsl's dawg.
	 */
	public IDawg<ApplicationTerm, TermVariable> getClauseDawg() {
		return mReasonClauseDawg;
	}

	/**
	 * Returns the unit clause that was the reason for setting this propagated decide stack literal.
	 * @return unit clause
	 */
	public ClauseEprLiteral getReasonClauseLit() {
		return mReasonUnitClauseLiteral;
	}

	@Override
	public String toString() {
		return String.format("(DSProp (%d): %c%s %s)", 
				nr, (mPolarity ? ' ' : '~'),  mPred, mDawg);
	}	
}
