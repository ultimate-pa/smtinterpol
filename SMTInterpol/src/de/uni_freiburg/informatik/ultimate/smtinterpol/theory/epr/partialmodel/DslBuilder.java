package de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.partialmodel;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.EprPredicate;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.clauses.ClauseEprLiteral;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.dawgs.IDawg;

public class DslBuilder {

	private int mIndex = -1;
	private boolean mPolarity;
	private EprPredicate mPred;
	private IDawg<ApplicationTerm, TermVariable> mDawg;
	
	private boolean mIsDecision;
	private ClauseEprLiteral mReasonUnitClause;
	
	private DslBuilder(boolean polarity, EprPredicate pred, 
			IDawg<ApplicationTerm, TermVariable> dawg) {
		mPolarity = polarity;
		mPred = pred;
		mDawg = dawg;

	}

	public DslBuilder(boolean polarity, EprPredicate pred, 
			IDawg<ApplicationTerm, TermVariable> dawg, boolean isDecision) {
		this(polarity, pred, dawg);
		assert isDecision : "shouldn't we use the other constructor here?";
		mIsDecision = isDecision;
	}
	
	public DslBuilder(boolean polarity, EprPredicate pred, 
			IDawg<ApplicationTerm, TermVariable> dawg, ClauseEprLiteral reasonUnitClause, boolean isDecision) {
		assert !isDecision : "shouldn't we use the other constructor here?";
		mPolarity = polarity;
		mPred = pred;
		mDawg = dawg;
		mIsDecision = isDecision;
		mReasonUnitClause = reasonUnitClause;
	}
	
	public void setIndex(int index) {
		assert mIndex == -1 : "index set twice";
		mIndex = index;
	}
	
	public DecideStackLiteral build() {
		if (mIsDecision) {
			assert mReasonUnitClause == null;
			return new DecideStackDecisionLiteral(mPolarity, mPred, mDawg, mIndex);
		} else {
			assert mReasonUnitClause != null;
			return new DecideStackPropagatedLiteral(mPolarity, mPred, mDawg, mReasonUnitClause, mIndex);
		}
	}

	public boolean isOnePoint() {
		return mDawg.isSingleton();
	}
}
