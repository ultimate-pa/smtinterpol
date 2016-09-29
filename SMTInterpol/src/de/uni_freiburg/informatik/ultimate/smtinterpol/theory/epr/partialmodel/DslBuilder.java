package de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.partialmodel;

import java.util.List;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.EprHelpers.Pair;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.EprPredicate;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.clauses.ClauseEprLiteral;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.dawgs.IDawg;
import de.uni_freiburg.informatik.ultimate.util.datastructures.ScopedHashSet;

public class DslBuilder {

//	private int mIndexOnPushStateStack = -1;
//	private int mPushStateStackIndex = - 1;
	private int mDecideStackIndex = -1;
	private boolean mPolarity;
	private EprPredicate mPred;
	private IDawg<ApplicationTerm, TermVariable> mDawg;
	
	private boolean mIsDecision;
	private ClauseEprLiteral mReasonUnitClause;
	private IDawg<ApplicationTerm, TermVariable> mReasonClauseDawg;
	
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
			IDawg<ApplicationTerm, TermVariable> dawg, 
			ClauseEprLiteral reasonUnitClause, IDawg<ApplicationTerm, TermVariable> reasonClauseDawg, 
			boolean isDecision) {
		this(polarity, pred, dawg);
		assert !isDecision : "shouldn't we use the other constructor here?";
		assert pred.getTermVariablesForArguments().equals(dawg.getColnames());
		assert reasonUnitClause.getClause().getVariables().equals(reasonClauseDawg.getColnames());
		mIsDecision = isDecision;
		mReasonUnitClause = reasonUnitClause;
		mReasonClauseDawg = reasonClauseDawg;
	}
	
//	public void setIndexOnPushStateStack(int index) {
//		assert mIndexOnPushStateStack == -1 : "index set twice";
//		mIndexOnPushStateStack = index;
//	}

//	/**
//	 * the index on the push state stack of the pushState that this dsl is pushed into
//	 * @param index
//	 */
//	public void setPushStateStackIndex(int index) {
//		assert mPushStateStackIndex == -1 : "index set twice";
//		mPushStateStackIndex = index;
//	}
	
	public void setDecideStackIndex(int index) {
		assert mDecideStackIndex == -1 : "index set twice";
		mDecideStackIndex = index;
	}
	
	public DecideStackLiteral build() {
//		assert mIndexOnPushStateStack != -1;
//		assert mPushStateStackIndex != -1;
		assert mDecideStackIndex != -1 : "index not set";
//		Pair<Integer, Integer> index = 
//				new Pair<Integer, Integer>(mPushStateStackIndex, mIndexOnPushStateStack);

		if (mIsDecision) {
			assert mReasonUnitClause == null;
			return new DecideStackDecisionLiteral(mPolarity, mPred, mDawg, mDecideStackIndex);
		} else {
			assert mReasonUnitClause != null;
			return new DecideStackPropagatedLiteral(mPolarity, mPred, mDawg, 
					mReasonUnitClause, mReasonClauseDawg, mDecideStackIndex);
		}
	}

	public boolean isOnePoint() {
		return mDawg.isSingleton();
	}

	public EprPredicate getEprPredicate() {
		assert mDawg.isSingleton() : "this is only expected in case we want to build a ground literal instead";
		return mPred;
	}

	public List<ApplicationTerm> getPoint() {
		assert isOnePoint() : "this is only expected in case we want to build a ground literal instead";
		return mDawg.iterator().next();
	}
}
