/*
 * Copyright (C) 2016-2017 Alexander Nutz (nutz@informatik.uni-freiburg.de)
 * Copyright (C) 2016-2017 University of Freiburg
 *
 * This file is part of SMTInterpol.
 *
 * SMTInterpol is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * SMTInterpol is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with SMTInterpol.  If not, see <http://www.gnu.org/licenses/>.
 */
package de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.partialmodel;

import java.util.List;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.EprPredicate;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.clauses.ClauseEprLiteral;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.dawgs.IDawg;

/**
 * Used to build a decide stack literal incrementally.
 * The builder is mutable so the decide stack literal can be immutable..
 * 
 * @author Alexander Nutz
 */
public class DslBuilder {

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
		assert pred.getTermVariablesForArguments().equals(dawg.getColNames());
		assert reasonUnitClause.getClause().getVariables().equals(reasonClauseDawg.getColNames());
		mIsDecision = isDecision;
		mReasonUnitClause = reasonUnitClause;
		mReasonClauseDawg = reasonClauseDawg;
	}
	

	public void setDecideStackIndex(int index) {
		assert mDecideStackIndex == -1 : "index set twice";
		mDecideStackIndex = index;
	}
	
	public DecideStackLiteral build() {
		assert mDecideStackIndex != -1 : "index not set";

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
