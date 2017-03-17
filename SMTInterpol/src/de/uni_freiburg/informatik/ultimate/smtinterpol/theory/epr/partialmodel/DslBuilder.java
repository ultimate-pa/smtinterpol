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
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.EprEqualityPredicate;
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
	
	/**
	 * Constructor for the "decision" case.
	 * 
	 * @param polarity
	 * @param pred
	 * @param dawg
	 * @param isDecision
	 */
	public DslBuilder(boolean polarity, EprPredicate pred, 
			IDawg<ApplicationTerm, TermVariable> dawg, boolean isDecision) {
		this(polarity, pred, dawg);
		assert isDecision : "shouldn't we use the other constructor here?";
		mIsDecision = isDecision;
	}
	
	/**
	 * Constructor for the "propagation" case.
	 * 
	 * @param polarity
	 * @param pred
	 * @param propagatedPoints Dawg that represents the points that are effectively set on the decide stack 
	 *     (i.e., propagated points in pred signature
	 * @param reasonUnitClause
	 * @param reasonClauseDawg Dawg that represents the instantiations of the clause that allow for unit propagation.
	 *           (essentially the propagated points in clause signature)
	 * @param isDecision
	 */
	public DslBuilder(boolean polarity, EprPredicate pred, 
			IDawg<ApplicationTerm, TermVariable> propagatedPoints, 
			ClauseEprLiteral reasonUnitClause, 
			IDawg<ApplicationTerm, TermVariable> reasonClauseDawg, 
			boolean isDecision) {
		this(polarity, pred, propagatedPoints);
		assert !isDecision : "shouldn't we use the other constructor here?";
		assert pred.getTermVariablesForArguments().equals(propagatedPoints.getColNames());
		assert reasonUnitClause.getClause().getVariables().equals(reasonClauseDawg.getColNames());
		mIsDecision = isDecision;
		mReasonUnitClause = reasonUnitClause;
		mReasonClauseDawg = reasonClauseDawg;
	}
	

	private DslBuilder(boolean polarity, EprPredicate pred, 
			IDawg<ApplicationTerm, TermVariable> dawg) {
		mPolarity = polarity;
		mPred = pred;
		mDawg = dawg;
	
	}

	public void setDecideStackIndex(int index) {
		assert mDecideStackIndex == -1 : "index set twice";
		mDecideStackIndex = index;
	}
	
	public DecideStackLiteral build() {
		assert mDecideStackIndex != -1 : "index not set";
		
		/*
		 * Environment should guarantee that reflexive points have been filtered out before.
		 * i.e.: "(!mPolarity /\ isEquality) --> !hasReflexivePoints"
		 *  (for both unit propagation and decision case)
		 */
		assert mPolarity
			|| !(mPred instanceof EprEqualityPredicate)
			|| !mIsDecision
			|| !mDawg.hasReflexivePoints() : "about to set a reflexive point (or more) on negated EqualityPredicate";
		
		/*
		 * Whenever we decide something positive on an EqualityPredicate, we take the symmetric and transitive hull 
		 * (together with all decisions/propagations of the EprEqualityPrediacte) instead of the input dawg.
		 */
		if (mPred instanceof EprEqualityPredicate && mPolarity) {
			mDawg = ((EprEqualityPredicate) mPred)
					.computeOverallSymmetricTransitiveClosureForPositiveEqualityPred(mDawg);
		}

//		if (mPred instanceof EprEqualityPredicate) {
//			if (mPolarity) {
//				/*
//				 * whenever we decide something positive on an EqualityPredicate, we take the
//				 * symmetric and transitive hull of all past decideStackLiterals for that predicate, together with the
//				 * inputDawg (instead of just the input dawg).
//				 */
//
//
//
//			} else {
//				if (mDawg.hasReflexivePoints()) {
//					assert mIsDecision : "unit propagation of reflexive points for (not (= ..)) should have been "
//							+ "avoided elsewhere";
//					/*
//					 * If we are trying to make a decision that includes reflexive points for the negated equality
//					 * predicate, we have to "cut" out the reflexive points.
//					 * Cutting out precisely the reflexive points may be impossible, so we allow to cut out more.
//					 * TODO: what if nothing is left?
//					 */
//					
//				}
//			}
//		}

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
