/*
 * Copyright (C) 2018 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.smtinterpol.theory.quant;

import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.logic.Theory;

/**
 * A QuantVarConstraint is an inequality between a TermVariable and a GroundTerm or between two TermVariable. Note that
 * only strict inequalities are supported (for integers, we can always obtain strict inequalities if one side is
 * ground), but the underlying atom (i.e. a non-strict inequality) is created and marked as unsupported.
 * 
 * @author Tanja Schindler
 *
 */
public class QuantVarConstraint extends QuantLiteral {

	private final TermVariable mLowerVar;
	private final TermVariable mUpperVar;
	private final GroundTerm mGroundBound;

	/**
	 * Create a new QuantVarConstraint. This should only be called for atoms underlying strict (i.e. negated)
	 * inequalities of the form "TermVariable < GroundTerm" or "GroundTerm < TermVariable". Note that, for integers, we
	 * can always obtain strict inequalities if one side is ground.
	 * <p>
	 * Note that we are actually creating the non-strict variant (i.e. the atom), but mark it as unsupported.
	 * <p>
	 * TODO Rewriting into strict inequalities should be done in QuantLiteralManager.
	 * 
	 * @param term
	 *            the term for the underlying inequality.
	 * @param var
	 *            the TermVariable.
	 * @param isLowerBound
	 *            flag that marks lower bound constraints.
	 * @param groundBound
	 *            the GroundTerm that is a bound for the variable.
	 */
	QuantVarConstraint(final Term term, final TermVariable var, final boolean isLowerBound,
			final GroundTerm groundBound) {
		super(term);
		mLowerVar = isLowerBound ? null : var;
		mUpperVar = isLowerBound ? var : null;
		mGroundBound = groundBound;
		mNegated = new NegQuantLiteral(this);

		// We only support x < t, i.e. (not (<= t x))
		mIsSupported = false;
	}

	/**
	 * Create a new QuantVarConstraint. This should only be called for atoms underlying strict (i.e. negated)
	 * inequalities of the form "TermVariable < TermVariable". We do not support "TermVariable <= TermVariable".
	 * <p>
	 * Note that we are actually creating the non-strict variant (i.e. the atom), but mark it as unsupported.
	 * 
	 * @param term
	 *            the term for the underlying inequality.
	 * @param lowerVar
	 *            the lower variable.
	 * @param upperVar
	 *            the upper variable.
	 */
	QuantVarConstraint(final Term term, final TermVariable lowerVar, final TermVariable upperVar) {
		super(term);
		mLowerVar = lowerVar;
		mUpperVar = upperVar;
		mGroundBound = null;
		mNegated = new NegQuantLiteral(this);

		// We only support x < y, i.e. (not (<= y x))
		mIsSupported = false;
	}

	@Override
	public Term getSMTFormula(final Theory smtTheory, final boolean quoted) {
		// TODO Auto-generated method stub
		return null;
	}

	public boolean isBothVar() {
		return mUpperVar != null && mLowerVar != null;
	}

	public boolean isLowerBound() {
		return mUpperVar != null;
	}

	public boolean isUpperBound() {
		return mLowerVar != null;
	}

	public TermVariable getLowerVar() {
		return mLowerVar;
	}

	public TermVariable getUpperVar() {
		return mUpperVar;
	}

	public GroundTerm getGroundBound() {
		return mGroundBound;
	}
}
