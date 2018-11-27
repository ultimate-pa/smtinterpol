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

import java.util.Map;

import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.logic.Theory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.Literal;

/**
 * A QuantVarEquality is an equality "TermVariable = TermVariable" or "TermVariable = GroundTerm". Negated
 * QuantVarEqualities will be used for Destructive Equality Reasoning, positive QuantVarEqualities are only allowed for
 * integers and with only one variable and will be treated by an auxiliary clause.
 * 
 * @author Tanja Schindler
 *
 */
public class QuantVarEquality extends QuantLiteral {

	private final TermVariable mLeftVar;
	private final TermVariable mRightVar; // = null iff mGround != null
	private final GroundTerm mGround;

	/**
	 * Create a new QuantVarEquality of the form "TermVariable = TermVariable". Only the negated version is supported,
	 * hence this should only be called for the atom of a disequality.
	 * 
	 * @param term
	 *            the term for the underlying equality atom.
	 * @param leftVar
	 *            the variable on the left hand side.
	 * @param rightVar
	 *            the variable at the right hand side.
	 */
	QuantVarEquality(final Term term, final TermVariable leftVar, final TermVariable rightVar) {
		super(term);
		mLeftVar = leftVar;
		mRightVar = rightVar;
		mGround = null;
		mNegated = new NegQuantLiteral(this);

		// We only support disequalities between two variables.
		mIsSupported = false;
	}

	/**
	 * Create a new QuantVarEquality of the form "TermVariable = GroundTerm". In the positive case, this should only be
	 * called for integers.
	 * 
	 * @param term
	 *            the term for the underlying equality atom.
	 * @param var
	 *            the variable.
	 * @param ground
	 *            the ground term.
	 */
	QuantVarEquality(final Term term, final TermVariable var, final GroundTerm ground) {
		super(term);
		mLeftVar = var;
		mRightVar = null;
		mGround = ground;
		mNegated = new NegQuantLiteral(this);

		// We support equalites between a variable (integer!) and a ground term, BUT by means of an aux clause.
		// We could treat them directly, but then we would have more case distinctions.
		if (!var.getSort().equals("Int")) {
			mIsSupported = false;
		}
	}

	@Override
	public Term getSMTFormula(final Theory smtTheory, final boolean quoted) {
		// TODO Auto-generated method stub
		return null;
	}

	Literal instantiate(Map<TermVariable, Term> instantiation) {
		// TODO Builds a CCEquality or an LAEquality
		return null;
	}

	boolean isBothVar() {
		return mLeftVar != null && mRightVar != null;
	}

	TermVariable getLeftVar() {
		return mLeftVar;
	}

	TermVariable getRightVar() {
		assert isBothVar() : "(Dis)eq contains only one variable!";
		return mRightVar;
	}

	GroundTerm getGroundTerm() {
		assert !isBothVar() : "Diseq between two variables!";
		return mGround;
	}
}
