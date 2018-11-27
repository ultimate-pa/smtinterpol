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
 * A QuantEUEquality is an equality EUTerm = EUTerm, where at least one side is not a GroundTerm.
 * 
 * @author Tanja Schindler
 *
 */
public class QuantEUEquality extends QuantLiteral {

	private final EUTerm mLhs;
	private final EUTerm mRhs;

	/**
	 * Create a new QuantEUEquality. This should only be called after checking that at least one of lhs and rhs contains
	 * quantified variables.
	 * 
	 * @param term
	 *            the underlying equality term.
	 * @param lhs
	 *            the left hand side of the equality as an EUTerm.
	 * @param rhs
	 *            the right hand side of the equality as an EUTerm.
	 */
	QuantEUEquality(final Term term, final EUTerm lhs, final EUTerm rhs) {
		super(term);
		assert !(lhs instanceof GroundTerm && rhs instanceof GroundTerm);
		mLhs = lhs;
		mRhs = rhs;
		mNegated = new NegQuantLiteral(this);
	}

	@Override
	public Term getSMTFormula(final Theory smtTheory, final boolean quoted) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	Literal instantiate(Map<TermVariable, Term> instantiation) {
		// Build a CCEquality
		return null;
	}

	EUTerm getLhs() {
		return mLhs;
	}

	EUTerm getRhs() {
		return mRhs;
	}

}
