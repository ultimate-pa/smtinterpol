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

/**
 * A QuantEUBoundConstraint is an inequality of the form QuantAffineTerm <= 0.
 *
 * @author Tanja Schindler
 *
 */
public class QuantEUBoundConstraint extends QuantLiteral {

	/**
	 * The QuantAffineTerm in "QuantAffineTerm <= 0".
	 */
	private final QuantAffineTerm mAffineTerm;

	/**
	 * Create a new QuantEUBoundConstraint for a given term. This should only be called after checking that the term
	 * contains quantified variables.
	 *
	 * @param term
	 *            the underlying term of the form "term <= 0" (or negated).
	 * @param lhs
	 *            the left hand side of the constraint.
	 */
	QuantEUBoundConstraint(final Term term, EUTerm lhs) {
		super(term);
		assert !(lhs instanceof GroundTerm);
		if (!(lhs instanceof QuantAffineTerm)) {
			lhs = new QuantAffineTerm(lhs);
		}
		mAffineTerm = (QuantAffineTerm) lhs;
		mNegated = new NegQuantLiteral(this);
	}

	QuantAffineTerm getAffineTerm() {
		return mAffineTerm;
	}
}
