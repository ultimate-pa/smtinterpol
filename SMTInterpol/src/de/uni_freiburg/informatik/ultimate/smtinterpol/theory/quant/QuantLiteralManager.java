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

import java.util.HashMap;
import java.util.Iterator;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.smtinterpol.convert.Clausifier;
import de.uni_freiburg.informatik.ultimate.smtinterpol.convert.SMTAffineTerm;
import de.uni_freiburg.informatik.ultimate.smtinterpol.proof.SourceAnnotation;

/**
 * Manage quantified literals. That is, decide if the literal is supported and build the supported literals.
 * 
 * @author Tanja Schindler
 *
 */
public class QuantLiteralManager {

	private final QuantifierTheory mQuantTheory;
	private final Clausifier mClausifier;
	private final EUTermManager mEUTermManager;

	/**
	 * The quantified literals built so far.
	 */
	private Map<Term, QuantLiteral> mQuantLits;

	QuantLiteralManager(final QuantifierTheory quantTheory) {
		mQuantTheory = quantTheory;
		mClausifier = quantTheory.getClausifier();
		mEUTermManager = quantTheory.getEUTermManager();

		mQuantLits = new HashMap<Term, QuantLiteral>();
	}

	/**
	 * Get the quantified equality <em>atom</em> for supported literals.
	 * <p>
	 * We support the following (dis-)equality literals: (i) EUTerm = EUTerm (pos. and neg.), (ii) TermVariable =
	 * GroundTerm, (iii) TermVariable != GroundTerm, and (iv) TermVariable != TermVariable.
	 * <p>
	 * Note: (iii) and (iv) are used for destructive equality reasoning.
	 * 
	 * @param positive
	 *            flag that marks if the term is positive or negated.
	 * @param term
	 *            the underlying equality atom term.
	 * @param source
	 *            the source partition of the term.
	 * @param lhs
	 *            the left hand side of the equality.
	 * @param rhs
	 *            the right hand side of the equality.
	 * 
	 * @return the QuantLiteral for the underlying equality. Throws an exception if the <em>literal</em> is not
	 *         supported.
	 */
	QuantLiteral getQuantEquality(final boolean positive, final Term term, final SourceAnnotation source,
			final Term lhs, final Term rhs) {
		final QuantLiteral atom = mQuantLits.get(term);
		if (atom != null) {
			if (positive && atom.isSupported()) {
				return atom;
			} else if (!positive && atom.negate().isSupported()) {
				// TODO At the moment, all negated atoms are supported, right?
				return atom;
			} else {
				throw new UnsupportedOperationException(
						(positive ? "Negated term " : "Term ") + term + " not in almost uninterpreted fragment!");
			}
		}

		SMTAffineTerm linAdded = SMTAffineTerm.create(lhs).add(SMTAffineTerm.create(rhs).negate());
		Map<Term, Rational> summands = linAdded.getSummands();
		final Rational constant = linAdded.getConstant();

		TermVariable leftVar = null;
		TermVariable rightVar = null;
		final Iterator<Term> it = summands.keySet().iterator();
		while (it.hasNext()) {
			Term summand = it.next();
			if (summand instanceof TermVariable) {
				if (summands.get(summand).isNegative()) {
					if (rightVar != null) {
						throw new UnsupportedOperationException(
								"Term " + term + " not in almost uninterpreted fragment!");
					}
					rightVar = (TermVariable) summand;
					it.remove();
				} else {
					if (leftVar != null) {
						throw new UnsupportedOperationException(
								"Term " + term + " not in almost uninterpreted fragment!");
					}
					leftVar = (TermVariable) summand;
					it.remove();
				}
			}
		}

		if (leftVar != null && rightVar != null) {
			if (!positive && summands.isEmpty() && constant.equals(Rational.ZERO)) {
				QuantVarEquality varEq = new QuantVarEquality(term, leftVar, rightVar);
				mQuantLits.put(term, varEq);
				return varEq;
			}
		} else if (leftVar != null || rightVar != null) {
			if (positive && !linAdded.isIntegral()) { // We support var=ground only for integers.
				throw new UnsupportedOperationException("Term " + term + " not in almost uninterpreted fragment!");
			}
			// We can either do destructive equality reasoning later (if !positive), or build an aux axiom.
			SMTAffineTerm remainderAffine = SMTAffineTerm.create(summands, constant, linAdded.getSort());
			if (leftVar != null) {
				remainderAffine.negate();
			}
			Term remainder = SMTAffineTerm.cleanup(remainderAffine);
			if (remainder.getFreeVars().length == 0) { // The variable can only be bound by ground terms.
				final EUTerm boundTerm = mEUTermManager.getEUTerm(remainder, source);
				assert boundTerm instanceof GroundTerm;
				final TermVariable var = leftVar != null ? leftVar : rightVar;
				QuantVarEquality varEq = new QuantVarEquality(term, var, (GroundTerm) boundTerm);
				mQuantLits.put(term, varEq);
				return varEq;
			}
		} else if (leftVar == null && rightVar == null) {
			final EUTerm lhsEU = mEUTermManager.getEUTerm(lhs, source);
			final EUTerm rhsEU = mEUTermManager.getEUTerm(rhs, source);
			QuantEUEquality euEq = new QuantEUEquality(term, lhsEU, rhsEU);
			mQuantLits.put(term, euEq);
			return euEq;
		}
		throw new UnsupportedOperationException(
				(positive ? "Term " : "Negated term ") + term + " not in almost uninterpreted fragment!");
	}

	/**
	 * Get the quantified inequality literal for supported literal.
	 * <p>
	 * We support the following inequality literals: (i) (EUTerm <= 0) (and negated) (ii) (TermVariable < GroundTerm)
	 * (iii) (GroundTerm < TermVariable) (iv) (TermVariable < TermVariable).
	 * 
	 * @param positive
	 *            flag that marks if the term is positive or negated.
	 * @param term
	 *            an inequality of the form "term <= 0".
	 * @param source
	 *            the source partition of the term.
	 * @param lhs
	 *            the left hand side of "term <= 0".
	 * @return a QuantLiteral for the underlying quantified inequality atom. Throws an exception if the <em>literal</em>
	 *         is not supported.
	 */
	QuantLiteral getQuantInequality(final boolean positive, final Term term, final SourceAnnotation source,
			final Term lhs) {
		final QuantLiteral atom = mQuantLits.get(term);
		if (atom != null) {
			if (positive && atom.isSupported()) {
				return atom;
			} else if (!positive && atom.negate().isSupported()) {
				// TODO At the moment, all negated atoms are supported, right?
				return atom;
			} else {
				throw new UnsupportedOperationException(
						(positive ? "Term " : "Negated term ") + term + " not in almost uninterpreted fragment!");
			}
		}

		final SMTAffineTerm linTerm = SMTAffineTerm.create(lhs);
		Map<Term, Rational> summands = linTerm.getSummands();
		final Rational constant = linTerm.getConstant();

		TermVariable lower = null; // the lower variable
		TermVariable upper = null;
		final Iterator<Term> it = summands.keySet().iterator();
		while (it.hasNext()) {
			Term summand = it.next();
			if (summand instanceof TermVariable) {
				if (summands.get(summand).isNegative()) {
					if (upper != null) {
						throw new UnsupportedOperationException(
								"Term " + term + " not in almost uninterpreted fragment!");
					}
					upper = (TermVariable) summand;
					it.remove();
				} else {
					if (lower != null) {
						throw new UnsupportedOperationException(
								"Term " + term + " not in almost uninterpreted fragment!");
					}
					lower = (TermVariable) summand;
					it.remove();
				}
			}
		}
		if (!positive) { // lower and upper must be switched in (not (var1 - var2 <= 0))
			final TermVariable temp = lower;
			lower = upper;
			upper = temp;
		}

		if (!positive && lower != null && upper != null) {
			if (!it.hasNext() && constant == Rational.ZERO) { // Two variables can only be compared with each other.
				QuantVarConstraint varConstr = new QuantVarConstraint(term, lower, upper);
				mQuantLits.put(term, varConstr);
				return varConstr;
			}
		} else if (lower != null || upper != null) {
			final boolean isLower = (upper != null);
			final TermVariable var = isLower ? upper : lower;
			if (positive && !var.getSort().getName().equals("Int")) {
				throw new UnsupportedOperationException("Term " + term + " not in almost uninterpreted fragment!");
			}
			Term bound = SMTAffineTerm.cleanup(SMTAffineTerm.create(summands,
					constant.add(positive ? Rational.ONE : Rational.ZERO), lhs.getSort()));
			if (bound.getFreeVars().length == 0) { // The variable can only be bound by ground terms.
				final EUTerm boundTerm = mEUTermManager.getEUTerm(bound, source);
				QuantVarConstraint varConstr = new QuantVarConstraint(term, var, isLower, (GroundTerm) boundTerm);
				mQuantLits.put(term, varConstr);
				return varConstr;
			}
		} else if (lower == null && upper == null) {
			final EUTerm euAffine = mEUTermManager.getEUTerm(lhs, source);
			QuantEUBoundConstraint euConstr = new QuantEUBoundConstraint(term, euAffine);
			mQuantLits.put(term, euConstr);
			return euConstr;
		}
		throw new UnsupportedOperationException(
				(positive ? "Term " : "Negated term ") + term + " not in almost uninterpreted fragment!");
	}
}
