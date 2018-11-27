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
	 * @param term
	 *            the underlying equality atom term.
	 * @param positive
	 *            flag that marks if the term is positive or negated.
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
	QuantLiteral getQuantEquality(final Term term, final boolean positive, final SourceAnnotation source,
			final Term lhs, final Term rhs) {
		final QuantLiteral atom = mQuantLits.get(term);
		if (atom != null) {
			if (positive && atom.isSupported()) {
				return atom;
			} else if (!positive && atom.negate().isSupported()) {
				return atom;
			} else {
				throw new UnsupportedOperationException(
						(positive ? "Negated term " : "Term ") + term + " not in almost uninterpreted fragment!");
			}
		}

		SMTAffineTerm rightAff = SMTAffineTerm.create(rhs);
		rightAff.negate();
		SMTAffineTerm linAdded = SMTAffineTerm.create(lhs);
		linAdded.add(rightAff);
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
			if (positive && !lhs.getSort().getName().equals("Int")) { // We support var=ground only for integers.
				throw new UnsupportedOperationException("Term " + term + " not in almost uninterpreted fragment!");
			}
			// We can either do destructive equality reasoning later (if !positive), or build an aux axiom.
			SMTAffineTerm remainderAffine = new SMTAffineTerm(summands, constant, lhs.getSort());
			if (leftVar != null) {
				remainderAffine.negate();
			}
			Term remainder = remainderAffine.toTerm(mClausifier.getTermCompiler(), lhs.getSort());
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
	 * Get the quantified inequality literal for a supported literal. Note that positive literals (x<=t) (they come as
	 * (x-t<=0)) are rewritten into the form ~(t+1<=x) (for x Int).
	 * <p>
	 * We support the following inequality literals: (i) (EUTerm <= 0) (and negated) (ii) ~(TermVariable <= GroundTerm)
	 * (iii) ~(GroundTerm <= TermVariable) (iv) ~(TermVariable <= TermVariable).
	 * 
	 * @param term
	 *            an inequality of the form "term <= 0".
	 * @param positive
	 *            flag that marks if the term appears positively or negated in the clause.
	 * @param source
	 *            the source partition of the term.
	 * @param lhs
	 *            the left hand side of "term <= 0".
	 * 
	 * @return a QuantLiteral for the underlying quantified inequality atom. Throws an exception if the literal is not
	 *         supported.
	 */
	QuantLiteral getQuantInequality(final Term term, final boolean positive, final SourceAnnotation source,
			final Term lhs) {

		final QuantLiteral lit = mQuantLits.get(term);
		if (lit != null) {
			if (positive && lit.isSupported()) {
				return lit;
			} else if (!positive && lit.negate().isSupported()) {
				return lit;
			} else {
				throw new UnsupportedOperationException(
						(positive ? "Term " : "Negated term ") + term + " not in almost uninterpreted fragment!");
			}
		}

		final SMTAffineTerm linTerm = SMTAffineTerm.create(lhs);
		Map<Term, Rational> summands = linTerm.getSummands();
		final Rational constant = linTerm.getConstant();

		// Check for free (=quantified) variables that do not appear in EUTerms.
		TermVariable lower = null; // the lower variable
		TermVariable upper = null;
		final Iterator<Term> it = summands.keySet().iterator();
		while (it.hasNext()) {
			Term summand = it.next();
			if (summand instanceof TermVariable) {
				if (positive != summands.get(summand).isNegative()) { // xor
					// the variable has a lower bound
					if (upper != null) {
						throw new UnsupportedOperationException(
								"Term " + term + " not in almost uninterpreted fragment!");
					}
					upper = (TermVariable) summand;
					it.remove();
				} else {
					// the variable has an upper bound
					if (lower != null) {
						throw new UnsupportedOperationException(
								"Term " + term + " not in almost uninterpreted fragment!");
					}
					lower = (TermVariable) summand;
					it.remove();
				}
			}
		}

		// If the literal is a QuantEUBoundConstraint, keep the given form.
		if (lower == null && upper == null) {
			final EUTerm euAffine = mEUTermManager.getEUTerm(lhs, source);
			QuantEUBoundConstraint euConstr = new QuantEUBoundConstraint(term, euAffine);
			mQuantLits.put(term, euConstr);
			return euConstr;
		}

		// Else, bring the literals into the form ~(x<=t), ~(t<=x), ~(x<=y)
		if (positive) {
			// First step of rewriting positive (x-t<=0) into ~(t+1<=x) for x integer
			if (lhs.getSort().getName().equals("Int")) {
				constant.add(Rational.MONE);
			} else {
				throw new UnsupportedOperationException("Term " + term + " not in almost uninterpreted fragment!");
			}
		}

		if (lower != null && upper != null) {
			// Two variables can only be compared with each other.
			if (!it.hasNext() && constant == Rational.ZERO) {
				QuantVarConstraint varConstr = new QuantVarConstraint(term, lower, upper);
				if (positive) {
					// TODO Requires testing!
					// Second step of converting positive literals into negated ones.
					// This can happen for positive (x+1<=y) (---> converted into ~(y<=x))
					varConstr.negate();
				}
				mQuantLits.put(term, varConstr);
				return varConstr;
			}
		} else {
			final boolean hasLowerBound = (upper != null);
			final TermVariable var = hasLowerBound ? upper : lower;
			SMTAffineTerm boundAffine = new SMTAffineTerm(summands, constant, lhs.getSort());
			// Isolate variable by bringing bound to the other side
			if (positive == hasLowerBound) { // for rewriting ~(x-t<=0) into ~(x<=t) and (x-t<=0) into ~(t+1<=x)
				boundAffine.negate();
			}
			Term bound = boundAffine.toTerm(mClausifier.getTermCompiler(), lhs.getSort());
			// The variable can only be bound by ground terms.
			if (bound.getFreeVars().length == 0) {
				final EUTerm boundTerm = mEUTermManager.getEUTerm(bound, source);
				QuantVarConstraint varConstr = new QuantVarConstraint(term, var, hasLowerBound, (GroundTerm) boundTerm);
				if (positive) {
					// Second step of converting positive literals into negated ones.
					// This can happen for positive (x+1<=y) (---> converted into ~(y<=x))
					varConstr.negate();
				}
				mQuantLits.put(term, varConstr);
				return varConstr;
			}
		}
		throw new UnsupportedOperationException(
				(positive ? "Term " : "Negated term ") + term + " not in almost uninterpreted fragment!");
	}
}
