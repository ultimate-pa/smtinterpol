/*
 * Copyright (C) 2026 University of Freiburg
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

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.logic.AnnotatedTerm;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.SMTLIBConstants;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.smtinterpol.util.Polynomial;

/**
 * A ground arithmetical atom that compares the numeric λ with λ-free terms, i.e., {@code (<= P 0)} or {@code (= L R)}
 * where λ occurs in P resp. L - R only as a linear summand {@code k·λ}.
 *
 * Since λ is smaller than every λ-free term, such an atom has a fixed value: {@code (<= P 0)} is true if k is positive
 * and false otherwise, and {@code (= L R)} is false. All three facts follow from {@code Q < 0}, where
 * {@code Q = c·λ + q} with {@code c = |k| > 0} is P resp. L - R multiplied by the sign of k. In proofs, λ is defined
 * as {@code min(b_1, ..., b_n) - 1} over the bounds {@link #getBounds()} of all atoms, which implies {@code Q < 0}.
 *
 * @author Jochen Hoenicke
 */
public final class LambdaBound {
	private final ApplicationTerm mAtom;
	private final Term mLambda;
	/** The sign of k. */
	private final int mSign;
	/** The positive coefficient c of λ in Q. */
	private final Rational mCoeff;
	/** The λ-free part q of Q. */
	private final Polynomial mRest;

	private LambdaBound(final ApplicationTerm atom, final Term lambda, final int sign, final Rational coeff,
			final Polynomial rest) {
		mAtom = atom;
		mLambda = lambda;
		mSign = sign;
		mCoeff = coeff;
		mRest = rest;
	}

	/**
	 * Analyze a ground atom.
	 *
	 * @param atom
	 *            an atom {@code (<= P 0)} or an equality.
	 * @return the analysis, or null if the atom does not compare λ linearly with λ-free terms.
	 */
	public static LambdaBound analyze(final Term atom) {
		if (!(atom instanceof ApplicationTerm) || atom.getFreeVars().length > 0) {
			return null;
		}
		final ApplicationTerm app = (ApplicationTerm) atom;
		final Term[] params = app.getParameters();
		final Polynomial poly;
		if (app.getFunction().getName() == SMTLIBConstants.LEQ && params.length == 2) {
			poly = new Polynomial(params[0]);
			poly.add(Rational.MONE, params[1]);
		} else if (app.getFunction().getName() == SMTLIBConstants.EQUALS && params.length == 2
				&& params[0].getSort().isNumericSort()) {
			poly = new Polynomial(params[0]);
			poly.add(Rational.MONE, params[1]);
		} else {
			return null;
		}
		Term lambda = null;
		Rational lambdaCoeff = null;
		final Polynomial rest = new Polynomial();
		for (final Entry<Map<Term, Integer>, Rational> summand : poly.getSummands().entrySet()) {
			final Map<Term, Integer> monomial = summand.getKey();
			if (monomial.size() == 1) {
				final Entry<Term, Integer> factor = monomial.entrySet().iterator().next();
				if (factor.getValue() == 1 && QuantUtil.isLambda(factor.getKey())) {
					if (lambda != null) {
						return null;
					}
					lambda = factor.getKey();
					lambdaCoeff = summand.getValue();
					continue;
				}
			}
			for (final Term factor : monomial.keySet()) {
				if (containsLambda(factor)) {
					return null;
				}
			}
			rest.add(summand.getValue(), monomial);
		}
		if (lambda == null) {
			return null;
		}
		final int sign = lambdaCoeff.signum();
		if (sign < 0) {
			rest.mul(Rational.MONE);
		}
		return new LambdaBound(app, lambda, sign, lambdaCoeff.abs(), rest);
	}

	private static boolean containsLambda(final Term term) {
		final ArrayDeque<Term> todo = new ArrayDeque<>();
		final Set<Term> seen = new HashSet<>();
		todo.add(term);
		while (!todo.isEmpty()) {
			final Term t = todo.removeLast();
			if (!seen.add(t)) {
				continue;
			}
			if (QuantUtil.isLambda(t)) {
				return true;
			}
			if (t instanceof ApplicationTerm) {
				for (final Term p : ((ApplicationTerm) t).getParameters()) {
					todo.add(p);
				}
			} else if (t instanceof AnnotatedTerm) {
				todo.add(((AnnotatedTerm) t).getSubterm());
			}
		}
		return false;
	}

	public ApplicationTerm getAtom() {
		return mAtom;
	}

	public Term getLambda() {
		return mLambda;
	}

	/**
	 * @return true if the atom is an inequality {@code (<= P 0)}, false if it is an equality.
	 */
	public boolean isInequality() {
		return mAtom.getFunction().getName() == SMTLIBConstants.LEQ;
	}

	/**
	 * @return the value of the atom when λ is smaller than all bounds.
	 */
	public boolean getValue() {
		return isInequality() && mSign > 0;
	}

	/**
	 * @return the sign of the coefficient of λ in P resp. L - R; Q is this term multiplied by the sign.
	 */
	public int getSign() {
		return mSign;
	}

	/**
	 * @return the positive coefficient c of λ in Q.
	 */
	public Rational getCoeff() {
		return mCoeff;
	}

	/**
	 * @return the λ-free part q of Q.
	 */
	public Polynomial getRest() {
		return mRest;
	}

	/**
	 * Compute the bounds b for which {@code λ <= b - 1} implies {@code Q < 0}: {@code -q} if c = 1; {@code -q} and 0
	 * if c > 1, since then {@code c·λ + q <= (-q - 1) + (c - 1)·(-1) + q = -c}; and {@code -q/c} if c < 1.
	 *
	 * @return the bounds as terms of the sort of λ.
	 */
	public List<Term> getBounds() {
		final Sort sort = mLambda.getSort();
		final List<Term> bounds = new ArrayList<>(2);
		final Polynomial negRest = new Polynomial();
		final int cmp = mCoeff.compareTo(Rational.ONE);
		negRest.add(cmp < 0 ? mCoeff.inverse().negate() : Rational.MONE, mRest);
		bounds.add(negRest.toTerm(sort));
		if (cmp > 0) {
			bounds.add(Rational.ZERO.toTerm(sort));
		}
		return bounds;
	}
}
