/*
 * Copyright (C) 2009-2012 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.smtinterpol.convert;

import java.math.BigDecimal;
import java.math.BigInteger;
import java.util.Iterator;
import java.util.LinkedHashMap;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.ConstantTerm;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.Theory;
import de.uni_freiburg.informatik.ultimate.util.HashUtils;

/**
 * Represents an affine term. An affine term is a sum
 *
 * <pre>
 * Σ c_i * x_i + c,
 * </pre>
 *
 * where c_i, c are rational (or integer) constants and x_i are flat terms that are not themselves affine terms.
 *
 * @author hoenicke.
 */
public final class SMTAffineTerm {

	private Sort mSort;
	private Map<Term, Rational> mSummands;
	private Rational mConstant;

	public SMTAffineTerm(final Sort sort) {
		mSummands = new LinkedHashMap<Term, Rational>();
		mConstant = Rational.ZERO;
		mSort = sort;
	}

	public SMTAffineTerm(final Map<Term, Rational> summands, final Rational constant, final Sort sort) {
		mSummands = summands;
		mConstant = constant;
		mSort = sort;
	}

	public SMTAffineTerm(final Term term) {
		this(term.getSort());
		Term[] subterms;
		if (term instanceof ApplicationTerm && ((ApplicationTerm) term).getFunction().getName().equals("+")) {
			subterms = ((ApplicationTerm) term).getParameters();
		} else {
			subterms = new Term[] { term };
		}
		for (Term subterm : subterms) {
			Rational factor = Rational.ONE;
			if (subterm instanceof ApplicationTerm && ((ApplicationTerm) subterm).getFunction().getName() == "*") {
				final Term[] params = ((ApplicationTerm) subterm).getParameters();
				assert params.length == 2;
				factor = convertConstant((ConstantTerm) params[0]);
				subterm = params[1];
			}
			if (subterm instanceof ApplicationTerm && ((ApplicationTerm) subterm).getFunction().getName() == "-"
					&& ((ApplicationTerm) subterm).getParameters().length == 1) {
				factor = factor.negate();
				subterm = ((ApplicationTerm) subterm).getParameters()[0];
			}
			if (subterm instanceof ApplicationTerm
					&& ((ApplicationTerm) subterm).getFunction().getName() == "to_real") {
				subterm = ((ApplicationTerm) subterm).getParameters()[0];
			}
			if (subterm instanceof ConstantTerm) {
				assert factor == Rational.ONE && mConstant == Rational.ZERO;
				mConstant = convertConstant((ConstantTerm) subterm);
			} else {
				assert !(mSummands.containsKey(subterm));
				mSummands.put(subterm, factor);
			}
		}
	}

	public void mul(final Rational factor) {
		if (factor == Rational.ZERO) {
			mSummands.clear();
			mConstant = Rational.ZERO;
			return;
		}

		for (final Map.Entry<Term, Rational> entry : mSummands.entrySet()) {
			entry.setValue(entry.getValue().mul(factor));
		}
		mConstant = mConstant.mul(factor);
	}

	public void add(final Rational constant) {
		mConstant = mConstant.add(constant);
	}

	public void add(final SMTAffineTerm other) {
		assert getSort().equals(other.getSort());
		addUnchecked(other);
	}

	public void addUnchecked(final SMTAffineTerm other) {
		for (final Map.Entry<Term, Rational> entry : other.mSummands.entrySet()) {
			final Term var = entry.getKey();
			if (mSummands.containsKey(var)) {
				final Rational r = mSummands.get(var).add(entry.getValue());
				if (r.equals(Rational.ZERO)) {
					mSummands.remove(var);
				} else {
					mSummands.put(var, r);
				}
			} else {
				mSummands.put(var, entry.getValue());
			}
		}
		mConstant = mConstant.add(other.mConstant);
		if (mSort != other.mSort && other.mSort.getName().equals("Real")) {
			mSort = other.mSort;
		}
	}

	public static Rational convertConstant(final ConstantTerm term) {
		Rational constant;
		final Object value = term.getValue();
		if (value instanceof BigInteger) {
			constant = Rational.valueOf((BigInteger) value, BigInteger.ONE);
		} else if (value instanceof BigDecimal) {
			final BigDecimal decimal = (BigDecimal) value;
			if (decimal.scale() <= 0) {
				final BigInteger num = decimal.toBigInteger();
				constant = Rational.valueOf(num, BigInteger.ONE);
			} else {
				final BigInteger num = decimal.unscaledValue();
				final BigInteger denom = BigInteger.TEN.pow(decimal.scale());
				constant = Rational.valueOf(num, denom);
			}
		} else if (value instanceof Rational) {
			constant = (Rational) value;
		} else {
			throw new InternalError("Something went wrong with constants!");
		}
		return constant;
	}

	/**
	 * Convert affine term to a different sort. This should only be used to convert from int to real, as it does not
	 * truncate.
	 *
	 * @param other
	 *            the affine term to convert.
	 * @param sort
	 *            the new sort.
	 */
	public void typecast(final Sort realSort) {
		mSort = realSort;
	}

	public void div(final Rational c) {
		mul(c.inverse());
	}

	public void negate() {
		mul(Rational.MONE);
	}

	public boolean isConstant() {
		return mSummands.isEmpty();
	}

	public Rational getConstant() {
		return mConstant;
	}

	public boolean isIntegral() {
		return mSort.getName().equals("Int");
	}

	public Sort getSort() {
		return mSort;
	}

	Rational getCoefficient(final Term subterm) {
		final Rational coeff = mSummands.get(subterm);
		return coeff == null ? Rational.ZERO : coeff;
	}

	public Rational getGcd() {
		assert (!mSummands.isEmpty());
		final Iterator<Rational> it = mSummands.values().iterator();
		Rational gcd = it.next().abs();
		while (it.hasNext()) {
			gcd = gcd.gcd(it.next().abs());
		}
		return gcd;
	}

	public Map<Term, Rational> getSummands() {
		return mSummands;
	}

	/**
	 * Convert the affine term to plain SMTLib term. Note that this is does not convert terms inside this term. Instead
	 * use the static method cleanup() for this, which works on arbitrary terms.
	 *
	 * @see SMTAffineTerm.cleanup
	 */
	public Term toTerm() {
		assert mSort.isNumericSort();
		final Theory t = mSort.getTheory();
		int size = mSummands.size();
		if (size == 0 || !mConstant.equals(Rational.ZERO)) {
			size++;
		}
		final Term[] sum = new Term[size];
		int i = 0;
		for (final Map.Entry<Term, Rational> factor : mSummands.entrySet()) {
			Term convTerm = factor.getKey();
			if (!convTerm.getSort().equals(mSort)) {
				convTerm = t.term("to_real", convTerm);
			}
			if (factor.getValue().equals(Rational.MONE)) {
				convTerm = t.term("-", convTerm);
			} else if (!factor.getValue().equals(Rational.ONE)) {
				final Term convfac = factor.getValue().toTerm(mSort);
				convTerm = t.term("*", convfac, convTerm);
			}
			sum[i++] = convTerm;
		}
		if (i < size) {
			sum[i++] = mConstant.toTerm(mSort);
		}
		return size == 1 ? sum[0] : t.term("+", sum);
	}

	@Override
	public String toString() {
		return toTerm().toString();
	}

	/**
	 * Normalize the order of the summands.
	 *
	 * @param compiler
	 *            TermCompiler used to unify SMTAffineTerms
	 * @return this or the singleton term corresponding to this.
	 */
	public void normalize(final TermCompiler compiler) {
		mSummands = compiler.unify(mSummands);
	}

	public boolean isAllIntSummands() {
		for (final Map.Entry<Term, Rational> me : mSummands.entrySet()) {
			if (!me.getKey().getSort().getName().equals("Int")) {
				return false;
			}
			if (!me.getValue().isIntegral()) {
				return false;
			}
		}
		return true;
	}

	@Override
	public boolean equals(final Object other) {
		if (!(other instanceof SMTAffineTerm)) {
			return false;
		}
		final SMTAffineTerm o = (SMTAffineTerm) other;
		return mSummands.equals(o.mSummands) && mConstant.equals(o.mConstant);
	}

	@Override
	public int hashCode() {
		return HashUtils.hashJenkins(mConstant.hashCode(), mSummands);
	}
}
