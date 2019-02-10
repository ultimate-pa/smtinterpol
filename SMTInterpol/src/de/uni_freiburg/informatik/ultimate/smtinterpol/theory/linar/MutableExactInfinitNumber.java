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
package de.uni_freiburg.informatik.ultimate.smtinterpol.theory.linar;

import java.math.BigInteger;

import de.uni_freiburg.informatik.ultimate.logic.Rational;

/**
 * Mutable version of the {@link InfinitNumber} class. All arithmetic
 * operations change the value of this object.
 *
 * This class is intended to save some unneeded temporary objects in bigger
 * calculations. This should reduce the number of garbage collections such that
 * the program should run faster.
 *
 * @author Juergen Christ
 */
public class MutableExactInfinitNumber implements Comparable<MutableExactInfinitNumber> {
	// Real part
	Rational mReal;
	// Infinitesimal part
	Rational mEps;
	/// --- Construction ---
	public MutableExactInfinitNumber() {
		this(Rational.ZERO,0);
	}

	public MutableExactInfinitNumber(final Rational a, final Rational eps) {
		mReal = a;
		mEps = eps;
	}
	public MutableExactInfinitNumber(final Rational a, final int eps) {
		this(a, Rational.valueOf(eps, 1));
	}
	public MutableExactInfinitNumber(final InfinitNumber other) {
		this(other.mA, other.mEps);
	}
	public MutableExactInfinitNumber(final MutableExactInfinitNumber other) {
		this(other.mReal, other.mEps);
	}
	MutableExactInfinitNumber assign(final MutableExactInfinitNumber other) {
		mReal = other.mReal;
		mEps = other.mEps;
		return this;
	}
	MutableExactInfinitNumber assign(final InfinitNumber other) {
		mReal = other.mA;
		mEps = Rational.valueOf(other.mEps, 1);
		return this;
	}
	/// --- Arithmetic ---
	/**
	 * Returns this + other.
	 */
	public void add(final ExactInfinitNumber other) {
		mReal = mReal.add(other.getRealValue());
		mEps = mEps.add(other.getEpsilon());
	}

	/**
	 * Returns this + other.
	 */
	public void add(final InfinitNumber other) {
		mReal = mReal.add(other.mA);
		mEps = mEps.add(Rational.valueOf(other.mEps, 1));
	}
	/**
	 * Returns this - other.
	 */
	public void sub(final InfinitNumber other) {
		mReal = mReal.sub(other.mA);
		mEps = mEps.add(Rational.valueOf(-other.mEps, 1));
	}
	/**
	 * Returns c*this.
	 */
	public void mul(final Rational c) {
		mReal = mReal.mul(c);
		mEps = mEps.mul(c);
	}
	/**
	 * Returns this/c.
	 */
	public void div(final Rational c) {
		mReal = mReal.div(c);
		mEps = mEps.div(c);
	}

	/**
	 * Returns this+(fac1*fac2)
	 * @param fac1
	 * @param fac2
	 * @return
	 */
	public void addmul(final ExactInfinitNumber fac1, final Rational fac2) {
		mReal = mReal.add(fac1.getRealValue().mul(fac2));
		mEps = mEps.add(fac1.getEpsilon().mul(fac2));
	}

	/**
	 * Returns this+(fac1*fac2)
	 *
	 * @param fac1
	 * @param fac2
	 * @return
	 */
	public void addmul(final InfinitNumber fac1, final Rational fac2) {
		mReal = mReal.add(fac1.mA.mul(fac2));
		switch (fac1.mEps) {
		case -1:
			mEps = mEps.sub(fac2);
			break;
		case 0:
			break;
		case 1:
			mEps = mEps.add(fac2);
			break;
		}
	}
	/**
	 * Returns this+(fac1*fac2)
	 * @param fac1
	 * @param fac2
	 * @return
	 */
	public void addmul(final InfinitNumber fac1, final BigInteger fac2) {
		addmul(fac1, Rational.valueOf(fac2, BigInteger.ONE));
	}
	/**
	 * Returns (this-s)/d
	 * @param s
	 * @param d
	 * @return
	 */
	public void subdiv(final InfinitNumber s, final Rational d) {
		mReal = mReal.add(s.mA.div(d));
		switch (s.mEps) {
		case -1:
			mEps = mEps.sub(d.inverse());
			break;
		case 0:
			break;
		case 1:
			mEps = mEps.add(d.inverse());
			break;
		}
	}

	public void negate() {
		mReal = mReal.negate();
		mEps = mEps.negate();
	}
	/// --- Comparing ---
	@Override
	public int compareTo(final MutableExactInfinitNumber arg0) {
		final int ac = mReal.compareTo(arg0.mReal);
		if (ac == 0) {
			return mEps.compareTo(arg0.mEps);
		}
		return ac;
	}
	public int compareTo(final InfinitNumber other) {
		final int ac = mReal.compareTo(other.mA);
		if (ac == 0) {
			return mEps.compareTo(Rational.valueOf(other.mEps, 1));
		}
		return ac;
	}
	@Override
	public boolean equals(final Object o) {
		if (o instanceof InfinitNumber) {
			final InfinitNumber n = (InfinitNumber)o;
			return mReal.equals(n.mA) && mEps.equals(Rational.valueOf(n.mEps, 1));
		}
		if (o instanceof MutableExactInfinitNumber) {
			final MutableExactInfinitNumber n = (MutableExactInfinitNumber) o;
			return mReal.equals(n.mReal) && mEps.equals(n.mEps);
		}
		return false;
	}
	@Override
	public int hashCode() {
		return mReal.hashCode() + 257 * mEps.hashCode();
	}
	/// --- Checks ---
	public boolean isInfinity() {
		return mReal.equals(Rational.POSITIVE_INFINITY) || mReal.equals(Rational.NEGATIVE_INFINITY);
	}

	@Override
	public String toString() {
		if (mEps.signum() == 0) {
			return mReal.toString();
		}
		return mReal + (mEps.signum() > 0 ? "+" : "") + mEps + "eps";
	}

	public ExactInfinitNumber toNumber() {
		return new ExactInfinitNumber(mReal, mEps);
	}

	public InfinitNumber toInfinitNumber() {
		assert (mEps == Rational.valueOf(mEps.signum(), 1));
		return new InfinitNumber(mReal, mEps.signum());
	}
}
