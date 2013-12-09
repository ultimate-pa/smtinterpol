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
package de.uni_freiburg.informatik.ultimate.logic;

import java.math.BigInteger;

import org.junit.Test;

import de.uni_freiburg.informatik.ultimate.logic.Rational;
import junit.framework.TestCase;

/**
 * Test Class for Rationals.
 * 
 * @author Jochen Hoenicke
 */
public final class RationalTest extends TestCase {
	
	final static BigInteger LARGE =
			new BigInteger("1234567890123456789012345678901234567890"); 
	final static Rational LARGE_RAT = Rational.valueOf(LARGE, BigInteger.ONE);
	static final Rational SMALL_RAT = Rational.valueOf(BigInteger.ONE,
			LARGE.divide(BigInteger.valueOf(7)));// NOCHECKSTYLE
	static final Rational RAT = LARGE_RAT.mul(SMALL_RAT);
	static final Rational MEDIUM1 = Rational.valueOf(Integer.MAX_VALUE, 1);
	static final Rational MEDIUM2 = Rational.valueOf(1, Integer.MAX_VALUE);
	static Rational MEDIUM3 = Rational.valueOf(0x789abcdf, 0x76543210);// NOCHECKSTYLE
	static final Rational SPECIAL1 = Rational.valueOf(
			BigInteger.ONE, BigInteger.valueOf(Integer.MIN_VALUE));
	static final Rational SPECIAL2 = Rational.valueOf(
			BigInteger.valueOf(Integer.MIN_VALUE), BigInteger.ONE);

	static final Rational[] RATIONALS = {
		Rational.ONE, Rational.MONE, Rational.ZERO,
		Rational.NAN, Rational.POSITIVE_INFINITY,
		Rational.NEGATIVE_INFINITY,
		LARGE_RAT, SMALL_RAT, RAT, MEDIUM1, MEDIUM2, MEDIUM3,
		SPECIAL1, SPECIAL2,
		LARGE_RAT.negate(), SMALL_RAT.negate(), RAT.negate(), 
		MEDIUM1.negate(), MEDIUM2.negate(), MEDIUM3.negate(),
		SPECIAL1.negate(), SPECIAL2.negate()
	};

	@Test
	public void testGCD() {
		assertEquals(0, Rational.gcd(0, 0));
		assertEquals(5, Rational.gcd(5, 0));// NOCHECKSTYLE
		assertEquals(5, Rational.gcd(0, 5));// NOCHECKSTYLE
		assertEquals(1, Rational.gcd(1, 5));// NOCHECKSTYLE
		assertEquals(1, Rational.gcd(5, 1));// NOCHECKSTYLE
		assertEquals(37, Rational.gcd(111, 37));// NOCHECKSTYLE
		assertEquals(10, Rational.gcd(150, 220));// NOCHECKSTYLE
		assertEquals(Integer.MAX_VALUE, Rational.gcd(Integer.MAX_VALUE,
				Integer.MAX_VALUE));
		assertEquals(1, Rational.gcd(Integer.MAX_VALUE, 720720));// NOCHECKSTYLE
		assertEquals(77, Rational.gcd(1309, 720720));// NOCHECKSTYLE
	}

	@Test
	public void testGCDlong() {
		assertEquals(0, Rational.gcd(0L, 0L));
		assertEquals(5, Rational.gcd(5L, 0L));// NOCHECKSTYLE
		assertEquals(5, Rational.gcd(0L, 5L));// NOCHECKSTYLE
		assertEquals(1, Rational.gcd(1L, 5L));// NOCHECKSTYLE
		assertEquals(1, Rational.gcd(5L, 1L));// NOCHECKSTYLE
		assertEquals(37, Rational.gcd(111L, 37L));// NOCHECKSTYLE
		assertEquals(10, Rational.gcd(150L, 220L));// NOCHECKSTYLE
		assertEquals(Long.MAX_VALUE, Rational.gcd(Long.MAX_VALUE,
				Long.MAX_VALUE));
		assertEquals(7, Rational.gcd(Long.MAX_VALUE, 720720L));// NOCHECKSTYLE
		assertEquals(1, Rational.gcd(Long.MAX_VALUE, Long.MAX_VALUE >> 1));
		assertEquals(77, Rational.gcd(1309l, 720720L));// NOCHECKSTYLE
	}

	@Test
	public void testValueOf() {
		assertSame(Rational.ZERO, Rational.valueOf(0, 5));// NOCHECKSTYLE
		assertSame(Rational.ONE, Rational.valueOf(5, 5));// NOCHECKSTYLE
		assertSame(Rational.MONE, Rational.valueOf(-5, 5));// NOCHECKSTYLE

		assertSame(Rational.ZERO, Rational.valueOf(0, Long.MAX_VALUE));
		assertSame(Rational.ONE, 
				Rational.valueOf(Long.MAX_VALUE, Long.MAX_VALUE));
		assertSame(Rational.MONE, 
				Rational.valueOf(-Long.MAX_VALUE, Long.MAX_VALUE));

		assertSame(Rational.POSITIVE_INFINITY, 
				Rational.valueOf(Long.MAX_VALUE, 0));
		assertSame(Rational.NEGATIVE_INFINITY, 
				Rational.valueOf(-Long.MAX_VALUE, 0));
		assertSame(Rational.NAN, Rational.valueOf(0, 0));

		assertEquals(Rational.valueOf(2, 1),
				Rational.valueOf(0x7fffffe, 0x3ffffffl));// NOCHECKSTYLE
		assertTrue(Rational.valueOf(1, -Long.MAX_VALUE).isNegative());
		assertTrue(!Rational.valueOf(1, Long.MAX_VALUE).isNegative());

		BigInteger large = new BigInteger(
				"1234567890123456789012345678901234567890");
		assertSame(Rational.ZERO, Rational.valueOf(
				BigInteger.ZERO,	BigInteger.ONE));
		assertSame(Rational.ZERO, Rational.valueOf(BigInteger.ZERO, large));
		assertSame(Rational.ONE, Rational.valueOf(large, large));
		assertSame(Rational.ONE, Rational.valueOf(
				large.negate(), large.negate()));
		assertSame(Rational.MONE, Rational.valueOf(large, large.negate()));
		assertSame(Rational.MONE, Rational.valueOf(large.negate(), large));
		assertSame(Rational.POSITIVE_INFINITY, Rational.valueOf(
				large, BigInteger.ZERO));
		assertSame(Rational.NEGATIVE_INFINITY, Rational.valueOf(
				large.negate(), BigInteger.ZERO));
		assertSame(Rational.NAN, Rational.valueOf(
				BigInteger.ZERO, BigInteger.ZERO));
	}

	@Test
	public void testAdd() {
		for (int i = 0; i < RATIONALS.length; i++) {
			for (int j = i + 1; j < RATIONALS.length; j++) {
				assertFalse(RATIONALS[i].equals(RATIONALS[j]));
				assertFalse(RATIONALS[j].equals(RATIONALS[i]));
			}
		}
		for (int i = 0; i < RATIONALS.length; i++) {
			assertSame("NAN + " + RATIONALS[i], Rational.NAN,
					Rational.NAN.add(RATIONALS[i]));
			assertSame(RATIONALS[i] + " + NAN", Rational.NAN,
					RATIONALS[i].add(Rational.NAN));
			if (RATIONALS[i] != Rational.NAN) {
				Rational expect = RATIONALS[i] == Rational.NEGATIVE_INFINITY
							? Rational.NAN : Rational.POSITIVE_INFINITY;
				assertSame(expect,
						RATIONALS[i].add(Rational.POSITIVE_INFINITY));
				assertSame(expect,
						Rational.POSITIVE_INFINITY.add(RATIONALS[i]));
				expect = RATIONALS[i] == Rational.POSITIVE_INFINITY
							? Rational.NAN : Rational.NEGATIVE_INFINITY;
				assertSame(expect,
						RATIONALS[i].add(Rational.NEGATIVE_INFINITY));
				assertSame(expect,
						Rational.NEGATIVE_INFINITY.add(RATIONALS[i]));
			}
		}
		
		for (int i = 0; i < RATIONALS.length; i++) {
			for (int j = i + 1; j < RATIONALS.length; j++) {
				assertEquals(RATIONALS[i].add(RATIONALS[j]),
						RATIONALS[j].add(RATIONALS[i]));
			}
		}
	}
	
	@Test
	public void testMul() {
		assertEquals(Rational.ZERO, Rational.POSITIVE_INFINITY.inverse());
		assertEquals(Rational.ZERO, Rational.NEGATIVE_INFINITY.inverse());
		assertEquals(Rational.POSITIVE_INFINITY, Rational.ZERO.inverse());
		assertEquals(Rational.NAN,
				Rational.ZERO.mul(Rational.POSITIVE_INFINITY));
		assertEquals(Rational.NAN,
				Rational.ZERO.mul(Rational.NEGATIVE_INFINITY));
		
		for (int i = 0; i < RATIONALS.length; i++) {
			if (RATIONALS[i] != Rational.ZERO
				&& !RATIONALS[i].denominator().equals(BigInteger.ZERO))
				assertEquals(Rational.ONE,
						RATIONALS[i].mul(RATIONALS[i].inverse()));
			for (int j = i + 1; j < RATIONALS.length; j++) {
				assertEquals(RATIONALS[i].mul(RATIONALS[j]),
						RATIONALS[j].mul(RATIONALS[i]));
				assertEquals(RATIONALS[i].mul(RATIONALS[j]).signum(),
						RATIONALS[i].signum() * RATIONALS[j].signum());
			}
		}
	}
	
	@Test
	public void testDiverse() {
		for (int i = 0; i < RATIONALS.length; i++) {
			assertEquals(0, RATIONALS[i].compareTo(RATIONALS[i]));
			for (int j = i + 1; j < RATIONALS.length; j++) {
				if (RATIONALS[i] != Rational.NAN
					&& RATIONALS[j] != Rational.NAN)
					assertTrue(RATIONALS[i] + " =<>= " + RATIONALS[j],
							RATIONALS[i].compareTo(RATIONALS[j]) != 0);
				assertEquals(RATIONALS[i] + " <=> " + RATIONALS[j],
						RATIONALS[i].compareTo(RATIONALS[j]),
						-RATIONALS[j].compareTo(RATIONALS[i]));
			}
		}
		for (int i = 0; i < RATIONALS.length; i++) {
			assertEquals(RATIONALS[i].isNegative(),
				     RATIONALS[i].compareTo(Rational.ZERO) < 0);
			assertEquals(RATIONALS[i].signum(),
				     RATIONALS[i].compareTo(Rational.ZERO));
			if (RATIONALS[i] != Rational.NEGATIVE_INFINITY)
				assertEquals(RATIONALS[i], RATIONALS[i].inverse().inverse());
			assertEquals(RATIONALS[i], RATIONALS[i].negate().negate());
			assertEquals(RATIONALS[i],
					RATIONALS[i].floor().add(RATIONALS[i].frac()));
			assertEquals(RATIONALS[i],
					RATIONALS[i].frac().add(RATIONALS[i].floor()));
			assertFalse(RATIONALS[i].frac().isNegative());
			assertTrue(RATIONALS[i].frac().compareTo(Rational.ONE) < 0);
			assertEquals(RATIONALS[i].isIntegral(),
					RATIONALS[i].frac() == Rational.ZERO);
		}
	}
}
