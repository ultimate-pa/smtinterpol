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

import org.junit.Test;

import de.uni_freiburg.informatik.ultimate.logic.MutableRational;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import junit.framework.TestCase;

/**
 * Test Class for Rationals.
 * 
 * @author Jochen Hoenicke
 */
public final class MutableRationalTest extends TestCase {
	Rational[] mRationals = RationalTest.RATIONALS;

	@Test
	public void testAdd() {
		for (int i = 0; i < mRationals.length; i++) {
			for (int j = 0; j < mRationals.length; j++) {
				MutableRational r1 = new MutableRational(mRationals[i]);
				assertSame(r1, r1.add(mRationals[j]));
				assertEquals(mRationals[i] + " + " + mRationals[j],
						mRationals[i].add(mRationals[j]), r1.toRational());
			}
		}
	}
	
	@Test
	public void testMul() {
		for (int i = 0; i < mRationals.length; i++) {
			for (int j = 0; j < mRationals.length; j++) {
				MutableRational r1 = new MutableRational(mRationals[i]);
				assertSame(r1, r1.mul(mRationals[j]));
				assertEquals(mRationals[i] + " * " + mRationals[j],
						mRationals[i].mul(mRationals[j]), r1.toRational());
			}
		}
	}
	
	@Test
	public void testDiverse() {
		for (int i = 0; i < mRationals.length; i++) {
			MutableRational r1 = new MutableRational(mRationals[i]);
			assertSame(r1, r1.inverse());
			assertEquals(mRationals[i] + ".inverse()",
					mRationals[i].inverse(), r1.toRational());
			r1 = new MutableRational(mRationals[i]);
			assertSame(r1, r1.negate());
			assertEquals(mRationals[i] + ".negate()",
					mRationals[i].negate(), r1.toRational());
			r1 = new MutableRational(mRationals[i]);
			assertEquals(mRationals[i] + ".isIntegral()",
					mRationals[i].isIntegral(), r1.isIntegral());
			assertEquals(mRationals[i] + ".isNegative()",
					mRationals[i].isNegative(), r1.isNegative());
			for (int j = 0; j < mRationals.length; j++) {
				MutableRational r2 = new MutableRational(mRationals[j]);
				assertEquals(mRationals[i] + " <=> " + mRationals[j],
						mRationals[i].compareTo(mRationals[j]),
						r1.compareTo(r2));
			}
		}
	}
}
