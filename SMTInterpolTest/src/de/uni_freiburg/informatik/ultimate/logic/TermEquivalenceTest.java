/*
 * Copyright (C) 2012-2013 University of Freiburg
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

import de.uni_freiburg.informatik.ultimate.logic.Logics;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermEquivalence;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.logic.Theory;
import junit.framework.TestCase;

public class TermEquivalenceTest extends TestCase {
	
	@Test
	public void testEq() {
		Theory theory = new Theory(Logics.AUFLIRA);
		// (let ((x y)) (forall ((y Int)) (>= y x)))
		// (let ((z y)) (forall ((w Int)) (>= w z)))
		Sort intSort = theory.getNumericSort();
		TermVariable x = theory.createTermVariable("x", intSort);
		TermVariable y = theory.createTermVariable("y", intSort);
		TermVariable z = theory.createTermVariable("z", intSort);
		TermVariable w = theory.createTermVariable("w", intSort);
		Term lhs = theory.let(x, y, 
				theory.forall(new TermVariable[]{y}, theory.term(">=", y, x)));
		Term rhs = theory.let(z, y, 
				theory.forall(new TermVariable[]{w}, theory.term(">=", w, z)));
		assertTrue(new TermEquivalence().equal(lhs, rhs));
	}
}
