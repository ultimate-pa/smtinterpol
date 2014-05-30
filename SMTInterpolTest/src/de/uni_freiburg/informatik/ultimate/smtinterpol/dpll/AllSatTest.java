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
package de.uni_freiburg.informatik.ultimate.smtinterpol.dpll;

import java.math.BigInteger;

import org.apache.log4j.Logger;
import org.junit.Assert;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.JUnit4;

import de.uni_freiburg.informatik.ultimate.logic.Logics;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.smtinterpol.smtlib2.SMTInterpol;
import de.uni_freiburg.informatik.ultimate.smtinterpol.util.TestCaseWithLogger;

@RunWith(JUnit4.class)
public class AllSatTest extends TestCaseWithLogger {

	@Test
	public void testAllSat() {
		SMTInterpol solver = new SMTInterpol(Logger.getRootLogger());
		solver.setOption(":verbosity", 10);
		solver.setLogic(Logics.QF_LIA);
		Sort[] empty = new Sort[0];
		Sort intSort = solver.sort("Int");
		solver.declareFun("x", empty, intSort);
		solver.declareFun("y", empty, intSort);
		Term zero = solver.numeral(BigInteger.ZERO);
		solver.assertTerm(solver.term(">=", 
				solver.term("+", solver.term("x"), solver.term("y")),
			zero));
		Term[] important = new Term[] {
				solver.term("<", solver.term("x"), zero),
				solver.term("<", solver.term("y"), zero),
				solver.term("=",
						solver.term("*",
								solver.numeral(BigInteger.valueOf(2)),
								solver.term("x")),
						solver.numeral(BigInteger.ONE)),
				solver.term("=", solver.term("x"), solver.term("x"))
		};
		int cnt = 0;
		for (Term[] minterm : solver.checkAllsat(important)) {
			System.err.println("Found minterm:");
			for (Term t : minterm)
				System.err.println(t);
			++cnt;
		}
		Assert.assertEquals(3, cnt);// NOCHECKSTYLE
	}
	
}
