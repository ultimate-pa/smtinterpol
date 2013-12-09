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
package de.uni_freiburg.informatik.ultimate.smtinterpol.samples;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.logic.Logics;
import de.uni_freiburg.informatik.ultimate.logic.SMTLIBException;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.smtinterpol.smtlib2.SMTInterpol;

public final class UsageStub {
	
	private UsageStub() {
		// Hide constructor
	}

	public static void main(String[] args) {
		try {
			Script s = new SMTInterpol(Logger.getRootLogger(), true);
			s.setLogic(Logics.QF_LIA);
			s.declareFun("x", new Sort[0], s.sort("Int"));
			s.declareFun("y", new Sort[0], s.sort("Int"));
			s.assertTerm(s.term(">", s.term("x"), s.term("y")));
			s.assertTerm(s.term("=", s.term("x"), s.numeral("0")));
			s.assertTerm(s.term(">", s.term("y"), s.numeral("0")));
			switch (s.checkSat()) {
			case UNSAT:
				System.out.println("unsat");
				break;
			case SAT:
				System.out.println("sat");
				break;
			case UNKNOWN:
				System.out.println("unknown");
				break;
			default:
				throw new InternalError("WHAT????");
			}
		} catch (SMTLIBException ex) {
			System.out.println("unknown");
			ex.printStackTrace(System.err);
		}
	}
	
}
