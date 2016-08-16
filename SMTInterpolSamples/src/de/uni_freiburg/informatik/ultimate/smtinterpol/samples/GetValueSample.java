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

import java.util.Map;

import de.uni_freiburg.informatik.ultimate.logic.Logics;
import de.uni_freiburg.informatik.ultimate.logic.SMTLIBException;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.smtinterpol.DefaultLogger;
import de.uni_freiburg.informatik.ultimate.smtinterpol.smtlib2.SMTInterpol;

public final class GetValueSample {
	
	private GetValueSample() {
		// Hide constructor
	}
	
	public static void main(String[] ignored) {
		try {
			// Create a new interaction script
			Script script = new SMTInterpol(new DefaultLogger());
			// Enable production of a model
			script.setOption(":produce-models", true);
			
			script.setLogic(Logics.QF_UFLIA);
			declareStuff(script);
			// Build the formula f(x) == f(y) /\ i > j
			Term x = script.term("x");
			Term y = script.term("y");
			Term fx = script.term("f", x);
			Term fy = script.term("f", y);
			Term i = script.term("i");
			Term j = script.term("j");
			Term ufterm = script.term("=", fx, fy);
			Term laterm = script.term(">", i, j);
			Term conj = script.term("and", ufterm, laterm);
			script.assertTerm(conj);
			LBool res = script.checkSat();
			if (res != LBool.SAT) {
				System.err.println("Bug in SMTInterpol: Result is " + res);
				System.exit(2);
			}
			Term[] valterms = { x, y, fx, fy, i, j };
			Map<Term, Term> val = script.getValue(valterms);
			for (Term t : valterms)
				System.out.println("Value for term " + t + " is " + val.get(t));
			script.exit();
		} catch (SMTLIBException exc) {
			exc.printStackTrace(System.err);
			System.exit(1);
		}
	}
			
	private static void declareStuff(Script script) throws SMTLIBException {
		// 0-ary sort U is the only sort we use
		script.declareSort("U", 0);
		// Variables: x, y of type U; f of type U->U
		Sort[] empty = {};
		Sort U = script.sort("U");
		script.declareFun("x", empty, U);
		script.declareFun("y", empty, U);
		script.declareFun("f", new Sort[]{ U }, U);
		Sort intSort = script.sort("Int");
		script.declareFun("i", empty, intSort);
		script.declareFun("j", empty, intSort);
	}
}
