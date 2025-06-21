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

import de.uni_freiburg.informatik.ultimate.logic.Model;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.smtinterpol.DefaultLogger;
import de.uni_freiburg.informatik.ultimate.smtinterpol.smtlib2.SMTInterpol;

/**
 * A sample to show the model production capabilities of SMTInterpol.  This
 * sample simulates the quantifier checking of the following conjunction:
 * (distinct c1 c2)
 * (distinct s1 s2)
 * (distinct v s1)
 * (distinct v s2)
 * (forall ((x U)) (or (= x c1) (= x c2)))                                   (1)
 * @author Juergen Christ
 */
public final class ModelSample {

	private ModelSample() {
		// Hide constructor
	}

	private static Term getSkolem(Script script, Sort sort, int num) {
		final String name = "sk_x" + num;
		script.declareFun(name, new Sort[0], sort);
		return script.term(name);
	}

	public static void main(String[] ignored) {
		// Counter for the skolem instances
		int numskolem = 0;
		// Let SMTInterpol set up the logger for us
		final Script script = new SMTInterpol(new DefaultLogger());
		// Enable model production
		script.setOption(":produce-models", true);
		script.setOption(":verbosity", 1);
		script.setLogic("QF_UF");
		// Declare sort U
		script.declareSort("U", 0);
		final Sort u = script.sort("U");
		// Declare constants
		final Sort[] emptySortArray = new Sort[0];
		script.declareFun("c1", emptySortArray, u);
		script.declareFun("c2", emptySortArray, u);
		script.declareFun("s1", emptySortArray, u);
		script.declareFun("s2", emptySortArray, u);
		script.declareFun("v", emptySortArray, u);
		// Prepare test term
		final TermVariable x = script.variable("x", u);
		final TermVariable[] var = {x};
		final Term testStub = script.term("or",
				script.term("=", script.term("c1"), x),
				script.term("=", script.term("c2"), x));
		// Possible Boolean result
		final Term falseTerm = script.term("false");
		// Assert formulas
		script.assertTerm(script.term("distinct", script.term("c1"),
				script.term("c2")));
		script.assertTerm(script.term("distinct", script.term("s1"),
				script.term("s2")));
		script.assertTerm(script.term("distinct", script.term("v"),
				script.term("s1")));
		script.assertTerm(script.term("distinct", script.term("v"),
				script.term("s2")));
//		script.assertTerm(script.term("distinct", script.term("s1"),
//				script.term("s2"), script.term("v")));
		// Refinement loop
		while (true) {
			final LBool isSat = script.checkSat();
			if (isSat == LBool.UNSAT) {
				System.out.println("Formula is unsat");
				return;
			}
			final Model model = script.getModel();
			final Term skolem = getSkolem(script, u, numskolem++);
			final Term test = script.let(var, new Term[] {skolem},
					script.term("not", testStub));
			final Term evalTest1 = model.evaluate(test);
			if (evalTest1 == falseTerm) {
				System.out.println("Using solver to check model");
				final Term sortConstraint = null;//model.constrainBySort(skolem);
				script.push(1);
				script.assertTerm(test);
				script.assertTerm(sortConstraint);
				final LBool mbqitest = script.checkSat();
				if (mbqitest == LBool.UNSAT) {
					// Recreate the model.
					script.pop(1);
					final LBool tmp = script.checkSat();
					assert tmp == LBool.SAT;
					break;
				}
				final Model mbqimodel = script.getModel();
				final Term valx = mbqimodel.evaluate(skolem);
				System.out.println("Instantiation: x <- " + valx);
				script.pop(1);
				script.assertTerm(script.let(var, new Term[] {valx}, testStub));
			} else {
				// We get a new instantiation for (1)
				final Term valx = model.evaluate(skolem);
				System.out.println("Instantiation: x <- " + valx);
				script.assertTerm(script.let(var, new Term[] {valx}, testStub));
			}
		}
		System.out.println("Formula is satisfiable with model:");
		System.out.println(script.getModel());
	}
}
