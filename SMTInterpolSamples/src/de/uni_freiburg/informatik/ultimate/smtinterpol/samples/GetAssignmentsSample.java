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

import java.util.HashSet;

import de.uni_freiburg.informatik.ultimate.logic.Annotation;
import de.uni_freiburg.informatik.ultimate.logic.Assignments;
import de.uni_freiburg.informatik.ultimate.logic.SMTLIBException;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.smtinterpol.DefaultLogger;
import de.uni_freiburg.informatik.ultimate.smtinterpol.smtlib2.SMTInterpol;

public final class GetAssignmentsSample {

	private GetAssignmentsSample() {
		// Hide constructor
	}

	public static void main(String[] ignored) {
		try {
			// Create a new interaction script
			final Script script = new SMTInterpol(new DefaultLogger());
			// Enable production of assignments for Boolean named terms
			script.setOption(":produce-assignments", true);

			script.setLogic("QF_UF");
			declareStuff(script);
			// Build the formula (f(x) == f(y) /\ x == y) \/ x != y
			// Name every literal in the formula
			final Term x = script.term("x");
			final Term y = script.term("y");
			final Term fx = script.term("f", x);
			final Term fy = script.term("f", y);
			final Term xeqy = script.term("=", x, y);
			final Term fxeqfy = script.term("=", fx, fy);
			final Term namedxeqy =
				script.annotate(xeqy, new Annotation(":named", "xeqy"));
			final Term namedxneqy =
				script.annotate(script.term("not", xeqy),
						new Annotation(":named", "xneqy"));
			final Term namedfxeqfy =
				script.annotate(fxeqfy, new Annotation(":named", "fxeqfy"));
			final Term conj = script.term("and", namedfxeqfy, namedxeqy);
			final Term disj = script.term("or", conj, namedxneqy);
			script.assertTerm(disj);
			LBool res = script.checkSat();
			if (res != LBool.SAT) {
				System.err.println("Bug in SMTInterpol: Formula is " + res);
				System.exit(2);
			}
			Assignments ass = script.getAssignment();
			final boolean isXEqY = ass.getAssignment("xeqy");
			final boolean isXNeqY = ass.getAssignment("xneqy");
			if (isXEqY == isXNeqY) {
				System.err.println(
						"Bug in SMTInterpol: x is equal to y and unequal at the same time!");// NOCHECKSTYLE
				System.exit(2);
			}
			Term clause;
			// Produce the smallest possible clause that excludes this
			// assignment
			if (ass.getNumTrueAssignments() <= ass.getNumFalseAssignments()) {
				// === BLOCKING CLAUSE ===
				// Negate all labels that are assigned true in the current model
				System.err.println("Blocking clause");
				final HashSet<Term> satLabels = new HashSet<Term>();
				for (final String label : ass.getTrueAssignments()) {
					satLabels.add(script.term("not", script.term(label)));
				}
				// Guard against 1-ary "or"
				clause = satLabels.size() == 1 ? satLabels.iterator().next()
					: script.term("or",
						satLabels.toArray(new Term[satLabels.size()]));
			} else {
				// === ENABLING CLAUSE ===
				// Add all labels that are assigned false in the current model
				System.err.println("Enabling clause");
				final HashSet<Term> unsatLabels = new HashSet<Term>();
				for (final String label : ass.getFalseAssignments()) {
					unsatLabels.add(script.term(label));
				}
				// Guard against 1-ary "or"
				clause = unsatLabels.size() == 1
						? unsatLabels.iterator().next() : script.term("or",
							unsatLabels.toArray(new Term[unsatLabels.size()]));
			}
			// Push one level onto the assertion stack
			script.push(1);
			// Assert that at least one label has to change
			script.assertTerm(clause);
			res = script.checkSat();
			if (res != LBool.SAT) {
				System.err.println("Bug in SMTInterpol: 2nd Formula is " + res);
				System.exit(2);
			}
			// Repeat since we are sat
			ass = script.getAssignment();
			// Produce the smallest possible clause that excludes this
			// assignment
			if (ass.getNumTrueAssignments() <= ass.getNumFalseAssignments()) {
				// === BLOCKING CLAUSE ===
				// Negate all labels that are assigned true in the current model
				System.err.println("Blocking clause");
				final HashSet<Term> satLabels = new HashSet<Term>();
				for (final String label : ass.getTrueAssignments()) {
					satLabels.add(script.term("not", script.term(label)));
				}
				// Guard against 1-ary "or"
				clause = satLabels.size() == 1 ? satLabels.iterator().next()
					: script.term("or",
						satLabels.toArray(new Term[satLabels.size()]));
			} else {
				// === ENABLING CLAUSE ===
				// Add all labels that are assigned false in the current model.
				System.err.println("Enabling clause");
				final HashSet<Term> unsatLabels = new HashSet<Term>();
				for (final String label : ass.getFalseAssignments()) {
					unsatLabels.add(script.term(label));
				}
				// Guard against 1-ary "or"
				clause = unsatLabels.size() == 1
					? unsatLabels.iterator().next()
						: script.term("or",
							unsatLabels.toArray(new Term[unsatLabels.size()]));
			}
			script.push(1);
			script.assertTerm(clause);
			res = script.checkSat();
			if (res != LBool.UNSAT) {
				System.err.println("Bug in SMTInterpol: 3rd Formula is " + res);
				System.exit(2);
			}
			// Go back to a satisfiable state
			script.pop(2);
			res = script.checkSat();
			System.out.println("Original formula was " + res);
			System.out.println(
					"I found two different models for the boolean part");
			script.exit();
		} catch (final SMTLIBException exc) {
			exc.printStackTrace(System.err);
			System.exit(1);
		}
	}

	private static void declareStuff(Script script) throws SMTLIBException {
		// 0-ary sort U is the only sort we use
		script.declareSort("U", 0);
		// Variables: x, y of type U; f of type U->U
		final Sort[] empty = {};
		final Sort U = script.sort("U");
		script.declareFun("x", empty, U);
		script.declareFun("y", empty, U);
		script.declareFun("f", new Sort[]{ U }, U);
	}
}
