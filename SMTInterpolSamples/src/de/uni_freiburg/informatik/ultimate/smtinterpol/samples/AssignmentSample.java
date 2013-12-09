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
package de.uni_freiburg.informatik.ultimate.smtinterpol.samples;

import java.util.HashSet;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.logic.Annotation;
import de.uni_freiburg.informatik.ultimate.logic.Assignments;
import de.uni_freiburg.informatik.ultimate.logic.Logics;
import de.uni_freiburg.informatik.ultimate.logic.SMTLIBException;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.smtinterpol.smtlib2.SMTInterpol;

public final class AssignmentSample {
	private AssignmentSample() {
		// Hide constructor
	}
	public static void main(String[] ignored) {
		try {
			// Create a new interaction script
			Script script = new SMTInterpol(Logger.getRootLogger());
			// Enable production of assignments for Boolean named terms
			script.setOption(":produce-assignments", true);
			
			script.setLogic(Logics.QF_UF);
			declareStuff(script);
			// Build the formula (f(x) == f(y) /\ x == y) \/ x != y
			// Name every literal in the formula
			Term x = script.term("x");
			Term y = script.term("y");
			Term fx = script.term("f", x);
			Term fy = script.term("f", y);
			Term xeqy = script.term("=", x, y);
			Term fxeqfy = script.term("=", fx, fy);
			Term namedxeqy =
				script.annotate(xeqy, new Annotation(":named", "xeqy"));
			Term namedxneqy =
				script.annotate(script.term("not", xeqy), 
						new Annotation(":named", "xneqy"));
			Term namedfxeqfy =
				script.annotate(fxeqfy, new Annotation(":named", "fxeqfy"));
			Term conj = script.term("and", namedfxeqfy, namedxeqy);
			Term disj = script.term("or", conj, namedxneqy);
			script.assertTerm(disj);
			LBool res = script.checkSat();
			if (res != LBool.SAT) {
				System.err.println("Bug in SMTInterpol: Formula is " + res);
				System.exit(2);
			}
			Assignments ass = script.getAssignment();
			boolean isXEqY = ass.getAssignment("xeqy");
			boolean isXNeqY = ass.getAssignment("xneqy");
			if (isXEqY == isXNeqY) {
				System.err.println(
						"Bug in SMTInterpol: x is equal to y and unequal at the same time!");// NOCHECKSTYLE
				System.exit(2);
			}
			Term clause = modelBlocker(script);
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
			clause = modelBlocker(script);
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
					"I found two different models for the Boolean abstraction");
			script.exit();
		} catch (SMTLIBException exc) {
			exc.printStackTrace(System.err);
			System.exit(1);
		}
	}
	
	private static Term blockingClause(Script script, Assignments ass) {
		// Negate all labels that are assigned true in the current model.
		System.err.println("Blocking clause");
		HashSet<Term> satLabels = new HashSet<Term>();
		for (String label : ass.getTrueAssignments())
			satLabels.add(script.term("not", script.term(label)));
		// Guard against 1-ary "or"
		return satLabels.size() == 1 ? satLabels.iterator().next()
				: script.term("or",
						satLabels.toArray(new Term[satLabels.size()]));
	}
	
	private static Term enablingClause(Script script, Assignments ass) {
		// Add all labels that are assigned false in the current model.
		System.err.println("Enabling clause");
		HashSet<Term> unsatLabels = new HashSet<Term>();
		for (String label : ass.getFalseAssignments())
			unsatLabels.add(script.term(label));
		// Guard against 1-ary "or"
		return unsatLabels.size() == 1 ? unsatLabels.iterator().next()
				: script.term("or", 
					unsatLabels.toArray(new Term[unsatLabels.size()]));
	}

	// Produce the smallest possible clause that excludes this assignment.
	private static Term modelBlocker(Script script) {
		Assignments ass = script.getAssignment();
		return ass.getNumTrueAssignments() <= ass.getNumFalseAssignments()
				? blockingClause(script, ass) : enablingClause(script, ass);
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
	}
}
