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

import de.uni_freiburg.informatik.ultimate.logic.Annotation;
import de.uni_freiburg.informatik.ultimate.logic.Assignments;
import de.uni_freiburg.informatik.ultimate.logic.Logics;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.smtinterpol.smtlib2.SMTInterpol;

public final class FlipDecisions {
	
	private FlipDecisions() {
		// Hide constructor
	}
	
	private static final boolean FLIP_ALL = false;
	
	public static void main(String[] unused) throws Exception {
		Script script = new SMTInterpol(Logger.getRootLogger(), true);
		script.setOption(":produce-assignments", true);
		script.setOption(":verbosity", 2);
		script.setLogic(Logics.QF_UF);
		Sort[] empty = {};
		Sort bool = script.sort("Bool");
		script.declareFun("P", empty, bool);
		script.declareFun("Q", empty, bool);
		// (assert (or P Q))
		script.assertTerm(script.term("or", 
				script.annotate(script.term("P"),
						new Annotation(":named", "Pname")),
				script.annotate(script.term("Q"),
						new Annotation(":named", "Qname"))));
		LBool sat = script.checkSat();
		if (sat != LBool.SAT) {
			System.err.println("Error!!!");
			System.exit(-1);
		}
		Assignments ass = script.getAssignment();
		System.err.println("P is " + ass.getAssignment("Pname"));
		System.err.println("Q is " + ass.getAssignment("Qname"));
		if (FLIP_ALL)
			((SMTInterpol) script).flipDecisions();
		else {
			((SMTInterpol) script).flipNamedLiteral(
					Math.random() >= 0.5 ? "Qname" : "Pname");// NOCHECKSTYLE
		}
		sat = script.checkSat();
		if (sat != LBool.SAT) {
			System.err.println("Error!!!");
			System.exit(-1);
		}
		ass = script.getAssignment();
		System.err.println("P is " + ass.getAssignment("Pname"));
		System.err.println("Q is " + ass.getAssignment("Qname"));
		script.exit();
	}
}
