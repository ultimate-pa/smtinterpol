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

import java.io.StringReader;

import de.uni_freiburg.informatik.ultimate.logic.Logics;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.smtinterpol.DefaultLogger;
import de.uni_freiburg.informatik.ultimate.smtinterpol.option.OptionMap;
import de.uni_freiburg.informatik.ultimate.smtinterpol.smtlib2.ParseEnvironment;
import de.uni_freiburg.informatik.ultimate.smtinterpol.smtlib2.SMTInterpol;

/**
 * This sample demonstrates the computation of tree interpolants for the famous
 * McCarthy 91 function using SMTInterpol.  This sample is the API version of
 * the input script <tt>mccarthy.smt2</tt>.
 * @author Juergen Christ
 */
public final class TreeInterpolationSample {
	
	private TreeInterpolationSample() {
		// Hide constructor
	}
	
	public static void main(String[] unused) {
		// Create a logging proxy
		DefaultLogger logger = new DefaultLogger();
		// Create an option map to handle all API options.
		OptionMap options = new OptionMap(logger, true);
		// Create a new solver
		Script solver = new SMTInterpol(options);
		// Enable interpolant production
		solver.setOption(":produce-interpolants", Boolean.TRUE);
		// A parse environment to read from strings.  This is a front end and
		// thus needs front end options.
		ParseEnvironment pe = new ParseEnvironment(solver, options);
		// Disable success messages
		solver.setOption(":print-success", Boolean.FALSE);
		solver.setLogic(Logics.QF_LIA);
		// Declare some function symbols
		pe.parseStream(new StringReader("(declare-fun x_1 () Int)"), "x_1");
		pe.parseStream(new StringReader("(declare-fun xm1 () Int)"), "xm1");
		pe.parseStream(new StringReader("(declare-fun x2 () Int)"), "x2");
		pe.parseStream(new StringReader("(declare-fun res4 () Int)"), "res4");
		// Symbols above will be used in a second query.
		solver.push(1);
		pe.parseStream(new StringReader("(declare-fun resm5 () Int)"), "resm5");
		pe.parseStream(new StringReader("(declare-fun xm6 () Int)"), "xm6");
		pe.parseStream(new StringReader("(declare-fun x7 () Int)"), "x7");
		pe.parseStream(new StringReader("(declare-fun res9 () Int)"), "res9");
		pe.parseStream(new StringReader("(declare-fun resm10 () Int)"), 
				"resm10");
		pe.parseStream(new StringReader("(declare-fun res11 () Int)"), "res11");
		// Assert all formulas.
		pe.parseStream(new StringReader(
				"(assert (! (<= x_1 100) :named M1))"), "M1");
		pe.parseStream(new StringReader(
				"(assert (! (= xm1 (+ x_1 11)) :named M2))"), "M2");
		pe.parseStream(new StringReader(
				"(assert (! (> x2 100) :named S11))"), "S11");
		pe.parseStream(new StringReader(
				"(assert (! (= res4 (- x2 10)) :named S12))"), "S12");
		pe.parseStream(new StringReader(
				"(assert (! (and (= x2 xm1) (= resm5 res4)) :named S1RET))"),
				"S1RET");
		pe.parseStream(new StringReader(
				"(assert (! (= xm6 resm5) :named M3))"), "M3");
		pe.parseStream(new StringReader(
				"(assert (! (> x7 100) :named S21))"), "S21");
		pe.parseStream(new StringReader(
				"(assert (! (= res9 (- x7 10)) :named S22))"), "S22");
		pe.parseStream(new StringReader(
				"(assert (! (and (= x7 xm6) (= resm10 res9)) :named S2RET))"),
				"S2RET");
		pe.parseStream(new StringReader(
				"(assert (! (= res11 resm10) :named M4))"), "M4");
		pe.parseStream(new StringReader(
			  	"(assert (! (and (<= x_1 101) (distinct res11 91)) :named ERR))"
		), "ERR");
		// Check for unsatisfiability
		LBool isSat = solver.checkSat();
		if (isSat != LBool.UNSAT) {
			System.err.println("ERROR: Formula should be unsat!");
			System.exit(1);
		}
		// Build up the formula tree
		Term[] partition = new Term[] {
				solver.term("M1"),
				solver.term("M2"),
				solver.term("S11"),
				solver.term("S12"),
				solver.term("S1RET"),
				solver.term("M3"),
				solver.term("S21"),
				solver.term("S22"),
				solver.term("S2RET"),
				solver.term("M4"),
				solver.term("ERR")
		};
		// corresponding SMTLIB notation:
		// (get-interpolants M1 M2 (S11 S12) S1RET M3 (S21 S22) S2RET M4 ERR)
		// S11 and S12 are in the same subtree.  The first element of this
		// subtree occurs at position 2 in the term array.
		// Similarly, S21 and S22 are in the same subtree which starts at
		// position 6.
		Term[] interpolants = solver.getInterpolants(partition, new int[] {
			0, 0, 2, 2, 0, 0, 6, 6, 0, 0, 0	// NOCHECKSTYLE
		});
		// Print the interpolants
		for (int i = 0; i < interpolants.length; ++i) {
			System.out.print(partition[i]);
			System.out.print(" is annotated with interpolant ");
			System.out.println(interpolants[i]);
		}
		// We omit the interpolant of the root.
		System.out.print(partition[interpolants.length]);
		System.out.println(" is annotated with interpolant false");
		// Prepare second call
		solver.pop(1);
		solver.push(1);
		// We don't need to assert since all needed symbols survived.
		pe.parseStream(new StringReader(
				"(assert (! (<= x_1 100) :named M1))"), "M1");
		pe.parseStream(new StringReader(
				"(assert (! (= xm1 (+ x_1 11)) :named M2))"), "M2");
		pe.parseStream(new StringReader(
				"(assert (! (= x2 xm1) :named CALL))"), "CALL");
		pe.parseStream(new StringReader(
				"(assert (! (> x2 100) :named S1))"), "S1");
		pe.parseStream(new StringReader(
				"(assert (! (= res4 (- x2 10)) :named S2))"), "S2");
		pe.parseStream(new StringReader(
				"(assert (! (and (<= x2 101) (distinct res4 91)) :named ERR))"),
				"ERR");
		// Check for unsatisfiability
		isSat = solver.checkSat();
		if (isSat != LBool.UNSAT) {
			System.err.println("ERROR: Formula should be unsat!");
			System.exit(1);
		}
		// Second call:
		// (get-interpolants M1 M2 CALL S1 S2 ERR)
		// This is a non-tree version.  We can simply use the non-tree API call.
		partition = new Term[] {
				solver.term("M1"),
				solver.term("M2"),
				solver.term("CALL"),
				solver.term("S1"),
				solver.term("S2"),
				solver.term("ERR")
		};
		interpolants = solver.getInterpolants(partition);
		// Print the interpolants
		for (int i = 0; i < interpolants.length; ++i) {
			System.out.print(partition[i]);
			System.out.print(" is annotated with interpolant ");
			System.out.println(interpolants[i]);
		}
		// We omit the interpolant of the root.
		System.out.print(partition[interpolants.length]);
		System.out.println(" is annotated with interpolant false");
		// Cleanup and exit
		solver.pop(1);
		solver.exit();
	}
}
