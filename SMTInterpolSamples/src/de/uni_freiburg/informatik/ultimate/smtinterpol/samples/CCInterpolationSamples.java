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

import java.math.BigInteger;
import java.util.Arrays;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.logic.Annotation;
import de.uni_freiburg.informatik.ultimate.logic.Logics;
import de.uni_freiburg.informatik.ultimate.logic.SMTLIBException;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.smtinterpol.smtlib2.SMTInterpol;

public final class CCInterpolationSamples {
	
	private CCInterpolationSamples() {
		// Hide constructor
	}
	
	private static final void bailout(SMTLIBException se) {
		se.printStackTrace(System.err);
		System.exit(1);
	}
	
	public static void main(String[] ignored) {
		try {
			// Create a new Benchmark to interact with SMTInterpol
			Script script = new SMTInterpol(Logger.getRootLogger(), true);
			// Enable proof production (needed for interpolation)
			script.setOption(":produce-proofs", true);
			// Don't be too verbose
			BigInteger verbosity = (BigInteger) script.getOption(":verbosity");
			script.setOption(":verbosity", verbosity.subtract(BigInteger.ONE));
			script.setLogic(Logics.QF_UF);
			script.declareSort("U", 0);
			Sort U = script.sort("U");
			Sort[] empty = new Sort[0];
			script.push(1);
			script.declareFun("a", empty, U);
			script.declareFun("b", empty, U);
			script.declareFun("ab1", empty, U);
			script.declareFun("ab2", empty, U);
			Term termA = script.term("and",
					script.term("=", script.term("a"), script.term("ab1")),
					script.term("=", script.term("a"), script.term("ab2")));
			// Naming termA as A lets us use this term in the interpolation
			Term A = script.annotate(termA, new Annotation(":named", "A"));
			Term termB = script.term("and",
					script.term("=", script.term("b"), script.term("ab1")),
					script.term("distinct", script.term("b"),
							script.term("ab2")));
			// Naming termB as B lets us use this term in the interpolation
			Term B = script.annotate(termB, new Annotation(":named", "B"));
			script.assertTerm(A);
			script.assertTerm(B);
			LBool isSat = script.checkSat();
			if (isSat == LBool.UNSAT) {
				// Compute interpolant between A and B
				Term[] partitions = new Term[] {
					script.term("A"),
					script.term("B")
				};
				Term[] interpolants = script.getInterpolants(partitions);
				System.out.println("Got Interpolants:");
				System.out.println(Arrays.toString(interpolants));
			} else {
				System.err.println("Strange bug in SMTInterpol.");
				System.err.println(
						"Sat-check on unsat formula yielded " + isSat);
				System.exit(2);
			}
			script.pop(1);
		} catch (SMTLIBException exc) {
			bailout(exc);
		}
	}
}
