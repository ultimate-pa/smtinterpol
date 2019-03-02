/*
 * Copyright (C) 2014 University of Freiburg
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

import org.apache.log4j.Logger;
import org.apache.log4j.SimpleLayout;
import org.apache.log4j.WriterAppender;

import de.uni_freiburg.informatik.ultimate.logic.Logics;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.smtinterpol.samples.util.Log4jProxy;
import de.uni_freiburg.informatik.ultimate.smtinterpol.smtlib2.SMTInterpol;

/**
 * This sample demonstrates how to instantiate the LogProxy interface for log4j.
 * @author Juergen Christ
 */
public final class LogProxySample {

	private LogProxySample() {
		// Hide constructor
	}

	public static void main(String[] unused) {
		// Set up Log4j
		final Logger logger = Logger.getLogger(LogProxySample.class);
		logger.addAppender(new WriterAppender(new SimpleLayout(), System.err));

		// Create and set up the solver
		final SMTInterpol solver = new SMTInterpol(new Log4jProxy(logger));
		solver.setOption(":verbosity", BigInteger.valueOf(5));
		solver.setLogic(Logics.QF_LIA);

		// Just a simple usage to produce some logging
		final Sort intSort = solver.sort("Int");
		final Sort[] empty = new Sort[0];
		solver.declareFun("x", empty, intSort);
		solver.declareFun("y", empty, intSort);
		solver.declareFun("z", empty, intSort);
		solver.assertTerm(solver.term("=",
				solver.term("*",
						solver.numeral(BigInteger.valueOf(2)),
						solver.term("x")),
					solver.term("z")));
		solver.checkSat();
		solver.assertTerm(solver.term("=",
				solver.term("+", solver.term("*",
						solver.numeral(BigInteger.valueOf(2)),
						solver.term("y")), solver.numeral(BigInteger.ONE)),
					solver.term("z")));
		solver.checkSat();
		solver.exit();
	}

}
