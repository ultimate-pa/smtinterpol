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
package de.uni_freiburg.informatik.ultimate.smtinterpol;

import de.uni_freiburg.informatik.ultimate.logic.Script;

/**
 * Generic interface for the different parsers of SMTInterpol.  Each interface
 * (SMTLIB, SMTLIB 2, DIMACS,...) should provide an implementation of this
 * interface to be used by the generic main method.
 * @author Juergen Christ
 */
public interface IParser {
	/**
	 * Parse a specific file. If the filename is <code>null</code>, the
	 * parser should parse standard input.  The last four arguments are options
	 * to be set by the parser.  The options correspond to the SMTLIB options
	 * with the corresponding name.  If one of the options is <code>null</code>,
	 * the option should not be set.  The script is responsible for proper
	 * conversion of the String to the desired type.  If the script to use is
	 * <code>null</code>, a default instance of SMTInterpol should be used.
	 * This default behaviour allows different parser implementations to fine
	 * tune the behaviour of the solver.  For example, the SMTLIB 2 parser can
	 * set up a logger that can actually be configured to log to different
	 * destinations.  But this is only possible if the parser can controll the
	 * logger directly which is not the case for scripts created before the
	 * parser is created.
	 * @param script       The script that should be used or <code>null</code>.
	 * @param filename     The name of the file to parse.
	 * @param printSuccess Should success messages be printed.
	 * @param verbosity    Verbosity level of the solver.
	 * @param timeout      Timeout for the solver.
	 * @param randomSeed   Random seed for the solver.
	 * @return Exit code.
	 */
	public int run(Script script, String filename, boolean printSucces,
			String verbosity, String timeout, String randomSeed);
}
