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
package de.uni_freiburg.informatik.ultimate.smtinterpol.smtlib;

import java.io.FileReader;
import java.io.InputStreamReader;
import java.io.Reader;

import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.smtinterpol.IParser;
import de.uni_freiburg.informatik.ultimate.smtinterpol.smtlib2.SMTInterpol;
import de.uni_freiburg.informatik.ultimate.smtinterpol.util.MySymbolFactory;

public class SMTLIBParser implements IParser {

	@Override
	public int run(Script script, String filename, boolean printSucces,
			String verbosity, String timeout, String randomSeed) {
		try {
			MySymbolFactory symfactory = new MySymbolFactory();
			Reader reader;
			if (filename == null) {
				filename = "<stdin>";
				reader = new InputStreamReader(System.in);
			} else {
				reader = new FileReader(filename);
			}
			Lexer lexer = new Lexer(reader);
			lexer.setSymbolFactory(symfactory);
			Parser parser = new Parser(lexer, symfactory);
			parser.setFileName(filename);
			if (script == null)
				script = new SMTInterpol();
			if (verbosity != null)
				script.setOption(":verbosity", verbosity);
			if (timeout != null)
				script.setOption(":timeout", timeout);
			if (randomSeed != null)
				script.setOption(":randomSeed", randomSeed);
			parser.setSolver(script, false);
			parser.parse();
			Term[] interpolants = parser.benchmark.check();
			if (interpolants != null) {
				for (int i = 0; i < interpolants.length; ++i)
					System.out.println("Interpolant "+i+": "+interpolants[i]);
			}
			parser.benchmark.close();
			return 0;
		} catch (Exception e) {
			System.err.println(e.getMessage());
			return 1;
		}
	}

}
