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
package de.uni_freiburg.informatik.ultimate.smtinterpol.smtlib2;

import de.uni_freiburg.informatik.ultimate.logic.SMTLIBException;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.smtinterpol.IParser;

public class SMTLIB2Parser implements IParser {

	@Override
	public int run(Script script, String filename, boolean printSucces,
			String verbosity, String timeout, String randomSeed) {
		if (filename == null)
			filename = "<stdin>";
        ParseEnvironment parseEnv = new ParseEnvironment(script);
        try {
        	parseEnv.setOption(":print-success", printSucces);
        } catch (SMTLIBException se) {
        	parseEnv.printError(se.getMessage());
        }
        if (verbosity != null) {
        	try {
            	parseEnv.setOption(":verbosity", verbosity);
            } catch (SMTLIBException se) {
            	parseEnv.printError(se.getMessage());
            }
        }
        if (timeout != null) {
        	try {
            	parseEnv.setOption(":timeout", timeout);
            } catch (SMTLIBException se) {
            	parseEnv.printError(se.getMessage());
            }
        }
        if (randomSeed != null) {
        	try {
            	parseEnv.setOption(":random-seed", randomSeed);
            } catch (SMTLIBException se) {
            	parseEnv.printError(se.getMessage());
            }
        }
        try {	
        	parseEnv.parseScript(filename);
        } catch (SMTLIBException se) {
        	parseEnv.printError(se.getMessage());
        }
		return 0;
	}

}
