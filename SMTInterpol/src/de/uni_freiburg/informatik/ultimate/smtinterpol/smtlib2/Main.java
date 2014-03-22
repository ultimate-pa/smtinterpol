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

import java.math.BigInteger;

import de.uni_freiburg.informatik.ultimate.logic.SMTLIBException;

public final class Main {
    
    private Main() {
        // Hide constructor
    }
	
	private static void usage() {
		System.err.println(
		        "USAGE smtinterpol [-q] [-v] [-t <num>] [-r <num>] [file.smt2]");
	}
	
	public static void main(String[] param) {
        int paramctr = 0;
        ParseEnvironment parseEnv = new ParseEnvironment();
        while (paramctr < param.length
        		&& param[paramctr].startsWith("-")) {
        	try {
	        	if (param[paramctr].equals("--")) {
	        		paramctr++;
	        		break;
	        	} else if (param[paramctr].equals("-v")) {
	        		parseEnv.setOption(":verbosity", BigInteger.valueOf(5)); // NOCHECKSTYLE
	        		paramctr++;
	        	} else if (param[paramctr].equals("-q")) {
	        		parseEnv.setOption(":verbosity", BigInteger.valueOf(3)); // NOCHECKSTYLE
	        		paramctr++;
	        	} else if (param[paramctr].equals("-t") && ++paramctr < param.length) {
	        		parseEnv.setOption(":timeout", param[paramctr]);
	        		paramctr++;
	        	} else if (param[paramctr].equals("-r") && ++paramctr < param.length) {
	   				parseEnv.setOption(":random-seed", param[paramctr]);
	        		paramctr++;
	        	} else {
	        		usage();
	        		return;
	        	}
        	} catch (SMTLIBException eParams) {
        		System.err.println(eParams.getMessage());
        	}
        }
		String filename;
		if (paramctr < param.length) {
			filename = param[paramctr++];
		} else {
			filename = "<stdin>";
		}
		if (paramctr != param.length) {
			usage();
			return;
		}
        parseEnv.parseScript(filename);
	}
}
