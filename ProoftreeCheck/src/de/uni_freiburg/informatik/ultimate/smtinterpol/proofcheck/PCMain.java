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
package de.uni_freiburg.informatik.ultimate.smtinterpol.proofcheck;

import java.io.File;

import de.uni_freiburg.informatik.ultimate.smtinterpol.DefaultLogger;
import de.uni_freiburg.informatik.ultimate.smtinterpol.option.OptionMap;
import de.uni_freiburg.informatik.ultimate.smtinterpol.smtlib2.SMTLIB2Parser;

/**
 * This class is starts the proof checking process.
 * 
 * Input format:
 * [file name, (useIsabelle, prettyOutput, fastProofs, partialProof)]
 * 
 * @author Christian Schilling
 */
public final class PCMain {
	
	private PCMain() {
		// Hide constructor
	}
	public static void main(String[] args) {
		if (args.length == 0) {
			return;
		}
		
		// file name is split from folders (appears in Isabelle lemma file)
		final String[] folderSplit = args[0].split(File.separator);
		final String filename = folderSplit[folderSplit.length - 1];
		final String[] fileSplit = filename.split("\\.");
		assert (fileSplit.length > 0);
		final String filenameNoExtension = fileSplit[0];
		
		// optional parameters
		final boolean useIsabelle =
				(args.length > 1) ? Boolean.parseBoolean(args[1]) : false;
		final boolean prettyOutput =
				(args.length > 2) ? Boolean.parseBoolean(args[2]) : false;
		final boolean fastProofs =
				(args.length > 3) ? Boolean.parseBoolean(args[3]) : true;
		final boolean partialProof =
				(args.length > 4) ? Boolean.parseBoolean(args[4]) : false;
		
		ProofChecker checker = new ProofChecker(filenameNoExtension,
				useIsabelle, prettyOutput, fastProofs, partialProof);
		checker.setOption(":verbosity", 3);
		DefaultLogger logger = new DefaultLogger();
		OptionMap options = new OptionMap(logger, true);
		new SMTLIB2Parser().run(checker, args[0], options);
	}
}
