package de.uni_freiburg.informatik.ultimate.eprequalityaxiomsadder;

import java.io.FileNotFoundException;

import de.uni_freiburg.informatik.ultimate.logic.LoggingScript;
import de.uni_freiburg.informatik.ultimate.logic.NoopScript;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.smtinterpol.DefaultLogger;
import de.uni_freiburg.informatik.ultimate.smtinterpol.IParser;
import de.uni_freiburg.informatik.ultimate.smtinterpol.LogProxy;
import de.uni_freiburg.informatik.ultimate.smtinterpol.option.OptionMap;
import de.uni_freiburg.informatik.ultimate.smtinterpol.smtlib2.SMTLIB2Parser;

public class EeaaMain {

	public static void main(String[] args) {
		LogProxy logger = new DefaultLogger();
		
		String infileName = null;
		String outfileName = null;
		try {
			infileName = args[0];
			outfileName = args[1];
		} catch (ArrayIndexOutOfBoundsException e) {
			System.out.println("Please give two arguments -- an input file and and output file (both .smt2)");
		}

		IParser parser = new SMTLIB2Parser();
		Script noopScript = new NoopScript();
		LoggingScript loggingScript = null;
		try {
			loggingScript = new EeaaLoggingScript(noopScript, outfileName, true);
		} catch (FileNotFoundException e) {
			System.out.println("File not found -- please give a valid output file name");
		}

		final int exitCode = parser.run(loggingScript, infileName, new OptionMap(logger, true));
		System.exit(exitCode);
	}

}
