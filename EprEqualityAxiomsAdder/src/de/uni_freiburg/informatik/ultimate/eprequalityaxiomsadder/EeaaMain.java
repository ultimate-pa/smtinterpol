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

	public static void main(String[] args) throws FileNotFoundException {
		// TODO Auto-generated method stub
		
		LogProxy logger = new DefaultLogger();
		
		String infileName = "C:/data/bin/smt-files/testEq.smt2";
		String outfileName = "C:/data/bin/smt-files/eeaaOutput.smt2";


//		try {
//			 loggingScript = new LoggingScript(outfileName, true);
//		} catch (FileNotFoundException e) {
//			System.err.println("could not create or find output file");
//		}
		
		//		final DefaultLogger logger = new DefaultLogger();
		IParser parser = new SMTLIB2Parser();
//		Script eeaaScript = new EeaaScript();
		Script noopScript = new NoopScript();
		LoggingScript loggingScript = new EeaaLoggingScript(noopScript, outfileName, true);

//		final int exitCode = parser.run(eeaaScript, infileName, new OptionMap(logger, true));
		final int exitCode = parser.run(loggingScript, infileName, new OptionMap(logger, true));
		System.exit(exitCode);
	}

}
