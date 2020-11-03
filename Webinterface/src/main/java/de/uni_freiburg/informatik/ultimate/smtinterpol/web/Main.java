package de.uni_freiburg.informatik.ultimate.smtinterpol.web;

import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.smtinterpol.DefaultLogger;
import de.uni_freiburg.informatik.ultimate.smtinterpol.option.OptionMap;
import de.uni_freiburg.informatik.ultimate.smtinterpol.smtlib2.ParseEnvironment;
import de.uni_freiburg.informatik.ultimate.smtinterpol.smtlib2.SMTInterpol;
import org.teavm.jso.JSBody;

import java.io.StringReader;
import java.io.StringWriter;

public class Main implements SolverInterface {

	@JSBody(params = { "handler" }, script = "runWebInterface = handler;")
	public static native void setSolverInterface(SolverInterface handler);

	// native method to have the string argument written in js. ( f.e. self.postmsg)
	@JSBody(params = { "message" }, script = "self.postMessage(message);")
	public static native void postMessage(String message);

	public void run() {
		setSolverInterface(this);
	}

	public static void main(String[] args) {
		new Main().run();
	}

	public String runSMTInterpol(String inputString) {
		StringWriter output = new StringWriter();

		final DefaultLogger logger = new DefaultLogger();
		final OptionMap options = new OptionMap(logger, true);

		SMTInterpol solver = new SMTInterpol(null, options);
		WebEnvironment pe = new WebEnvironment(solver, options);

		options.getOption(":regular-output-channel").set(output);
		pe.parseStream(new StringReader(inputString), "webinput.smt2");

		return output.toString();
	}

	public class WebEnvironment extends ParseEnvironment {
		public WebEnvironment(Script script, OptionMap options) {
			super(script, options);
		}

		public void exitWithStatus(int status) {
			/* can't exit */
		}

		/*
		wird immer von smtInterpol aufgerufen, immer wennn er ein Erg. hat.
		print response methode überscheiben, sodass die zwischen ergebnisse geposted werden
		können.
		 */
		public void printResponse(Object response) {
			postMessage(response.toString());
		}
	}
}