package de.uni_freiburg.informatik.ultimate.smtinterpol.web;

import de.uni_freiburg.informatik.ultimate.logic.PrintTerm;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.smtinterpol.DefaultLogger;
import de.uni_freiburg.informatik.ultimate.smtinterpol.option.OptionMap;
import de.uni_freiburg.informatik.ultimate.smtinterpol.smtlib2.ParseEnvironment;
import de.uni_freiburg.informatik.ultimate.smtinterpol.smtlib2.SExpression;
import de.uni_freiburg.informatik.ultimate.smtinterpol.smtlib2.SMTInterpol;
import de.uni_freiburg.informatik.ultimate.smtinterpol.smtlib2.TerminationRequest;
import org.teavm.jso.JSBody;

import java.io.PrintWriter;
import java.io.StringReader;
import java.io.StringWriter;

public class Main implements SolverInterface {

	private WebTerminationRequest tR = new WebTerminationRequest();

	@JSBody(params = { "handler" }, script = "runWebInterface = handler;")
	public static native void setSolverInterface(SolverInterface handler);

	// native method to have the string argument written in js. ( f.e. wie self.postmsg)
	@JSBody(params = { "message" }, script = "self.postMessage(message);")
	public static native void postMessage(String message);

	public void run() {
		setSolverInterface(this);
	}

	public static void main(String[] args) {
		new Main().run();
	}

	public String runSMTInterpol(String inputString) {
		final DefaultLogger logger = new DefaultLogger();
		final OptionMap options = new OptionMap(logger, true);
		// NUll is the termination request, next Line.
		// Eigene Classe implementieren.
		SMTInterpol solver = new SMTInterpol(tR, options);
		WebEnvironment pe = new WebEnvironment(solver, options);
		StringWriter output = new StringWriter();
		options.getOption(":regular-output-channel").set(output);


		pe.parseStream(new StringReader(inputString), "webinput.smt2");
		return output.toString();
	}

	@Override
	public void requestTermination() {
		tR.setTerReq(true);
	}

	public class WebEnvironment extends ParseEnvironment {
		public WebEnvironment(Script script, OptionMap options) {
			super(script, options);
		}

		public void exitWithStatus(int status) {
			/* can't exit */
		}

		/*
		wird immer von smtInterpol aufgerufen immer wennn er ein Erg. hat.
		print response methode überscheiben , sodass die zwischen ergebnisse geposted werden
		public void printResponse(Object response)
		post messege response.tostring.
		 */
		public void printResponse(Object response) {
			postMessage(response.toString());
		}
	}

	public class WebTerminationRequest implements TerminationRequest {
		volatile boolean terReq = false;
		@Override
		public boolean isTerminationRequested() {
			return terReq;
		}
		public void setTerReq(boolean terReq1) {
			terReq = terReq1;
		}
	}
}