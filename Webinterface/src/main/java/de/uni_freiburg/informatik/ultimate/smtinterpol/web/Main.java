package de.uni_freiburg.informatik.ultimate.smtinterpol.web;

import de.uni_freiburg.informatik.ultimate.logic.FormulaLet;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.smtinterpol.DefaultLogger;
import de.uni_freiburg.informatik.ultimate.smtinterpol.option.OptionMap;
import de.uni_freiburg.informatik.ultimate.smtinterpol.smtlib2.ParseEnvironment;
import de.uni_freiburg.informatik.ultimate.smtinterpol.smtlib2.SMTInterpol;
import de.uni_freiburg.informatik.ultimate.smtinterpol.proof.ProofRules;
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

	public void runSMTInterpol(String inputString) {
		final DefaultLogger logger = new DefaultLogger();
		final OptionMap options = new OptionMap(logger, true);

		SMTInterpol solver = new SMTInterpol(null, options);
		WebEnvironment pe = new WebEnvironment(solver, options);
		pe.parseStream(new StringReader(inputString), "<webinput>");
	}

	public class WebEnvironment extends ParseEnvironment {
		public WebEnvironment(Script script, OptionMap options) {
			super(script, options);
		}

		public void exitWithStatus(int status) {
			/* can't exit */
		}

		/**
		 * Post response from SMTInterpol directly to the client.
		 */
		public void printResponse(Object response) {
			if (response instanceof Term) {
				Term term = (Term) response;
				Term lettedTerm = new FormulaLet().let(term);
				if (ProofRules.isProofRule(ProofRules.RES, term)) {
					StringBuilder sb = new StringBuilder();
					ProofRules.printProof(sb, lettedTerm);
					postMessage(sb.toString());
				} else {
					postMessage(lettedTerm.toStringDirect());
				}
			} else {
				postMessage(response.toString());
			}
		}
	}
}
