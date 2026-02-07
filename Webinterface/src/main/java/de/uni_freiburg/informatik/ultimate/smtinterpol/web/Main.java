package de.uni_freiburg.informatik.ultimate.smtinterpol.web;

import java.io.PrintWriter;
import java.io.StringReader;
import java.io.StringWriter;

import org.teavm.jso.JSBody;

import de.uni_freiburg.informatik.ultimate.logic.FormulaLet;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.smtinterpol.DefaultLogger;
import de.uni_freiburg.informatik.ultimate.smtinterpol.option.OptionMap;
import de.uni_freiburg.informatik.ultimate.smtinterpol.proof.ProofRules;
import de.uni_freiburg.informatik.ultimate.smtinterpol.proof.checker.CheckingScript;
import de.uni_freiburg.informatik.ultimate.smtinterpol.smtlib2.ParseEnvironment;
import de.uni_freiburg.informatik.ultimate.smtinterpol.smtlib2.SExpression;
import de.uni_freiburg.informatik.ultimate.smtinterpol.smtlib2.SMTInterpol;

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

	@Override
	public void runSMTInterpol(String inputString) {
		final DefaultLogger logger = new DefaultLogger();
		final OptionMap options = new OptionMap(logger, true);

		final SMTInterpol solver = new SMTInterpol(null, options);
		final WebEnvironment pe = new WebEnvironment(solver, options);
		pe.parseStream(new StringReader(inputString), "<webinput>");
	}

	@Override
	public void runProofChecker(String inputString, String proofString) {
		final DefaultLogger logger = new DefaultLogger();
		final OptionMap options = new OptionMap(logger, true);

		final Script solver = new CheckingScript(options, "<proofinput>", new StringReader(proofString)) {
			@Override
			public void printResult(Object result) {
				postMessage(result.toString());
			}
		};
		final WebEnvironment pe = new WebEnvironment(solver, options) {
			@Override
			public void printResponse(Object response) {
				if (response instanceof SExpression) {
					postMessage(response.toString());
				}
			}
		};
		try {
			pe.parseStream(new StringReader(inputString), "<webinput>");
		} catch (final Exception ex) {
			final StringWriter sw = new StringWriter();
			final PrintWriter pw = new PrintWriter(sw);
			ex.printStackTrace(pw);
			pw.close();
			postMessage(sw.toString());
		}
	}

	public class WebEnvironment extends ParseEnvironment {
		public WebEnvironment(Script script, OptionMap options) {
			super(script, options);
		}

		@Override
		public void exitWithStatus(int status) {
			/* can't exit */
		}

		/**
		 * Post response from SMTInterpol directly to the client.
		 */
		@Override
		public void printResponse(Object response) {
			if (response instanceof Term) {
				final Term term = (Term) response;
				final Term lettedTerm = new FormulaLet().let(term);
				if (ProofRules.isProof(term)) {
					final StringBuilder sb = new StringBuilder();
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
