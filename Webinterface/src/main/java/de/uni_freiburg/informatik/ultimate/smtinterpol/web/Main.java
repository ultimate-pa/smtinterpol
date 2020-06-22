package de.uni_freiburg.informatik.ultimate.smtinterpol.web;

import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.smtinterpol.DefaultLogger;
import de.uni_freiburg.informatik.ultimate.smtinterpol.option.OptionMap;
import de.uni_freiburg.informatik.ultimate.smtinterpol.smtlib2.ParseEnvironment;
import de.uni_freiburg.informatik.ultimate.smtinterpol.smtlib2.SMTInterpol;
import org.teavm.jso.browser.Window;
import org.teavm.jso.dom.html.HTMLButtonElement;
import org.teavm.jso.dom.html.HTMLDocument;
import org.teavm.jso.dom.html.HTMLElement;
import org.teavm.jso.dom.html.HTMLInputElement;

import java.io.StringReader;
import java.io.StringWriter;

public class Main {
	private HTMLDocument document = Window.current().getDocument();
	private HTMLButtonElement runButton = document.getElementById("run").cast();
	private HTMLElement resultPanel = document.getElementById("result");
	private HTMLInputElement inputPanel = (HTMLInputElement) document.getElementById("input");

	public void run() {
		runButton.listenClick(evt -> runSMTInterpol());
	}

	public static void main(String[] args) {
		new Main().run();
	}

	public void runSMTInterpol() {
		runButton.setDisabled(true);
		String inputString = inputPanel.getValue().toString();

		try {
			final DefaultLogger logger = new DefaultLogger();
			final OptionMap options = new OptionMap(logger, true);
			SMTInterpol solver = new SMTInterpol(null, options);
			WebEnvironment pe = new WebEnvironment(solver, options);
			StringWriter output = new StringWriter();
			options.getOption(":regular-output-channel").set(output);
			resultPanel.clear();
			pe.parseStream(new StringReader(inputString), "webinput.smt2");
			resultPanel.appendChild(document.createTextNode(output.toString()));
		} finally {
			runButton.setDisabled(false);
		}
	}


	public class WebEnvironment extends ParseEnvironment {
		public WebEnvironment(Script script, OptionMap options) {
			super(script, options);
		}

		public void exitWithStatus(int status) {
			/* can't exit */
		}
	}
}
