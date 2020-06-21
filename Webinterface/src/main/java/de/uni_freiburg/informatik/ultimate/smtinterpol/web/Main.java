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
			SMTInterpol smtl = new SMTInterpol();
			final DefaultLogger logger = new DefaultLogger();
			final OptionMap options = new OptionMap(logger, true);
			WebEnvironment pe = new WebEnvironment(smtl, options);
			pe.parseStream(new StringReader(inputString), "webinput.smt2");

			if (inputPanel.getValue().toString().length() > 1) {
				resultPanel.clear();
				resultPanel.appendChild(document.createTextNode(pe.mResult.toString()));
			}
		} finally {
            runButton.setDisabled(false);
		}
    }


	public class WebEnvironment extends ParseEnvironment {

		public StringBuilder mResult = new StringBuilder();
		
		public WebEnvironment(Script script, OptionMap options) {
			super(script, options);
		}

		public void printResponse(final Object response) {
			mResult.append(response.toString()).append(System.getProperty("line.separator"));
		}
	}
}

