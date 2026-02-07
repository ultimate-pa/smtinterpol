package de.uni_freiburg.informatik.ultimate.smtinterpol.web;

import org.teavm.jso.JSObject;

public interface SolverInterface extends JSObject {

	void runSMTInterpol(String input);

	void runProofChecker(String input, String proof);
}
