package de.uni_freiburg.informatik.ultimate.smtinterpol.web;

import org.teavm.jso.JSObject;

public interface SolverInterface extends JSObject {

    String runSMTInterpol(String input);
}
