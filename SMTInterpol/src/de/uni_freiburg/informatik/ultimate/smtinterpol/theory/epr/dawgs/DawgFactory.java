package de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.dawgs;

import java.util.List;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;

public class DawgFactory<LETTER> {

	public IDawg<LETTER> createEmptyDawg(TermVariable[] termVariables) {
		assert termVariables != null;
		return new Dawg<LETTER>(termVariables);
	}
	
}
