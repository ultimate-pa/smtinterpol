package de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.dawgs;

import java.util.Set;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.EprTheory;

public class DawgFactory<LETTER, COLNAMES> {
	
	EprTheory mEprTheory;
	Set<LETTER> mAllConstants;
	
	public DawgFactory(Set<LETTER> allConstants, EprTheory eprTheory) {
		mEprTheory = eprTheory;
		mAllConstants = allConstants;
	}

	public IDawg<LETTER, COLNAMES> createEmptyDawg(COLNAMES[] termVariables) {
		assert termVariables != null;
		//TODO freeze the current allConstants set, here?? or can it just change transparently?? 
		return new Dawg<LETTER, COLNAMES>(termVariables, mAllConstants);
	}

	public IDawg<LETTER, COLNAMES> createEmptyDawg(int arity) {
		assert false : "TODO: implement";
		return null;
	}
	
}
