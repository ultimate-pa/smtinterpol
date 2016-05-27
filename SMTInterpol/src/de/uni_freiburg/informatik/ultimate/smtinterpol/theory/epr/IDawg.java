package de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr;

import de.uni_freiburg.informatik.ultimate.logic.TermVariable;

public interface IDawg {
	
	public TermVariable[] getVariables();
	
	public IDawgSubstitution join(IDawg other);

	public IDawg complement();
}
