package de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.partialmodel;

import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.TermTuple;

public interface IDawg {
	
	public TermVariable[] getVariables();
	
	public IDawgSubstitution join(IDawg other);

	public IDawg complement();
	
	public IDawg union(IDawg other);
	
	public boolean accepts(TermTuple point);
}
