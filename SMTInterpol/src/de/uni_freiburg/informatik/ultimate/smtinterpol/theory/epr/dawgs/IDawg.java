package de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.dawgs;

import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.TermTuple;

public interface IDawg<LETTER> {
	
	public TermVariable[] getVariables();
	
	public IDawgSubstitution join(IDawg<LETTER> other);

	public IDawg<LETTER> complement();
	
	public IDawg<LETTER> union(IDawg<LETTER> other);
	
	public boolean accepts(TermTuple point);

	/**
	 * Add one point to this Dawg
	 * Requires:
	 *  - arguments.length equals the arity of this dawg
	 *  - arguments only contains constants
	 * @param arguments
	 */
	public void add(Term[] arguments);

	/**
	 * Add all points of a given Dawg to this Dawg
	 * Requires:
	 *  - dawg's arities must be equal
	 * @param dawg
	 */
	public void addAll(IDawg<LETTER> dawg);

	public boolean isEmpty();

	public boolean isUniversal();

	/**
	 * same as join??
	 * @param fp
	 * @return
	 */
	public IDawg<LETTER> intersect(IDawg<LETTER> fp);

	public void removeAll(IDawg<LETTER> fpOne);
}
