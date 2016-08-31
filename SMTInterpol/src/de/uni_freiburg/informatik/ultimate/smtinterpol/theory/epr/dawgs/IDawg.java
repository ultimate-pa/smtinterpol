package de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.dawgs;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.TermTuple;

public interface IDawg<LETTER, COLNAMES> {
	
	public COLNAMES[] getColnames();
	
	public int getArity();
	
	public IDawgSubstitution join(IDawg<LETTER, COLNAMES> other);

	public IDawg<LETTER, COLNAMES> complement();
	
	public IDawg<LETTER, COLNAMES> union(IDawg<LETTER, COLNAMES> other);
	
	public boolean accepts(LETTER[] point);

	/**
	 * Add one point to this Dawg
	 * Requires:
	 *  - arguments.length equals the arity of this dawg
	 *  - arguments only contains constants
	 * @param arguments
	 */
	public void add(LETTER[] arguments);

	/**
	 * Add all points of a given Dawg to this Dawg
	 * Requires:
	 *  - dawg's arities must be equal
	 * @param dawg
	 */
	public void addAll(IDawg<LETTER, COLNAMES> dawg);

	public boolean isEmpty();

	public boolean isUniversal();

	/**
	 * same as join??
	 * @param fp
	 * @return
	 */
	public IDawg<LETTER, COLNAMES> intersect(IDawg<LETTER, COLNAMES> other);

	public void removeAll(IDawg<LETTER, COLNAMES> other);

	public boolean supSetEq(IDawg<ApplicationTerm, TermVariable> points);
}
