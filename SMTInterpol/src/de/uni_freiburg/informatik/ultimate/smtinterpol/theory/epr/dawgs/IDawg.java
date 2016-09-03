package de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.dawgs;

import java.util.Collection;
import java.util.List;
import java.util.Map;
import java.util.SortedSet;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.TermTuple;

public interface IDawg<LETTER, COLNAMES> {
	
//	public COLNAMES[] getColnames();
	public SortedSet<COLNAMES> getColnames();
//	public List<COLNAMES> getColnames();
	
	public int getArity();
	
	public IDawg<LETTER, COLNAMES> join(IDawg<LETTER, COLNAMES> other);

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
	public void add(List<LETTER> arguments);

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

	/**
	 * Add all the given points of the given Dawg.
	 * Assumes that the given Dawgs column names are a subset of this Dawg's column names.
	 * @param d1
	 */
	public void addAllWithSubsetSignature(IDawg<LETTER, COLNAMES> d1);

	/**
	 * Removes all points from this dawg that, projected to the columns of the argument dawg,
	 * match at least one of the points in the argument dawg.
	 * @param clFulfilledPoints
	 */
	public void removeAllWithSubsetSignature(IDawg<LETTER, COLNAMES> points);

	public IDawg<LETTER, COLNAMES> select(Map<COLNAMES, LETTER> selectMap);

}
