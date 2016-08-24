package de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.dawgs;

public interface IDawgSubstitution {

	/**
	 * Compute the IDawg that results from applying this substitution to it.
	 * @param other
	 * @return
	 */
	public IDawg apply(IDawg other);
	
	/**
	 * Is this substitution empty, i.e., will its application always result 
	 * in an empty IDawg?
	 */
	public boolean isEmpty();
}
