package de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.partialmodel;

/**
 * Parent class for everything that may lie on the epr decide stack.
 * (e.g. different kinds of literals and markers)
 * 
 * @author Alexander Nutz
 */
public abstract class DecideStackEntry {

	/**
	 * A number indicating where on the epr decide stack, relatively to other entries,
	 * this entry lies. 
	 * Note that these number may not be adjacent for entries that are adjacent on the 
	 * epr decide stack, but their sequence is always strictly increasing from the bottom
	 * to the top of the epr decide stack.
	 */
	final int nr;
	
	public DecideStackEntry(int i) {
		nr = i;
	}
}
