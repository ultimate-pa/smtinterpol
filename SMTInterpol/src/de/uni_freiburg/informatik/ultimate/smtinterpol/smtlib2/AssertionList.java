package de.uni_freiburg.informatik.ultimate.smtinterpol.smtlib2;

import de.uni_freiburg.informatik.ultimate.logic.PrintTerm;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.smtinterpol.Config;

/**
 * Class to represent a list of assertions.  These are used for the getAssertion response, which should
 * print the assertions as they were given (without let conversion).
 * 
 * @author hoenicke
 */
public class AssertionList {
	private Term[] mAssertions;

	public AssertionList(Term[] assertions) {
		this.mAssertions = assertions;
	}
	
	public Term[] getData() {
		return mAssertions;
	}
	
	/**
	 * Convert S-expression to its string representation.
	 */
	public String toString() {
		final StringBuilder sb = new StringBuilder();
		final PrintTerm pt = new PrintTerm();
		sb.append('(');
		String sep = "";
		final String itemSep = Config.RESULTS_ONE_PER_LINE ? System.getProperty("line.separator") + " " : " ";
		for (final Term t : mAssertions) {
			sb.append(sep);
			pt.append(sb, t);
			sep = itemSep;
		}
		sb.append(')');
		return sb.toString();
	}
}
