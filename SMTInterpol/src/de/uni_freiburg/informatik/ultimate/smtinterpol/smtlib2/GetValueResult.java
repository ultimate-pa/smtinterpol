package de.uni_freiburg.informatik.ultimate.smtinterpol.smtlib2;

import java.util.Map;

import de.uni_freiburg.informatik.ultimate.logic.PrintTerm;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.smtinterpol.Config;

/**
 * Class to represent a list of assertions.  These are used for the getAssertion response, which should
 * print the assertions as they were given (without let conversion).
 * 
 * @author hoenicke
 */
public class GetValueResult {
	private Map<Term,Term> mValues;

	public GetValueResult(Map<Term, Term> result) {
		this.mValues = result;
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
		for (final Map.Entry<Term, Term> me : mValues.entrySet()) {
			sb.append(sep);
			sb.append('(');
			pt.append(sb, me.getKey());
			sb.append(' ');
			pt.append(sb, me.getValue());
			sb.append(')');
			sep = itemSep;
		}
		return sb.toString();
	}
}
