package de.uni_freiburg.informatik.ultimate.smtinterpol.smtlib2;

import de.uni_freiburg.informatik.ultimate.smtinterpol.Config;

/**
 * Class to represent an S-expression.  An S-expression is represented internally as an array of objects.
 * The objects can be either arrays (sub-S-expressions), or other objects that implement a toString() method
 * to print their syntactical representation.
 * 
 * @author hoenicke
 *
 */
public class SExpression {
	private Object[] mData;

	public SExpression(Object[] data) {
		this.mData = data;
	}
	
	public Object[] getData() {
		return mData;
	}
	
	private static boolean convertSexp(final StringBuilder sb, final Object o, final int indentation) {
		if (o instanceof Object[]) {
			if (Config.RESULTS_ONE_PER_LINE && indentation > 0) {
				sb.append(System.getProperty("line.separator"));
				for (int i = 0; i < indentation; ++i) {
					sb.append(' ');
				}
			}
			sb.append('(');
			final Object[] array = (Object[]) o;
			boolean subarray = false;
			String sep = "";
			for (final Object el : array) {
				sb.append(sep);
				subarray |= convertSexp(sb, el, indentation + Config.INDENTATION);
				sep = " ";
			}
			if (subarray && Config.RESULTS_ONE_PER_LINE) {
				sb.append(System.getProperty("line.separator"));
				for (int i = 0; i < indentation; ++i) {
					sb.append(' ');
				}
			}
			sb.append(')');
			return true;
		} else {
			sb.append(o);
		}
		return false;
	}

	/**
	 * Convert S-expression to its string representation.
	 */
	public String toString() {
		StringBuilder sb = new StringBuilder();
		convertSexp(sb, mData, 0);
		return sb.toString();
	}
}
