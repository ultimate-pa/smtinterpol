package de.uni_freiburg.informatik.ultimate.logic;

import java.util.NoSuchElementException;

/**
 * Represents an SMTLIB datatype sort.
 *
 * @author Jochen Hoenicke
 */
public class DataType extends SortSymbol {

	public static class Constructor {
		private final String mName;
		private final Sort[] mArgumentSorts;
		private final String[] mSelectors;

		public Constructor(final String name, final String[] selectors, final Sort[] argumentSorts) {
			mName = name;
			mSelectors = selectors;
			mArgumentSorts = argumentSorts;
		}

		public String getName() {
			return mName;
		}

		public Sort[] getArgumentSorts() {
			return mArgumentSorts;
		}

		public int getSelectorIndex(final String selector) {
			for (int i = 0; i < mSelectors.length; i++) {
				if (mSelectors[i].equals(selector)) {
					return i;
				}
			}
			throw new NoSuchElementException();
		}

		public String[] getSelectors() {
			return mSelectors;
		}

		@Override
		public String toString() {
			final StringBuilder sb = new StringBuilder();
			sb.append("(");
			sb.append(mName);
			if (mSelectors.length != 0) {
				for (int i = 0; i < mSelectors.length; i++) {
					sb.append(" ");
					sb.append("(");
					sb.append(mSelectors[i]);
					sb.append(" ");
					sb.append(mArgumentSorts[i]);
					sb.append(")");
				}
			}
			sb.append(")");
			return sb.toString();
		}
	}

	public DataType(final Theory theory, final String name, final int numParams) {
		super(theory, name, numParams, null, DATATYPE);
	}

	/**
	 * The constructors.
	 */
	Constructor[] mConstructors;
	/**
	 * The generic sort arguments.
	 */
	Sort[] mSortVariables;

	public void setConstructors(final Sort[] sortVars, final Constructor[] constrs) {
		assert mConstructors == null;
		mSortVariables = sortVars;
		mConstructors = constrs;
	}

	public Sort[] getSortVariables() {
		return mSortVariables;
	}

	public Constructor findConstructor(final String name) {
		for (int i = 0; i < mConstructors.length; i++) {
			if (mConstructors[i].getName().equals(name)) {
				return mConstructors[i];
			}
		}
		return null;
	}

	public Constructor getConstructor(final String name) {
		final Constructor constr = findConstructor(name);
		if (constr == null) {
			throw new NoSuchElementException();
		}
		return constr;
	}

	public Constructor[] getConstructors() {
		return mConstructors;
	}
}
