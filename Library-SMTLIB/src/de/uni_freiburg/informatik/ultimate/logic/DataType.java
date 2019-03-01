package de.uni_freiburg.informatik.ultimate.logic;

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

		public Constructor(String name, String[] selectors, Sort[] argumentSorts) {
			this.mName = name;
			this.mSelectors = selectors;
			this.mArgumentSorts = argumentSorts;
		}

		public String getName() {
			return mName;
		}

		public Sort[] getArgumentSorts() {
			return mArgumentSorts;
		}

		public String[] getSelectors() {
			return mSelectors;
		}
	}

	public DataType(Theory theory, String name, int numParams) {
		super(theory, name, numParams, null, DATATYPE);
	}
	
	/**
	 * The constructors.
	 */
	Constructor[] mConstructors;
	

	public void setConstructors(Constructor[] constrs) {
		assert mConstructors == null;
		mConstructors = constrs;
	}

	public Constructor[] getContructors() {
		return mConstructors;
	}
}
