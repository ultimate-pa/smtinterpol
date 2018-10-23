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
	}
	
	/**
	 * The constructors.
	 */
	final Constructor[] mConstructors;
}
