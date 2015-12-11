package de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr;

/**
 * Represents an uninterpreted predicate that the EPR theory reasons about.
 * Stores and updates a model for that predicate.
 * If setting a literal leads to a conflict, that conflict is reported.
 * 
 * @author Alexander Nutz
 */
public class EprPredicate {
	private final String mName;
	
	public EprPredicate(String name) {
		this.mName = name;
	}
	
	public void setPositive(EprAtom ea) {
		
	}

	public void setNegative(EprAtom ea) {
		
	}
	
	public void unset(EprAtom ea) {

	}
	
	public String toString() {
		return mName;
	}
}
