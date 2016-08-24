package de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.dawgs;

public interface IDawgLetter<LETTER> {
	
	public class EnumDawgLetter<LETTER> implements IDawgLetter<LETTER> {
		
	}
	
	public class EqualsDawgLetter<LETTER> implements IDawgLetter<LETTER> {
		
	}
	
	public enum EmptyDawgLetter implements IDawgLetter {
		INSTANCE;
		
	}
	
	public enum UniversalDawgLetter implements IDawgLetter {
		INSTANCE;
		
	}
}
