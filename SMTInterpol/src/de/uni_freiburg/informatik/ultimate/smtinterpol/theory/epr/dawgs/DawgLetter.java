package de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.dawgs;

public abstract class DawgLetter<LETTER> {
	
	public abstract boolean contains(LETTER l);
	
	public abstract DawgLetter<LETTER> complement();	
	

	
	
	
	@SuppressWarnings("rawtypes")
	public static class EmptyDawgLetter extends DawgLetter {
		static EmptyDawgLetter INSTANCE = new EmptyDawgLetter();
		
		// hidden constructor
		private EmptyDawgLetter() {
		}

		@Override
		public boolean contains(Object l) {
			return false;
		}

		@Override
		public DawgLetter complement() {
			return UniversalDawgLetter.INSTANCE;
		}
		
	}
	
	@SuppressWarnings("rawtypes")
	public static class UniversalDawgLetter extends DawgLetter {
		static UniversalDawgLetter INSTANCE = new UniversalDawgLetter();

		// hidden constructor
		private UniversalDawgLetter() {
		}


		@Override
		public boolean contains(Object l) {
			return true;
		}

		@Override
		public DawgLetter complement() {
			return EmptyDawgLetter.INSTANCE;
		}
		
	}
}
