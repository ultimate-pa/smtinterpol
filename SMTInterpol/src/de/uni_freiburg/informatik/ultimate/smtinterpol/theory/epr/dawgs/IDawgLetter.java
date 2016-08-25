package de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.dawgs;

import java.util.Collection;
import java.util.HashSet;
import java.util.Set;

public interface IDawgLetter<LETTER> {
	
	public boolean contains(LETTER l);
	
	public IDawgLetter<LETTER> complement();
	
	public class EnumDawgLetter<LETTER> implements IDawgLetter<LETTER> {
		
		private final Set<LETTER> mLetters;
		
		public EnumDawgLetter(Collection<LETTER> letters) {
			mLetters = new HashSet<LETTER>(letters);
		}

		@Override
		public boolean contains(LETTER l) {
			return mLetters.contains(l);
		}

		@Override
		public IDawgLetter<LETTER> complement() {
			assert false : "TODO: implement";
			return null;
		}
		
	}
	
	public class EqualsDawgLetter<LETTER> implements IDawgLetter<LETTER> {

		@Override
		public boolean contains(LETTER l) {
			assert false : "TODO: implement";
			// not totally clear what this should do..
			return false;
		}

		@Override
		public IDawgLetter<LETTER> complement() {
			assert false : "TODO: implement";
			// not totally clear what this should do..
			return null;
		}
		
	}
	
	public enum EmptyDawgLetter implements IDawgLetter {
		INSTANCE;

		@Override
		public boolean contains(Object l) {
			return false;
		}

		@Override
		public IDawgLetter complement() {
			return UniversalDawgLetter.INSTANCE;
		}
		
	}
	
	public enum UniversalDawgLetter implements IDawgLetter {
		INSTANCE;

		@Override
		public boolean contains(Object l) {
			return true;
		}

		@Override
		public IDawgLetter complement() {
			return EmptyDawgLetter.INSTANCE;
		}
		
	}
}
