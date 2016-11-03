package de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.dawgs;

import java.util.Collection;
import java.util.HashSet;
import java.util.Set;

public abstract class AbstractSetDawgLetter<LETTER> extends DawgLetter<LETTER> {

	public class SetDawgLetter extends AbstractSetDawgLetter<LETTER> {
		
		private final Set<LETTER> mLetters;
		
		public SetDawgLetter(Collection<LETTER> letters) {
			mLetters = new HashSet<LETTER>(letters);
		}

		@Override
		public boolean contains(LETTER l) {
			return mLetters.contains(l);
		}

		@Override
		public DawgLetter<LETTER> complement() {
			return new ComplementSetDawgLetter(this);
		}
		
	}
	
	public class ComplementSetDawgLetter extends AbstractSetDawgLetter<LETTER> {
		
		SetDawgLetter mSetLetter;

		public ComplementSetDawgLetter(SetDawgLetter setDawgLetter) {
			mSetLetter = setDawgLetter;
		}

		@Override
		public boolean contains(LETTER l) {
			return !mSetLetter.contains(l);
		}

		@Override
		public DawgLetter<LETTER> complement() {
			return mSetLetter;
		}
		
	}
}
