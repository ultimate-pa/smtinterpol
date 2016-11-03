package de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.dawgs;

public abstract class AbstractEqualsDawgLetter<LETTER> extends DawgLetter<LETTER> {
	
	// the position in the point that is supposed to be equal
	int mEqualsPosition;

	// an EqualsDawgLetter attaches equals-information to a SetDawgLetter
	AbstractSetDawgLetter<LETTER> mBaseDawgLetter;

	public AbstractEqualsDawgLetter(int pos, AbstractSetDawgLetter<LETTER> set) {
		mEqualsPosition = pos;
		mBaseDawgLetter = set;
	}
	
	@Override
	public boolean contains(LETTER l) {
			assert false : "contains on an EqualsDawgLetter should not be called, right?..";
			return false;
	}

	public class AndEqualsDawgLetter extends AbstractEqualsDawgLetter<LETTER> {

		public AndEqualsDawgLetter(int pos, AbstractSetDawgLetter<LETTER> set) {
			super(pos, set);
		}

		@Override
		public DawgLetter<LETTER> complement() {
			return new OrNotEqualsDawgLetter(mEqualsPosition, 
					(AbstractSetDawgLetter<LETTER>) mBaseDawgLetter.complement());
		}
		
	}

	public class OrEqualsDawgLetter extends AbstractEqualsDawgLetter<LETTER> {
		

		public OrEqualsDawgLetter(int pos, AbstractSetDawgLetter<LETTER> set) {
			super(pos, set);
		}

		@Override
		public DawgLetter<LETTER> complement() {
			return new AndNotEqualsDawgLetter(mEqualsPosition, (AbstractSetDawgLetter<LETTER>) mBaseDawgLetter.complement());
		}
		
	}
	public class AndNotEqualsDawgLetter extends AbstractEqualsDawgLetter<LETTER> {
		
		public AndNotEqualsDawgLetter(int pos, AbstractSetDawgLetter<LETTER> set) {
			super(pos, set);
		}

		@Override
		public DawgLetter<LETTER> complement() {
			return new OrEqualsDawgLetter(mEqualsPosition, (AbstractSetDawgLetter<LETTER>) mBaseDawgLetter.complement());
		}
		
	}
	
	public class OrNotEqualsDawgLetter extends AbstractEqualsDawgLetter<LETTER> {
		
		public OrNotEqualsDawgLetter(int pos, AbstractSetDawgLetter<LETTER> set) {
			super(pos, set);
		}

		@Override
		public DawgLetter<LETTER> complement() {
			return new AndEqualsDawgLetter(mEqualsPosition, (AbstractSetDawgLetter<LETTER>) mBaseDawgLetter.complement());
		}
		
	}

}
