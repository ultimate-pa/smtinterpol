package de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.dawgs;

public abstract class AbstractSimpleDawgLetter<LETTER, COLNAMES> implements IDawgLetter<LETTER, COLNAMES> {

	protected final Object mSortId;
	
	public AbstractSimpleDawgLetter(Object sortId) {
		assert sortId != null;
		mSortId = sortId;
	}
	
	@Override
	public Object getSortId() {
		return mSortId;
	}
}
