package de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.dawgs;

import java.util.HashSet;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.EprHelpers;

public abstract class AbstractDawgLetter<LETTER, COLNAMES> implements IDawgLetter<LETTER, COLNAMES> {

	protected final Object mSortId;
	protected final DawgLetterFactory<LETTER, COLNAMES> mDawgLetterFactory;
	
	public AbstractDawgLetter(DawgLetterFactory<LETTER, COLNAMES> dawgLetterFactory, Object sortId) {
		assert sortId != null;
		mSortId = sortId;
		mDawgLetterFactory = dawgLetterFactory;
	}
	
	@Override
	public Object getSortId() {
		return mSortId;
	}
	
	
	@Override
	public final Set<IDawgLetter<LETTER, COLNAMES>> difference(IDawgLetter<LETTER, COLNAMES> other) {
		Set<IDawgLetter<LETTER, COLNAMES>> result = new HashSet<IDawgLetter<LETTER,COLNAMES>>();
		Set<IDawgLetter<LETTER, COLNAMES>> otherComplement = other.complement();
		// apply distributivity..
		for (IDawgLetter<LETTER, COLNAMES> oce : otherComplement) {
			final IDawgLetter<LETTER, COLNAMES> intersectDl = this.intersect(oce);
			if (intersectDl instanceof EmptyDawgLetter<?, ?>) {
				continue;
			}
			result.add(intersectDl);
		}
		assert !EprHelpers.hasEmptyLetter(result);
		return result;
	}
}
