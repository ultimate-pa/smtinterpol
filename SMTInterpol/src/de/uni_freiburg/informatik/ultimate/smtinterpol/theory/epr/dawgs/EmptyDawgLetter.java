package de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.dawgs;

import java.util.Collection;
import java.util.Collections;
import java.util.List;
import java.util.Map;
import java.util.Set;

/**
 * A DawgLetter that captures no LETTER.
 * (probably this should not occur in any Dawg, but only as an intermediate result during construction
 *  -- an edge labelled with this letter should be omitted)
 * 
 * @author Alexander Nutz
 *
 * @param <LETTER>
 * @param <COLNAMES>
 */
public class EmptyDawgLetter<LETTER, COLNAMES> extends AbstractSimpleDawgLetter<LETTER, COLNAMES> {

	private final DawgLetterFactory<LETTER, COLNAMES> mDawgLetterFactory;

	EmptyDawgLetter(DawgLetterFactory<LETTER, COLNAMES> dlf, Object sortId) {
		super(sortId);
		mDawgLetterFactory = dlf;
	}

	@Override
	public Set<IDawgLetter<LETTER, COLNAMES>> complement() {
		return Collections.singleton(mDawgLetterFactory.getUniversalDawgLetter(mSortId));
	}

	@Override
	public IDawgLetter<LETTER, COLNAMES> intersect(IDawgLetter<LETTER, COLNAMES> other) {
		return this;
	}

	@Override
	public Set<IDawgLetter<LETTER, COLNAMES>> difference(IDawgLetter<LETTER, COLNAMES> other) {
		return Collections.singleton((IDawgLetter<LETTER, COLNAMES>) this);
	}

	@Override
	public boolean matches(LETTER ltr, List<LETTER> word, Map<COLNAMES, Integer> colnamesToIndex) {
		return false;
	}

	@Override
	public IDawgLetter<LETTER, COLNAMES> restrictToLetter(LETTER ltr) {
		assert false;
		return null;
	}

	@Override
	public Collection<LETTER> allLettersThatMatch(List<LETTER> word, Map<COLNAMES, Integer> colnamesToIndex) {
		return Collections.emptySet();
	}
	
	@Override
	public String toString() {
		return "EmptyDawgLetter";
	}
}

