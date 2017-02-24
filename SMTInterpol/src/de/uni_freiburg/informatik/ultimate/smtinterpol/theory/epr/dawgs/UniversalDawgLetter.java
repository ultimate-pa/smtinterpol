package de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.dawgs;

import java.util.Collection;
import java.util.Collections;
import java.util.List;
import java.util.Map;
import java.util.Set;

/**
 * A DawgLetter that captures all LETTERs.
 * (i.e. the DawgLetter whose LETTER-set is "allConstants", and whose (un)equals-sets are empty)
 * 
 * @author Alexander Nutz
 *
 * @param <LETTER>
 * @param <COLNAMES>
 */
public class UniversalDawgLetter<LETTER, COLNAMES> implements IDawgLetter<LETTER, COLNAMES> {

	private final DawgLetterFactory<LETTER, COLNAMES> mDawgLetterFactory;

	UniversalDawgLetter(DawgLetterFactory<LETTER, COLNAMES> dlf) {
		mDawgLetterFactory = dlf;
	}

	@Override
	public Set<IDawgLetter<LETTER, COLNAMES>> complement() {
		return Collections.singleton(mDawgLetterFactory.getEmptyDawgLetter());
	}

	@Override
	public IDawgLetter<LETTER, COLNAMES> intersect(IDawgLetter<LETTER, COLNAMES> other) {
		return other;
	}
	
	@Override
	public Set<IDawgLetter<LETTER, COLNAMES>> difference(IDawgLetter<LETTER, COLNAMES> other) {
		return other.complement();
	}
	
	@Override
	public boolean matches(LETTER ltr, List<LETTER> word, Map<COLNAMES, Integer> colnamesToIndex) {
		return true;
	}
	
	@Override
	public IDawgLetter<LETTER, COLNAMES> restrictToLetter(LETTER ltr) {
		return mDawgLetterFactory.getOrCreateSingletonSetDawgLetter(ltr);
	}

	@Override
	public Collection<LETTER> allLettersThatMatch(List<LETTER> word, Map<COLNAMES, Integer> colnamesToIndex) {
		return mDawgLetterFactory.getAllConstants();
	}

	@Override
	public String toString() {
		return "UniversalDawgLetter";
	}
}