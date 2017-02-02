package de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.dawgs;

import java.util.Collections;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

public class SimpleDawgLetter<LETTER, COLNAMES> implements DawgLetter<LETTER, COLNAMES> {
	
	private final Set<LETTER> mLetters;
	private final DawgLetterFactory<LETTER, COLNAMES> mDawgLetterFactory;
	
	public SimpleDawgLetter(DawgLetterFactory<LETTER, COLNAMES> dlf, Set<LETTER> letters) {
		mDawgLetterFactory = dlf;
		mLetters = letters;
	}

	@Override
	public Set<DawgLetter<LETTER, COLNAMES>> complement() {
		final Set<LETTER> resultLetters = new HashSet<LETTER>();
		resultLetters.addAll(mDawgLetterFactory.getAllConstants());
		resultLetters.removeAll(mLetters);
		
		return Collections.singleton(mDawgLetterFactory.getSimpleDawgLetter(resultLetters));
	}

	@Override
	public Set<DawgLetter<LETTER, COLNAMES>> difference(DawgLetter<LETTER, COLNAMES> other) {
		SimpleDawgLetter<LETTER, COLNAMES> otherSdl = (SimpleDawgLetter<LETTER, COLNAMES>) other;
		final Set<LETTER> resultLetters = new HashSet<LETTER>();
		resultLetters.addAll(mLetters);
		resultLetters.removeAll(otherSdl.mLetters);
	
		return Collections.singleton(mDawgLetterFactory.getSimpleDawgLetter(resultLetters));
	}

	@Override
	public DawgLetter<LETTER, COLNAMES> intersect(DawgLetter<LETTER, COLNAMES> other) {
		SimpleDawgLetter<LETTER, COLNAMES> otherSdl = (SimpleDawgLetter<LETTER, COLNAMES>) other;
		final Set<LETTER> resultLetters = new HashSet<LETTER>();
		resultLetters.addAll(mLetters);
		resultLetters.retainAll(otherSdl.mLetters);
	
		return mDawgLetterFactory.getSimpleDawgLetter(resultLetters);
	}

	@Override
	public boolean matches(LETTER ltr, List<LETTER> word, Map<COLNAMES, Integer> colnamesToIndex) {
		return mLetters.contains(ltr);
	}

	public Set<LETTER> getLetters() {
		return mLetters;
	}

	@Override
	public DawgLetter<LETTER, COLNAMES> restrictToLetter(LETTER selectLetter) {
		return mDawgLetterFactory.getSimpleDawgLetter(Collections.singleton(selectLetter));
	}
}
