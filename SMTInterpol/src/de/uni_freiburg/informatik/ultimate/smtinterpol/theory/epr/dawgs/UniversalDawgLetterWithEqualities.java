package de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.dawgs;

import java.util.Collection;
import java.util.List;
import java.util.Map;
import java.util.Set;

public class UniversalDawgLetterWithEqualities<LETTER, COLNAMES> extends AbstractDawgLetterWithEqualities<LETTER, COLNAMES> {
	
	public UniversalDawgLetterWithEqualities(DawgLetterFactory<LETTER, COLNAMES> dawgLetterFactory, 
			Set<COLNAMES> equalColnames, Set<COLNAMES> inequalColnames, Object sortId) {
		super(dawgLetterFactory, equalColnames, inequalColnames, sortId);
	}

	@Override
	public Set<IDawgLetter<LETTER, COLNAMES>> complement() {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public IDawgLetter<LETTER, COLNAMES> intersect(IDawgLetter<LETTER, COLNAMES> other) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public boolean matches(LETTER ltr, List<LETTER> word, Map<COLNAMES, Integer> colnamesToIndex) {
		// TODO Auto-generated method stub
		return false;
	}

	@Override
	public Collection<LETTER> allLettersThatMatch(List<LETTER> word, Map<COLNAMES, Integer> colnamesToIndex) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public IDawgLetter<LETTER, COLNAMES> restrictToLetter(LETTER selectLetter) {
		// TODO Auto-generated method stub
		return null;
	}

}
