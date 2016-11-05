package de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.dawgs;

import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;
import java.util.SortedSet;

public class DawgLetterFactory<LETTER, COLNAMES> {
	
	
	UniversalDawgLetter<LETTER, COLNAMES> mUniversalDawgLetter;
	EmptyDawgLetter<LETTER, COLNAMES> mEmptyDawgLetter;

	Set<DawgLetter<LETTER, COLNAMES>> mUniversalDawgLetterSingleton;
	Set<DawgLetter<LETTER, COLNAMES>> mEmptyDawgLetterSingleton;
	
	
	Set<LETTER> mAllConstants;
	
	Map<Set<LETTER>, Map<Set<COLNAMES>, Map<Set<COLNAMES>, DawgLetter<LETTER, COLNAMES>>>> mKnownDawgLetters;
	

	public DawgLetterFactory(Set<LETTER> allConstants) {
		mAllConstants = allConstants;
		
		mKnownDawgLetters = 
				new HashMap<Set<LETTER>, Map<Set<COLNAMES>, Map<Set<COLNAMES>, DawgLetter<LETTER, COLNAMES>>>>();

		mUniversalDawgLetter = new UniversalDawgLetter<LETTER, COLNAMES>(this);
		mEmptyDawgLetter = new EmptyDawgLetter<LETTER, COLNAMES>(this);
		mEmptyDawgLetterSingleton = Collections.singleton((DawgLetter<LETTER, COLNAMES>) mEmptyDawgLetter);
		mUniversalDawgLetterSingleton = Collections.singleton((DawgLetter<LETTER, COLNAMES>) mUniversalDawgLetter);
	}

	public DawgLetter<LETTER, COLNAMES> createSingletonSetDawgLetter(LETTER element) {
		Set<LETTER> singleton = new HashSet<LETTER>();
		singleton.add(element);
		Set<COLNAMES> es = Collections.emptySet();
		return getDawgLetter(singleton, es, es);
	}
	
	UniversalDawgLetter<LETTER, COLNAMES> getUniversalDawgLetter() {
		return mUniversalDawgLetter;
	}
	
	EmptyDawgLetter<LETTER, COLNAMES> getEmptyDawgLetter() {
		return mEmptyDawgLetter;
	}

	Set<DawgLetter<LETTER, COLNAMES>> getUniversalDawgLetterSingleton() {
		return mUniversalDawgLetterSingleton;
	}
	
	Set<DawgLetter<LETTER, COLNAMES>> getEmptyDawgLetterSingleton() {
		return mEmptyDawgLetterSingleton;
	}

	public DawgLetter<LETTER, COLNAMES> getDawgLetter(Set<LETTER> newLetters, Set<COLNAMES> equalColnames,
			Set<COLNAMES> inequalColnames) {

		if (newLetters.isEmpty()) {
			// if the set of LETTERs is empty, the (in)equalities don't matter
			return mEmptyDawgLetter;
		}
		
		if (newLetters.equals(mAllConstants) 
				&& equalColnames.isEmpty() 
				&& inequalColnames.isEmpty()) {
			return mUniversalDawgLetter;
		}
		
		
		Map<Set<COLNAMES>, Map<Set<COLNAMES>, DawgLetter<LETTER, COLNAMES>>> colnamesToColnamesToDawgLetter = 
				mKnownDawgLetters.get(newLetters);
		
		if (colnamesToColnamesToDawgLetter == null) {
			colnamesToColnamesToDawgLetter = 
					new HashMap<Set<COLNAMES>, Map<Set<COLNAMES>,DawgLetter<LETTER,COLNAMES>>>();
			mKnownDawgLetters.put(newLetters, colnamesToColnamesToDawgLetter);
		}
		
		Map<Set<COLNAMES>, DawgLetter<LETTER, COLNAMES>> colNamesToDawgLetter =
					colnamesToColnamesToDawgLetter.get(equalColnames);
		
		if (colNamesToDawgLetter == null) {
			colNamesToDawgLetter = new HashMap<Set<COLNAMES>, DawgLetter<LETTER,COLNAMES>>();
			colnamesToColnamesToDawgLetter.put(equalColnames, colNamesToDawgLetter);
		}
		
		DawgLetter<LETTER, COLNAMES> dl = colNamesToDawgLetter.get(inequalColnames);
		
		if (dl == null) {
			dl = new DawgLetter<LETTER, COLNAMES>(newLetters, equalColnames, inequalColnames, this);
			colNamesToDawgLetter.put(inequalColnames, dl);
		}
		
		return dl;
	}
	
	public Set<LETTER> getAllConstants() {
		return mAllConstants;
	}
}
