package de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.dawgs;

import java.util.Collections;
import java.util.Set;

public abstract class AbstractDawgLetterWithEqualities<LETTER, COLNAMES> extends AbstractDawgLetter<LETTER, COLNAMES> {

	final Set<COLNAMES> mEqualColnames;
	final Set<COLNAMES> mUnequalColnames;

	public AbstractDawgLetterWithEqualities(DawgLetterFactory<LETTER, COLNAMES> dawgLetterFactory, 
			Set<COLNAMES> equalColnames, Set<COLNAMES> inequalColnames, Object sortId) {
		super(dawgLetterFactory, sortId);
		mEqualColnames = Collections.unmodifiableSet(equalColnames);
		mUnequalColnames = Collections.unmodifiableSet(inequalColnames);
	}
}
