package de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.dawgs;

import java.util.Collection;
import java.util.Collections;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
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
	
	@Override
	public final Collection<LETTER> allLettersThatMatch(List<LETTER> word, Map<COLNAMES, Integer> colnamesToIndex) {
		final Set<LETTER> result = new HashSet<LETTER>();
		for (LETTER constant : mDawgLetterFactory.getAllConstants(mSortId)) {
			if (this.matches(constant, word, colnamesToIndex)) {
				result.add(constant);
			}
		}
		return result;
	}
	
	/**
	 * Checks (only) if the equality constraints match for the given arguments.
	 * (needs to be overwritten if the DawgLetter poses further constraints..)
	 */
	@Override
	public boolean matches(LETTER ltr, List<LETTER> word, Map<COLNAMES, Integer> colnamesToIndex) {
		for (COLNAMES cn : mEqualColnames) {
			Integer cnIndex = colnamesToIndex.get(cn);
			if (word.get(cnIndex) != ltr) {
				return false;
			}
		}
		for (COLNAMES cn : mUnequalColnames) {
			Integer cnIndex = colnamesToIndex.get(cn);
			if (word.get(cnIndex) == ltr) {
				return false;
			}
		}
		return true;
	}
	
	/**
	 * Build a nice String from all the (dis)equality constraints of this DawgLetter.
	 * To be used by subclasses' toString methods.
	 * 
	 * @return
	 */
	protected String printedEqualityConstraints() {
		final StringBuilder sb = new StringBuilder();
		
		String comma = "";
		if (!mEqualColnames.isEmpty()) {
			sb.append("Eq: ");
			for (COLNAMES eq : mEqualColnames) { 
				sb.append(comma);
				sb.append(eq);
				comma = ", ";
			}
		}
		
		comma = "";
		if (!mUnequalColnames.isEmpty()) {
			sb.append(" UnEq: ");
			for (COLNAMES deq : mUnequalColnames) { 
				sb.append(comma);
				sb.append(deq);
				comma = ", ";
			}
		}
		return sb.toString();
	}
}
