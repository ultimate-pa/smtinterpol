/*
 * Copyright (C) 2017 Alexander Nutz (nutz@informatik.uni-freiburg.de)
 * Copyright (C) 2017 University of Freiburg
 *
 * This file is part of SMTInterpol.
 *
 * SMTInterpol is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * SMTInterpol is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with SMTInterpol.  If not, see <http://www.gnu.org/licenses/>.
 */
package de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.dawgs;

import java.util.Collection;
import java.util.Collections;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

/**
 * 
 * @author Alexander Nutz (nutz@informatik.uni-freiburg.de)
 *
 * @param <LETTER>
 * @param <COLNAMES>
 * 
 * deprecated because DawgLettersWithEqualities don't work well with projectAwayColumn operation
 *  --> it seems simpler to work around them completely by using "constructive equality reasoning"
 */
@Deprecated
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
	
	@Override
	public IDawgLetter<LETTER, COLNAMES> union(IDawgLetter<LETTER, COLNAMES> other) {
		assert false : "this should not be called (the result of a DWLE-union is a set of DLWEs in general";
		return null;
	}
}
