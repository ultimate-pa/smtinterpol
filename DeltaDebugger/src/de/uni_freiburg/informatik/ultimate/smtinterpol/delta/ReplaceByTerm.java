/*
 * Copyright (C) 2012-2013 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.smtinterpol.delta;

import de.uni_freiburg.informatik.ultimate.logic.PrintTerm;
import de.uni_freiburg.informatik.ultimate.logic.Term;

final class ReplaceByTerm extends Substitution {
	
	private final Term mReplacement;
	private final boolean mNeutral;
	
	public ReplaceByTerm(Term match, Term replacement, boolean neutral) {
		this(match, replacement, false, neutral);
	}
	
	public ReplaceByTerm(Term match, Term replacement, boolean recurse,
			boolean neutral) {
		super(match, recurse);
		mReplacement = replacement;
		mNeutral = neutral;
	}
	
	public boolean isNeutralReplacement() {
		return mNeutral;
	}
	
	public Term getReplacement() {
		return mReplacement;
	}

	@Override
	public Term apply(Term input) {
		return mReplacement;
	}

	@Override
	public Cmd getAdditionalCmd(Term input) {
		return null;
	}
	
	@Override
	public String toString() {
		final StringBuilder sb = new StringBuilder();
		final PrintTerm pt = new PrintTerm();
		pt.append(sb, getMatch());
		sb.append(" ==> ");
		pt.append(sb, mReplacement);
		return sb.toString();
	}
	
}
