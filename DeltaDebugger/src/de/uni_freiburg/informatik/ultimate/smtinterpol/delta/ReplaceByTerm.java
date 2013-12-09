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
	
	Term mReplacement;
	
	public ReplaceByTerm(Term match, Term replacement) {
		super(match);
		mReplacement = replacement;
	}

	@Override
	public Term apply(Term input) {
		return mReplacement;
	}

	@Override
	public Cmd getAdditionalCmd(Term input) {
		return null;
	}
	
	public String toString() {
		StringBuilder sb = new StringBuilder();
		PrintTerm pt = new PrintTerm();
		pt.append(sb, getMatch());
		sb.append(" ==> ");
		pt.append(sb, mReplacement);
		return sb.toString();
	}
	
}
