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
package de.uni_freiburg.informatik.ultimate.smtinterpol.proofcheck;

import de.uni_freiburg.informatik.ultimate.logic.Term;

/**
 * This class wraps a function definition from a :named annotation to be
 * written later on.
 */
public class NamedWrapper {
	final String mName;
	final Term mSubterm;
	
	/**
	 * @param name the name
	 * @param subterm the sub-term
	 */
	public NamedWrapper(final String name, final Term subterm) {
		mName = name;
		mSubterm = subterm;
	}
	
	@Override
	public String toString() {
		final StringBuilder builder = new StringBuilder();
		builder.append('[');
		builder.append(mName);
		builder.append(", ");
		builder.append(mSubterm.toStringDirect());
		builder.append(']');
		return builder.toString();
	}
}
