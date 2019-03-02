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

import de.uni_freiburg.informatik.ultimate.logic.Term;

/**
 * Super class for all commands containing terms.  This class is needed since
 * a command containing terms might contain named terms and thus provide
 * definitions of new symbols.
 * @author Juergen Christ
 */
public abstract class TermCmd extends Cmd {

	private boolean mHasNames = false;

	protected void addTerm(Term t) {
		mHasNames |= new NamedHelper().checkTerm(t);
	}

	protected void addTerms(Term[] ts) {
		final NamedHelper nh = new NamedHelper();
		for (int i = 0; i < ts.length && !mHasNames; ++i) {
			mHasNames |= nh.checkTerm(ts[i]);
		}
	}

	@Override
	public boolean hasDefinitions() {
		return mHasNames;
	}

}
