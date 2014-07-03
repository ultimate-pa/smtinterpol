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

public abstract class Substitution {
	
	private boolean mActive = false;
	private final Term mMatch;
	private boolean mSuccess = false;
	private final boolean mRecurse;
	
	public Substitution(Term match) {
		this(match, false);
	}
	
	public Substitution(Term match, boolean recurse) {
		mMatch = match;
		mRecurse = recurse;
	}
	
	public boolean matches(Term t) {
		return mMatch == t;
	}
	
	public Term getMatch() {
		return mMatch;
	}
	
	public boolean isActive() {
		return mActive;
	}
	
	public void activate() {
		mActive = true;
	}
	
	public void deactivate() {
		mActive = false;
	}
	
	public boolean isRecurse() {
		return mRecurse;
	}
	
	public void success() {
		mSuccess = true;
	}
	
	public boolean isSuccess() {
		return mSuccess;
	}
	
	public abstract Term apply(Term input);
	public abstract Cmd getAdditionalCmd(Term input);
}
