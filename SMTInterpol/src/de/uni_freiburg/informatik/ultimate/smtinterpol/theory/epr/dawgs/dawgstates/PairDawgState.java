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
package de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.dawgs.dawgstates;

public class PairDawgState extends DawgState {

	final DawgState mFirst;
	final DawgState mSecond;
	
	final boolean mFirstIsSink;
	final boolean mSecondIsSink;
	
	public PairDawgState(DawgState s, boolean firstIsSink, boolean secondIsSink, DawgState replacement) {
		super(replacement);
		assert firstIsSink != secondIsSink;
		
		if (firstIsSink) {
			mFirst = null;
			mSecond = s;
			mFirstIsSink = true;
			mSecondIsSink = false;
		} else {
			mFirst = s;
			mSecond = null;
			mFirstIsSink = false;
			mSecondIsSink = true;
		}
	}

	public PairDawgState(DawgState f, DawgState s, DawgState replacement) {
		super(replacement);
		assert f != null && s != null;
		mFirstIsSink = false;
		mSecondIsSink = false;
		mFirst = f;
		mSecond = s;
	}
	
	public boolean isFirstSink() {
		return mFirstIsSink;
	}

	public boolean isSecondSink() {
		return mSecondIsSink;
	}

	public DawgState getFirst() {
		return mFirst;
	}
	
	public DawgState getSecond() {
		return mSecond;
	}
	
	@Override
	public String toString() {
		return String.format("PairDawgState%d(#%d,#%d)", 
				this.hashCode() % 10000,
				mFirstIsSink ? -1 : mFirst.hashCode() % 10000,
				mSecondIsSink ? -1 : mSecond.hashCode() % 10000);
	}
}