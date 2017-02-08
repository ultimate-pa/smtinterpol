/*
 * Copyright (C) 2016-2017 Alexander Nutz (nutz@informatik.uni-freiburg.de)
 * Copyright (C) 2016-2017 University of Freiburg
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

import java.util.Set;

/**
 * 
 * @author Alexander Nutz (nutz@informatik.uni-freiburg.de)
 *
 */
public class DawgState {
	
	public DawgState() {
		
	}

	@Override
	public String toString() {
		return "DawgState#" + Integer.toString(this.hashCode()).substring(0, 4);
	}
}

class PairDawgState extends DawgState {

	final DawgState mFirst;
	final DawgState mSecond;
	
	final boolean mFirstIsSink;
	final boolean mSecondIsSink;
	
	PairDawgState(DawgState s, boolean firstIsSink, boolean secondIsSink) {
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

	PairDawgState(DawgState f, DawgState s) {
		assert f != null && s != null;
		mFirstIsSink = false;
		mSecondIsSink = false;
		mFirst = f;
		mSecond = s;
	}
	
	DawgState getFirst() {
		return mFirst;
	}
	
	DawgState getSecond() {
		return mSecond;
	}
	
	@Override
	public String toString() {
//		return "PairDawgState(#" + mFirst.hashCode() + ",#" + mSecond.hashCode() + ")";
		return String.format("PairDawgState%d(#%d,#%d)", 
				this.hashCode() % 10000,
				mFirstIsSink ? -1 : mFirst.hashCode() % 10000,
				mSecondIsSink ? -1 : mSecond.hashCode() % 10000);
	}
}

class SetDawgState extends DawgState {
	
	private final Set<DawgState> mDawgStates;
	
	SetDawgState(Set<DawgState> dawgStates) {
		mDawgStates = dawgStates;
	}
	
	Set<DawgState> getInnerStates() {
		return mDawgStates;
	}

	@Override
	public String toString() {
		return "SetDawgState:" + mDawgStates;
	}
}

/**
 * DawgState containing information for the rename-and-reorder dawg transformation.
 * 
 * @author Alexander Nutz (nutz@informatik.uni-freiburg.de)
 *
 * @param <LETTER>
 * @param <COLNAMES>
 */
class RenameAndReorderDawgState<LETTER, COLNAMES> extends DawgState { 


	private final IDawgLetter<LETTER, COLNAMES> mLetter;
	
	private final COLNAMES mRightNeighbourColumn;
	
	private final DawgState mInnerState;

	public RenameAndReorderDawgState(IDawgLetter<LETTER, COLNAMES> letter, COLNAMES column, DawgState innerDawgState) {
		this.mLetter = letter;
		this.mRightNeighbourColumn = column;
		this.mInnerState = innerDawgState;
	}

	/**
	 * An edge with this letter will be inserted in the new column
	 */
	public IDawgLetter<LETTER, COLNAMES> getLetter() {
		return mLetter;
	}

	/**
	 * A column in the old Dawgs signature or null, indicating where the new column will be inserted.
	 * The states that are left of this column will be split.
	 * (this value being null means that the final states of the old dawg will be split.
	 */
	public COLNAMES getColumn() {
		return mRightNeighbourColumn;
	}

	/**
	 * We make different copies from the old-dawg's states between old and new column, this fields
	 * contains the original state that we copied from.
	 */
	public DawgState getInnerState() {
		return mInnerState;
	}
	
}
