/*
 * Copyright (C) 2014 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.smtinterpol.theory.cclosure;

/**
 * An entry in the weakeq modulo i map.  This entry is an option type.  It can
 * either be a CCTerm that specifies where to look for a weakeq modulo i step,
 * or a pair of selects.  Use {@link #isModuloStep()} to check.  In both cases,
 * {@link #getNextArray()} gives the right endpoint of this step.
 * @author Juergen Christ
 */
public class WeakEQiEntry {
	
	final CCAppTerm mLeftSelect, mRightSelect;
	
	final CCTerm mLeftModuloArray, mRightModuloArray;
	
	public WeakEQiEntry(CCTerm nextLeftArray, CCTerm nextRightArray,
			boolean order) {
		mLeftSelect = mRightSelect = null;
		if (order) {
			mLeftModuloArray = nextLeftArray;
			mRightModuloArray = nextRightArray;
		} else {
			mLeftModuloArray = nextRightArray;
			mRightModuloArray = nextLeftArray;
		}
	}
	
	public WeakEQiEntry(CCAppTerm leftSelect, CCAppTerm rightSelect,
			boolean order) {
		if (order) {
			mLeftSelect = leftSelect;
			mRightSelect = rightSelect;
		} else {
			mLeftSelect = rightSelect;
			mRightSelect = leftSelect;
		}
		mLeftModuloArray = getLeftArray();
		mRightModuloArray = getRightArray();
	}
	
	public CCTerm getLeftModuloArray() {
		return mLeftModuloArray;
	}
	
	public CCTerm getRightModuloArray() {
		return mRightModuloArray;
	}
	
	final CCTerm getLeftSelect() {
		return mLeftSelect;
	}
	
	final CCTerm getRightSelect() {
		return mRightSelect;
	}
	
	final CCTerm getLeftArray() {
		return ((CCAppTerm) mLeftSelect.getFunc()).getArg();
	}
	
	final CCTerm getRightArray() {
		return ((CCAppTerm) mRightSelect.getFunc()).getArg();
	}
	
	final CCTerm getLeftIndex() {
		return mLeftSelect.mArg;
	}
	
	final CCTerm getRightIndex() {
		return mRightSelect.mArg;
	}
	
	public boolean isModuloStep() {
		return mLeftSelect != null;
	}
	

	public String toString() {
		return isModuloStep() ? (mLeftSelect + " <=> " + mRightSelect)
				: mLeftModuloArray + "<=>" + mRightModuloArray;
	}

}
