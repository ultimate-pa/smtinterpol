/*
 * Copyright (C) 2019 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.smtinterpol.theory.quant.ematching;

import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.cclosure.CCTerm;

/**
 * Code to compare two CCTerms. If the terms are equal, the remaining code can be executed. If they are not yet equal,
 * executing the Compare code will install a trigger in the CClosure.
 * 
 * @author Tanja Schindler
 */
public class CompareCode implements ICode {

	private final EMatching mEMatching;
	private final int mFirstRegIndex, mSecondRegIndex;
	private final ICode mRemainingCode;

	public CompareCode(final EMatching eMatching, final int firstRegIndex, final int secondRegIndex,
			final ICode remainingCode) {
		mEMatching = eMatching;
		mFirstRegIndex = firstRegIndex;
		mSecondRegIndex = secondRegIndex;
		mRemainingCode = remainingCode;
	}

	@Override
	public void execute(CCTerm[] register) {
		final CCTerm firstTerm = register[mFirstRegIndex];
		final CCTerm secondTerm = register[mSecondRegIndex];
		if (mEMatching.getQuantTheory().getCClosure().isEqSet(firstTerm, secondTerm)) {
			mEMatching.addCode(mRemainingCode, register);
		} else {
			mEMatching.installCompareTrigger(firstTerm, secondTerm, mRemainingCode, register);
		}
	}

	@Override
	public String toString() {
		return "compare(r" + mFirstRegIndex + ", r" + mSecondRegIndex + ",\n" + mRemainingCode.toString() + ")";
	}
}
