/*
 * Copyright (C) 2021 University of Freiburg
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

import java.util.ArrayList;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.DataType;
import de.uni_freiburg.informatik.ultimate.logic.DataType.Constructor;
import de.uni_freiburg.informatik.ultimate.logic.FunctionSymbol;
import de.uni_freiburg.informatik.ultimate.smtinterpol.convert.Clausifier;
import de.uni_freiburg.informatik.ultimate.smtinterpol.util.SymmetricPair;

/**
 * This ReverseTrigger is meant to be applied on to constructor terms and trigger the execution of rule 1 & 2 of the data type theory
 * 
 * @author moritz
 *
 */
public class DTReverseTrigger extends ReverseTrigger {
	/**
	 * The constructor term on which this trigger is applied.
	 */
	final CCTerm mArg;
	int mArgPos;
	/**
	 * The function symbol on which this trigger will be activated.
	 */
	final FunctionSymbol mFunctionSymbol;
	final Clausifier mClausifier;
	final DataTypeTheory mDTTheory;
	
	public DTReverseTrigger(DataTypeTheory dtTheory, Clausifier clausifier, FunctionSymbol fs, CCTerm arg) {
		mDTTheory = dtTheory;
		mClausifier = clausifier;
		mFunctionSymbol = fs;
		mArg = arg;
	}

	@Override
	public CCTerm getArgument() {
		return mArg;
	}

	@Override
	public int getArgPosition() {
		return 0;
	}

	@Override
	public FunctionSymbol getFunctionSymbol() {
		return mFunctionSymbol;
	}

	@Override
	public void activate(CCAppTerm appTerm) {
		/*
		 * 
		 */
		ApplicationTerm argAT = (ApplicationTerm) mArg.mFlatTerm;
		ArrayList<SymmetricPair<CCTerm>> reason = new ArrayList<>();
		reason.add(new SymmetricPair<CCTerm>(appTerm.getArg(), mArg));
		if (mFunctionSymbol.getName() == "is") {
			// If appTerm is a "is" function, check if it tests for the constructor of mArg.
			// If so set the function equal to true else to false. 
			FunctionSymbol fs = ((ApplicationTerm) appTerm.mFlatTerm).getFunction();
			if (fs.getIndices()[0].equals(argAT.getFunction().getName())) {
				mDTTheory.addPendingEquality(new SymmetricPair<CCTerm>(appTerm, mClausifier.getCCTerm(mClausifier.getTheory().mTrue)), reason);
			} else {
				mDTTheory.addPendingEquality(new SymmetricPair<CCTerm>(appTerm, mClausifier.getCCTerm(mClausifier.getTheory().mFalse)), reason);
			}
		} else {
			// If appTerm is a selector function, set it equal to the matchin argument of mArg.
			FunctionSymbol fs = argAT.getFunction();
			DataType argDT = (DataType) fs.getReturnSort().getSortSymbol();
			Constructor c = argDT.findConstructor(argAT.getFunction().getName());
			for (int i = 0; i < c.getSelectors().length; i++) {
				if (mFunctionSymbol.getName() == c.getSelectors()[i]) {
					mDTTheory.addPendingEquality(new SymmetricPair<CCTerm>(appTerm, mClausifier.getCCTerm(argAT.getParameters()[i])), reason);
					return;
				}
			}
			
			assert false :"selector function not part of constructor";
		}
	}

}
