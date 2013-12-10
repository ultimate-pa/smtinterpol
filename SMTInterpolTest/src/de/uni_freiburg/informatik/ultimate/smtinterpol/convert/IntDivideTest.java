/*
 * Copyright (C) 2009-2012 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.smtinterpol.convert;


import java.math.BigInteger;
import java.util.ArrayList;
import java.util.Arrays;

import org.apache.log4j.Logger;
import org.junit.Test;

import de.uni_freiburg.informatik.ultimate.logic.FunctionSymbol;
import de.uni_freiburg.informatik.ultimate.logic.Logics;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.Theory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.ClauseDeletionHook;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.DPLLEngine;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.Literal;
import de.uni_freiburg.informatik.ultimate.smtinterpol.proof.ProofNode;
import de.uni_freiburg.informatik.ultimate.smtinterpol.smtlib2.TerminationRequest;
import de.uni_freiburg.informatik.ultimate.smtinterpol.util.TestCaseWithLogger;

/**
 * Test Class for integer divide operators.
 * 
 * @author Jochen Hoenicke
 */
public final class IntDivideTest extends TestCaseWithLogger {
	Theory mTheory;
	Clausifier mClausifier;
	Sort mIntSort, mRealSort;
	Term mI,mJ,mK,mL,mR,mS,mT;
	ArrayList<Literal[]> mClauses = new ArrayList<Literal[]>();
	
	public IntDivideTest() {
		mTheory = new Theory(Logics.QF_UFLIRA);
		Logger logger = Logger.getRootLogger();
		DPLLEngine dpllEngine = new DPLLEngine(mTheory, logger,
				new TerminationRequest() {
			
					@Override
					public boolean isTerminationRequested() {
						return false;
					}
				});
		mClausifier = new Clausifier(dpllEngine, 0) {
			@Override
			public void addClause(
					Literal[] lits, ClauseDeletionHook hook, ProofNode pn) {
				mClauses.add(lits);
			}
		};
		mClausifier.setLogic(Logics.QF_UFLIRA);
		
		Sort[] empty = new Sort[0];
		mIntSort = mTheory.getSort("Int");
		mRealSort = mTheory.getSort("Real");
		mI = mTheory.term(mTheory.declareFunction("i", empty, mIntSort));
		mJ = mTheory.term(mTheory.declareFunction("j", empty, mIntSort));
		mK = mTheory.term(mTheory.declareFunction("k", empty, mIntSort));
		mL = mTheory.term(mTheory.declareFunction("l", empty, mIntSort));
		mR = mTheory.term(mTheory.declareFunction("r", empty, mRealSort));
		mS = mTheory.term(mTheory.declareFunction("s", empty, mRealSort));
		mT = mTheory.term(mTheory.declareFunction("t", empty, mRealSort));
	}
	
	@Test
	@SuppressWarnings("unused")
	public void testCreateDiv() {
		Term five = mTheory.numeral(BigInteger.valueOf(5));// NOCHECKSTYLE
		FunctionSymbol abs = mTheory.getFunction("abs", mIntSort);
		FunctionSymbol add = mTheory.getFunction("+", mIntSort, mIntSort);
		FunctionSymbol addr = mTheory.getFunction("+", mRealSort, mRealSort);
		FunctionSymbol mul = mTheory.getFunction("*", mIntSort, mIntSort);
		FunctionSymbol div = mTheory.getFunction("div", mIntSort, mIntSort);
		FunctionSymbol mod = mTheory.getFunction("mod", mIntSort, mIntSort);
		FunctionSymbol toint = mTheory.getFunction("to_int", mRealSort);
		FunctionSymbol isint = mTheory.getFunction("is_int", mRealSort);
		FunctionSymbol toreal = mTheory.getFunction("to_real", mIntSort);
		Term termDiv = mTheory.term(div, mI, five);
		Term termMod = mTheory.term(mod, mI, five);
		Term termAbs = mTheory.term(abs, mJ);
		Term termToI = mTheory.term(toint, mR);
		Term termSum = mTheory.term(add,
				mTheory.term(mul, mTheory.term(div, mI, five), five),
				mTheory.term(mod, mI, five),
				mTheory.term(toint, mR),
				mTheory.term(abs, mJ));
		Term formIsInt = 
				mTheory.term(isint,
						mTheory.term(addr, mR, mS, mTheory.term(toreal, mI)));
		mClausifier.addFormula(formIsInt);
		System.err.println(formIsInt);
		for (Literal[] clause : mClauses)
			System.err.println(Arrays.toString(clause));
	}
}
