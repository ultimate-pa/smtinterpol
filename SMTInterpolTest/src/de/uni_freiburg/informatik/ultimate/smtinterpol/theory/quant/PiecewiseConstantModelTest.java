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
package de.uni_freiburg.informatik.ultimate.smtinterpol.theory.quant;

import java.math.BigInteger;
import java.util.Arrays;
import java.util.List;

import org.junit.Assert;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.JUnit4;

import de.uni_freiburg.informatik.ultimate.logic.FunctionSymbol;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.Theory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.DefaultLogger;
import de.uni_freiburg.informatik.ultimate.smtinterpol.convert.Clausifier;
import de.uni_freiburg.informatik.ultimate.smtinterpol.proof.SourceAnnotation;
import de.uni_freiburg.informatik.ultimate.smtinterpol.smtlib2.SMTInterpol;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.cclosure.CClosure;

/**
 * Tests for the model production for quantified formulas.
 *
 * @author Tanja Schindler
 */
@RunWith(JUnit4.class)
public class PiecewiseConstantModelTest {

	SMTInterpol mSolver;
	Theory mTheory;
	Clausifier mClausifier;
	CClosure mClosure;

	Sort mInt;
	Sort mU;

	FunctionSymbol mF;
	Term mLambda;
	Term[] mATerms;
	Term[] mBTerms;
	Term[][] mFTerms;
	List<Term> mXVars;
	Term mFX;

	public PiecewiseConstantModelTest() {
		mSolver = new SMTInterpol(new DefaultLogger());
		mSolver.setLogic("ALL");
		mTheory = mSolver.getTheory();
		mClausifier = mSolver.getClausifier();
		mClosure = mClausifier.getCClosure();
		mInt = mSolver.sort("Int");
		createterms();
	}

	private void createterms() {
		final Sort[] paramSort = { mInt, mInt };
		
		mLambda = mClausifier.getQuantifierTheory().getLambda(mInt);
		mClausifier.createCCTerm(mLambda, SourceAnnotation.EMPTY_SOURCE_ANNOT);

		mATerms = new Term[8];
		mBTerms = new Term[8];
		mATerms[0] = mLambda;
		mBTerms[0] = mLambda;
		for (int i = 1; i < 8; ++i) {
			final String ai = "a" + i;
			mTheory.declareFunction(ai, Script.EMPTY_SORT_ARRAY, mInt);
			mATerms[i] = mTheory.term(ai);
			final String bi = "b" + i;
			mTheory.declareFunction(bi, Script.EMPTY_SORT_ARRAY, mInt);
			mBTerms[i] = mTheory.term(bi);
		}

		mF = mTheory.declareFunction("f", paramSort, mInt);
		mFTerms = new Term[8][8];
		for (int i = 0; i < 8; i++) {
			for (int j = 0; j < 8; j++) {
				mFTerms[i][j] = mTheory.term(mF, mATerms[i], mBTerms[j]);
			}
		}

		mXVars = Arrays.asList(mSolver.variable("x1", mInt), mSolver.variable("x2", mInt));
		mFX = mTheory.term(mF, mXVars.toArray(new Term[mXVars.size()]));
	}

	@Test
	public void testInt() {
		mSolver.assertTerm(mSolver.term("<", Arrays.copyOfRange(mATerms, 1, mATerms.length)));
		mSolver.assertTerm(mSolver.term("<", Arrays.copyOfRange(mBTerms, 1, mBTerms.length)));
		mSolver.assertTerm(mSolver.term("=", mFTerms[0][0], mTheory.numeral(BigInteger.ZERO)));
		mSolver.assertTerm(mSolver.term("=", mFTerms[0][6], mTheory.numeral(BigInteger.ONE)));
		mSolver.assertTerm(mSolver.term("=", mFTerms[2][0], mTheory.numeral(BigInteger.valueOf(2))));
		mSolver.assertTerm(mSolver.term("=", mFTerms[4][6], mTheory.numeral(BigInteger.valueOf(3))));
		mSolver.assertTerm(mSolver.term("=", mFTerms[6][2], mTheory.numeral(BigInteger.valueOf(4))));
		mSolver.assertTerm(mSolver.term("=", mFTerms[6][4], mTheory.numeral(BigInteger.valueOf(5))));
		mSolver.checkSat();
		/* Model should look as follows
		 f(x,y) = ite (x>=a6/\y>=b4, f(a6,b4),
		               ite (x>=a6/\y>=b2, f(a6,b2),
		                    ite (x>=a4/\y>=b6, f(a4,b6),
		                         ite (x>=a2, f(a2,lambda),
		                              ite (y>=b6, f(lambda,b6), f(lambda,lambda)))))) */
		final PiecewiseConstantModel model = new PiecewiseConstantModel(mClausifier.getQuantifierTheory());
		final List<Term> subsA1B1 = Arrays.asList(mATerms[1], mBTerms[1]);
		Assert.assertEquals(mClausifier.getCCTerm(mFTerms[0][0]), model.evaluateInCC(mFX, mXVars, subsA1B1));
		final List<Term> subsA2B1 = Arrays.asList(mATerms[2], mBTerms[1]);
		Assert.assertEquals(mClausifier.getCCTerm(mFTerms[2][0]), model.evaluateInCC(mFX, mXVars, subsA2B1));
		final List<Term> subsA3B7 = Arrays.asList(mATerms[3], mBTerms[7]);
		Assert.assertEquals(mClausifier.getCCTerm(mFTerms[2][0]), model.evaluateInCC(mFX, mXVars, subsA3B7));
		final List<Term> subsA5B1 = Arrays.asList(mATerms[5], mBTerms[1]);
		Assert.assertEquals(mClausifier.getCCTerm(mFTerms[2][0]), model.evaluateInCC(mFX, mXVars, subsA5B1));
		final List<Term> subsA5B7 = Arrays.asList(mATerms[5], mBTerms[7]);
		Assert.assertEquals(mClausifier.getCCTerm(mFTerms[4][6]), model.evaluateInCC(mFX, mXVars, subsA5B7));
		final List<Term> subsA7B1 = Arrays.asList(mATerms[7], mBTerms[1]);
		Assert.assertEquals(mClausifier.getCCTerm(mFTerms[2][0]), model.evaluateInCC(mFX, mXVars, subsA7B1));
		final List<Term> subsA7B3 = Arrays.asList(mATerms[7], mBTerms[3]);
		Assert.assertEquals(mClausifier.getCCTerm(mFTerms[6][2]), model.evaluateInCC(mFX, mXVars, subsA7B3));
		final List<Term> subsA7B5 = Arrays.asList(mATerms[7], mBTerms[5]);
		Assert.assertEquals(mClausifier.getCCTerm(mFTerms[6][4]), model.evaluateInCC(mFX, mXVars, subsA7B5));
		final List<Term> subsA1B5 = Arrays.asList(mATerms[1], mBTerms[5]);
		Assert.assertEquals(mClausifier.getCCTerm(mFTerms[0][0]), model.evaluateInCC(mFX, mXVars, subsA1B5));
		final List<Term> subsA1B7 = Arrays.asList(mATerms[1], mBTerms[7]);
		Assert.assertEquals(mClausifier.getCCTerm(mFTerms[0][6]), model.evaluateInCC(mFX, mXVars, subsA1B7));
	}

	@Test
	public void testIntDefaultValues() {
		PiecewiseConstantModel model;
		// no f application
		model = new PiecewiseConstantModel(mClausifier.getQuantifierTheory());
		final List<Term> subsA1B1 = Arrays.asList(mATerms[1], mBTerms[1]);
		Assert.assertEquals(mClausifier.getCCTerm(mLambda), model.evaluateInCC(mFX, mXVars, subsA1B1));
		// no f(lambda,lambda) application
		mSolver.assertTerm(mSolver.term("<", mATerms[1], mATerms[2]));
		mSolver.assertTerm(mSolver.term("<", mBTerms[1], mBTerms[2]));
		mSolver.assertTerm(mSolver.term("=", mFTerms[0][2], mTheory.numeral(BigInteger.ONE)));
		mSolver.checkSat();
		model = new PiecewiseConstantModel(mClausifier.getQuantifierTheory());
		Assert.assertEquals(mClausifier.getCCTerm(mLambda), model.evaluateInCC(mFX, mXVars, subsA1B1));
	}
}
