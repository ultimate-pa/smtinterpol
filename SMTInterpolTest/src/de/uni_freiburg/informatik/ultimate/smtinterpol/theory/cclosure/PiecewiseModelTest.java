/*
 * Copyright (C) 2026 University of Freiburg
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

import java.math.BigInteger;
import java.util.Arrays;

import org.junit.Assert;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.JUnit4;

import de.uni_freiburg.informatik.ultimate.logic.FunctionSymbol;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.Theory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.DefaultLogger;
import de.uni_freiburg.informatik.ultimate.smtinterpol.convert.Clausifier;
import de.uni_freiburg.informatik.ultimate.smtinterpol.model.SharedTermEvaluator;
import de.uni_freiburg.informatik.ultimate.smtinterpol.option.SMTInterpolConstants;
import de.uni_freiburg.informatik.ultimate.smtinterpol.smtlib2.SMTInterpol;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.cclosure.PiecewiseModel.Value;

/**
 * Tests for the piecewise-constant model of uninterpreted functions. The Int tests are ported from
 * {@code PiecewiseConstantModelTest} (Tanja Schindler) on the {@code quantifier_models} branch.
 *
 * @author Jochen Hoenicke
 */
@RunWith(JUnit4.class)
public class PiecewiseModelTest {

	SMTInterpol mSolver;
	Theory mTheory;
	Clausifier mClausifier;
	Sort mInt;

	FunctionSymbol mF;
	Term mLambda;
	Term[] mATerms;
	Term[] mBTerms;
	Term[][] mFTerms;

	public PiecewiseModelTest() {
		mSolver = new SMTInterpol(new DefaultLogger());
		mSolver.setLogic("ALL");
		mTheory = mSolver.getTheory();
		mClausifier = mSolver.getClausifier();
		mInt = mSolver.sort("Int");
		mLambda = lambda(mInt);

		mATerms = new Term[8];
		mBTerms = new Term[8];
		mATerms[0] = mLambda;
		mBTerms[0] = mLambda;
		for (int i = 1; i < 8; ++i) {
			mATerms[i] = declare("a" + i, mInt);
			mBTerms[i] = declare("b" + i, mInt);
		}
		mF = mTheory.declareFunction("f", new Sort[] { mInt, mInt }, mInt);
		mFTerms = new Term[8][8];
		for (int i = 0; i < 8; i++) {
			for (int j = 0; j < 8; j++) {
				mFTerms[i][j] = mTheory.term(mF, mATerms[i], mBTerms[j]);
			}
		}
	}

	private Term lambda(final Sort sort) {
		return mTheory.term(mTheory.getFunctionWithResult(SMTInterpolConstants.LAMBDA, null, sort, new Sort[0]));
	}

	private Term declare(final String name, final Sort sort) {
		mTheory.declareFunction(name, Script.EMPTY_SORT_ARRAY, sort);
		return mTheory.term(name);
	}

	private Term num(final int i) {
		return mTheory.numeral(BigInteger.valueOf(i));
	}

	private PiecewiseModel buildModel() {
		return new PiecewiseModel(mClausifier.getCClosure(), mClausifier.getArrayTheory(),
				new SharedTermEvaluator(mClausifier),
				sort -> mClausifier.getCCTerm(lambda(sort)));
	}

	/** The value of a ground term: its CC value if it has a CCTerm, otherwise its LA value. */
	private Value value(final PiecewiseModel model, final Term term) {
		final CCTerm cc = mClausifier.getCCTerm(term);
		if (cc != null) {
			return model.getValue(cc);
		}
		return Value.concrete(term.getSort(), new SharedTermEvaluator(mClausifier).evaluate(term, mTheory));
	}

	private void assertCorner(final PiecewiseModel model, final Term expected, final Term... args) {
		final Value[] argValues = new Value[args.length];
		for (int i = 0; i < args.length; i++) {
			argValues[i] = value(model, args[i]);
		}
		final FunctionSymbol func = ((de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm) expected)
				.getFunction();
		Assert.assertEquals(mClausifier.getCCTerm(expected), model.getCorner(func, argValues));
	}

	@Test
	public void testInt() {
		mSolver.assertTerm(mSolver.term("<", Arrays.copyOfRange(mATerms, 1, mATerms.length)));
		mSolver.assertTerm(mSolver.term("<", Arrays.copyOfRange(mBTerms, 1, mBTerms.length)));
		mSolver.assertTerm(mSolver.term("=", mFTerms[0][0], num(0)));
		mSolver.assertTerm(mSolver.term("=", mFTerms[0][6], num(1)));
		mSolver.assertTerm(mSolver.term("=", mFTerms[2][0], num(2)));
		mSolver.assertTerm(mSolver.term("=", mFTerms[4][6], num(3)));
		mSolver.assertTerm(mSolver.term("=", mFTerms[6][2], num(4)));
		mSolver.assertTerm(mSolver.term("=", mFTerms[6][4], num(5)));
		Assert.assertEquals(LBool.SAT, mSolver.checkSat());
		/* The model is
		 f(x,y) = ite (x>=a6/\y>=b4, f(a6,b4),
		               ite (x>=a6/\y>=b2, f(a6,b2),
		                    ite (x>=a4/\y>=b6, f(a4,b6),
		                         ite (x>=a2, f(a2,lambda),
		                              ite (y>=b6, f(lambda,b6), f(lambda,lambda)))))) */
		final PiecewiseModel model = buildModel();
		assertCorner(model, mFTerms[0][0], mATerms[1], mBTerms[1]);
		assertCorner(model, mFTerms[2][0], mATerms[2], mBTerms[1]);
		assertCorner(model, mFTerms[2][0], mATerms[3], mBTerms[7]);
		assertCorner(model, mFTerms[2][0], mATerms[5], mBTerms[1]);
		assertCorner(model, mFTerms[4][6], mATerms[5], mBTerms[7]);
		assertCorner(model, mFTerms[2][0], mATerms[7], mBTerms[1]);
		assertCorner(model, mFTerms[6][2], mATerms[7], mBTerms[3]);
		assertCorner(model, mFTerms[6][4], mATerms[7], mBTerms[5]);
		assertCorner(model, mFTerms[0][0], mATerms[1], mBTerms[5]);
		assertCorner(model, mFTerms[0][6], mATerms[1], mBTerms[7]);
		assertCorner(model, mFTerms[0][0], mLambda, mLambda);
		// the corners themselves
		assertCorner(model, mFTerms[4][6], mATerms[4], mBTerms[6]);
		assertCorner(model, mFTerms[6][4], mATerms[6], mBTerms[4]);
		Assert.assertEquals(Value.concrete(mInt, Rational.valueOf(3, 1)),
				model.evaluate(mF, new Value[] { value(model, mATerms[5]), value(model, mBTerms[7]) }));
	}

	@Test
	public void testIntDefaultValues() {
		final Value[] subsA1B1 = new Value[] { Value.concrete(mInt, Rational.ZERO), Value.concrete(mInt, Rational.ONE) };
		// no f application
		PiecewiseModel model = buildModel();
		Assert.assertNull(model.getCorner(mF, subsA1B1));
		Assert.assertEquals(Value.lambda(mInt), model.evaluate(mF, subsA1B1));
		// no f(lambda,lambda) application
		mSolver.assertTerm(mSolver.term("<", mATerms[1], mATerms[2]));
		mSolver.assertTerm(mSolver.term("<", mBTerms[1], mBTerms[2]));
		mSolver.assertTerm(mSolver.term("=", mFTerms[0][2], num(1)));
		Assert.assertEquals(LBool.SAT, mSolver.checkSat());
		model = buildModel();
		Assert.assertNull(model.getCorner(mF, new Value[] { value(model, mATerms[1]), value(model, mBTerms[1]) }));
		assertCorner(model, mFTerms[0][2], mATerms[1], mBTerms[2]);
		assertCorner(model, mFTerms[0][2], mATerms[2], mBTerms[2]);
	}

	/** Classes without LA shared term are above all concrete values, in creation order. */
	@Test
	public void testCCOnly() {
		final FunctionSymbol g = mTheory.declareFunction("g", new Sort[] { mInt }, mInt);
		final Term c = declare("c", mInt);
		final Term d = declare("d", mInt);
		final Term gc = mTheory.term(g, c);
		final Term gd = mTheory.term(g, d);
		final Term ga1 = mTheory.term(g, mATerms[1]);
		mSolver.assertTerm(mSolver.term("<", mATerms[1], mATerms[2]));
		mSolver.assertTerm(mSolver.term("distinct", gc, gd, ga1));
		mSolver.assertTerm(mSolver.term("=", ga1, num(7)));
		Assert.assertEquals(LBool.SAT, mSolver.checkSat());
		final PiecewiseModel model = buildModel();
		final Value vc = value(model, c);
		final Value vd = value(model, d);
		final Value va2 = value(model, mATerms[2]);
		Assert.assertFalse(vc.isConcrete());
		Assert.assertTrue(va2.isConcrete());
		Assert.assertTrue(va2.compareTo(vc) < 0);
		Assert.assertTrue(vc.compareTo(vd) < 0);
		Assert.assertTrue(vc.compareTo(vc.addOffset(Rational.ONE)) < 0);
		Assert.assertTrue(vc.addOffset(Rational.valueOf(100, 1)).compareTo(vd) < 0);
		assertCorner(model, ga1, mATerms[2]);
		assertCorner(model, gc, c);
		assertCorner(model, gc, c, Rational.ONE);
		assertCorner(model, gd, d);
		Assert.assertNull(model.getCorner(g, new Value[] { Value.lambda(mInt) }));
	}

	private void assertCorner(final PiecewiseModel model, final Term expected, final Term arg,
			final Rational offset) {
		final FunctionSymbol func = ((de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm) expected)
				.getFunction();
		Assert.assertEquals(mClausifier.getCCTerm(expected),
				model.getCorner(func, new Value[] { value(model, arg).addOffset(offset) }));
	}

	/** Uninterpreted arguments: exact class first, then the lambda corner. */
	@Test
	public void testUninterpreted() {
		mSolver.declareSort("U", 0);
		final Sort u = mSolver.sort("U");
		final Term lambdaU = lambda(u);
		final FunctionSymbol h = mTheory.declareFunction("h", new Sort[] { u, mInt }, mInt);
		final Term p = declare("p", u);
		final Term q = declare("q", u);
		final Term r = declare("r", u);
		final Term hp1 = mTheory.term(h, p, mATerms[1]);
		final Term hl2 = mTheory.term(h, lambdaU, mATerms[2]);
		final Term hq3 = mTheory.term(h, q, mATerms[3]);
		mSolver.assertTerm(mSolver.term("<", mATerms[1], mATerms[2], mATerms[3]));
		mSolver.assertTerm(mSolver.term("distinct", p, q));
		mSolver.assertTerm(mSolver.term("distinct", p, r));
		mSolver.assertTerm(mSolver.term("distinct", hp1, hl2, hq3));
		Assert.assertEquals(LBool.SAT, mSolver.checkSat());
		final PiecewiseModel model = buildModel();
		final CCTerm rCC = mClausifier.getCCTerm(r);
		// p: own corner from a1 on, lambda corner from a2 on (p's corner has precedence for a1 only)
		assertCorner(model, hp1, p, mATerms[1]);
		Assert.assertEquals(mClausifier.getCCTerm(hp1),
				model.getCorner(h, new Value[] { value(model, p), value(model, mATerms[3]) }));
		// q: below a3 falls back to the lambda corner
		assertCorner(model, hq3, q, mATerms[3]);
		assertCorner(model, hl2, q, mATerms[2]);
		Assert.assertNull(model.getCorner(h, new Value[] { value(model, q), value(model, mATerms[1]) }));
		// r (no own corner unless r = q)
		if (rCC.getRepresentative() != mClausifier.getCCTerm(q).getRepresentative()) {
			assertCorner(model, hl2, r, mATerms[3]);
		}
		Assert.assertEquals(Value.lambda(u), value(model, lambdaU));
	}

	private Value intValue(final int i) {
		return Value.concrete(mInt, Rational.valueOf(i, 1));
	}

	private Term select(final Term array, final int index) {
		return mTheory.term("select", array, num(index));
	}

	/** Every select in the E-graph is a corner of the model of its array. */
	private void assertSelectsCovered(final PiecewiseModel model) {
		for (final CCTerm term : mClausifier.getCClosure().mAllTerms) {
			if (ArrayTheory.isSelectTerm(term)) {
				final CCAppTerm select = (CCAppTerm) term;
				final Value index = model.getValue(ArrayTheory.getIndexFromSelect(select));
				Assert.assertEquals(model.getValue(select),
						model.evaluateSelect(ArrayTheory.getArrayFromSelect(select), index));
			}
		}
	}

	/** Without stores the array is piecewise constant over its selects. */
	@Test
	public void testArraySelects() {
		final Sort arr = mSolver.sort("Array", mInt, mInt);
		final Term a = declare("arr", arr);
		mSolver.assertTerm(mSolver.term("=", select(a, 1), num(10)));
		mSolver.assertTerm(mSolver.term("=", select(a, 5), num(50)));
		mSolver.assertTerm(mSolver.term("=", mTheory.term("select", a, mLambda), num(-1)));
		Assert.assertEquals(LBool.SAT, mSolver.checkSat());
		final PiecewiseModel model = buildModel();
		final CCTerm aCC = mClausifier.getCCTerm(a);
		Assert.assertEquals(intValue(-1), model.evaluateSelect(aCC, Value.lambda(mInt)));
		Assert.assertEquals(intValue(-1), model.evaluateSelect(aCC, intValue(0)));
		Assert.assertEquals(intValue(10), model.evaluateSelect(aCC, intValue(1)));
		Assert.assertEquals(intValue(10), model.evaluateSelect(aCC, intValue(4)));
		Assert.assertEquals(intValue(50), model.evaluateSelect(aCC, intValue(5)));
		Assert.assertEquals(intValue(50), model.evaluateSelect(aCC, intValue(100)));
		assertSelectsCovered(model);
	}

	/** Stores change the model of the weak representative only at their index. */
	@Test
	public void testArrayStores() {
		final Sort arr = mSolver.sort("Array", mInt, mInt);
		final Term a = declare("arr", arr);
		final Term b = mTheory.term("store", a, num(3), num(30));
		final Term c = mTheory.term("store", b, num(5), num(7));
		final Term d = mTheory.term("store", mTheory.term("const", null, arr, num(4)), num(2), num(9));
		mSolver.assertTerm(mSolver.term("=", select(a, 1), num(10)));
		mSolver.assertTerm(mSolver.term("=", select(a, 5), num(50)));
		mSolver.assertTerm(mSolver.term("=", select(c, 8), num(80)));
		mSolver.assertTerm(mSolver.term("distinct", c, d));
		Assert.assertEquals(LBool.SAT, mSolver.checkSat());
		final PiecewiseModel model = buildModel();
		assertSelectsCovered(model);
		final CCTerm aCC = mClausifier.getCCTerm(a);
		final CCTerm bCC = mClausifier.getCCTerm(b);
		final CCTerm cCC = mClausifier.getCCTerm(c);
		final CCTerm dCC = mClausifier.getCCTerm(d);
		Assert.assertEquals(intValue(10), model.evaluateSelect(aCC, intValue(1)));
		Assert.assertEquals(intValue(50), model.evaluateSelect(aCC, intValue(5)));
		Assert.assertEquals(intValue(30), model.evaluateSelect(bCC, intValue(3)));
		Assert.assertEquals(intValue(7), model.evaluateSelect(cCC, intValue(5)));
		Assert.assertEquals(intValue(80), model.evaluateSelect(cCC, intValue(8)));
		Assert.assertEquals(intValue(9), model.evaluateSelect(dCC, intValue(2)));
		for (int i = -2; i < 12; i++) {
			final Value index = intValue(i);
			if (i != 3) {
				Assert.assertEquals(model.evaluateSelect(aCC, index), model.evaluateSelect(bCC, index));
			}
			if (i != 5) {
				Assert.assertEquals(model.evaluateSelect(bCC, index), model.evaluateSelect(cCC, index));
			}
			if (i != 2) {
				Assert.assertEquals(intValue(4), model.evaluateSelect(dCC, index));
			}
		}
		Assert.assertEquals(intValue(4), model.evaluateSelect(dCC, Value.lambda(mInt)));
	}
}
