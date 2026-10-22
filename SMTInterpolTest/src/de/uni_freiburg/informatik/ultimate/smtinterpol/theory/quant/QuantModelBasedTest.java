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
package de.uni_freiburg.informatik.ultimate.smtinterpol.theory.quant;

import java.io.StringReader;

import org.junit.Assert;
import org.junit.Rule;
import org.junit.Test;
import org.junit.rules.Timeout;
import org.junit.runner.RunWith;
import org.junit.runners.JUnit4;

import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.smtinterpol.DefaultLogger;
import de.uni_freiburg.informatik.ultimate.smtinterpol.option.OptionMap;
import de.uni_freiburg.informatik.ultimate.smtinterpol.smtlib2.ParseEnvironment;
import de.uni_freiburg.informatik.ultimate.smtinterpol.smtlib2.SMTInterpol;

/**
 * Tests for the model-based final check ({@code :quant-fc-method model_based}) with piecewise-constant models.
 *
 * @author Jochen Hoenicke
 */
@RunWith(JUnit4.class)
public class QuantModelBasedTest {

	/** Fails a test that hangs, e.g., in a loop that ignores the solver timeout. */
	@Rule
	public final Timeout mTimeout = Timeout.seconds(30);

	private static final String DECLS = "(set-logic AUFLIA)"
			+ "(declare-sort U 0)(declare-fun f (Int) Int)(declare-fun h (Int Int) Int)(declare-fun a () Int)"
			+ "(declare-fun b () Int)(declare-fun arr () (Array Int Int))(declare-fun P (U) Bool)"
			+ "(declare-fun Q (U) Bool)(declare-fun c () U)";

	private LBool check(final String asserts) {
		return check(10000, asserts);
	}

	private LBool check(final int timeout, final String asserts) {
		final OptionMap options = new OptionMap(new DefaultLogger(), true);
		final SMTInterpol script = new SMTInterpol(null, options);
		final String setup = "(set-option :quant-fc-method model_based)(set-option :timeout " + timeout + ")";
		new ParseEnvironment(script, options).parseStream(new StringReader(setup + DECLS + asserts), "test");
		return script.checkSat();
	}

	@Test
	public void testSatBelowBound() {
		Assert.assertEquals(LBool.SAT,
				check("(assert (forall ((x Int)) (or (< x a) (<= 0 (f x)))))(assert (= (f b) (- 1)))(assert (< b a))"));
	}

	@Test
	public void testUnsatAboveBound() {
		Assert.assertEquals(LBool.UNSAT,
				check("(assert (forall ((x Int)) (or (< x a) (<= 0 (f x)))))(assert (= (f (+ a 3)) (- 1)))"));
	}

	@Test
	public void testSatArray() {
		Assert.assertEquals(LBool.SAT, check("(assert (forall ((x Int)) (or (< x 0) (<= 0 (select arr x)))))"
				+ "(assert (= (select arr (- 1)) (- 5)))"));
	}

	@Test
	public void testUnsatArrayStore() {
		Assert.assertEquals(LBool.UNSAT, check("(assert (forall ((x Int)) (or (< x 0) (<= 0 (select arr x)))))"
				+ "(assert (= (select (store arr 3 (- 2)) b) (- 1)))(assert (<= 0 b))"));
	}

	@Test
	public void testSatUninterpretedSort() {
		Assert.assertEquals(LBool.SAT,
				check("(assert (forall ((x U)) (or (P x) (Q x))))(assert (not (P c)))(assert (forall ((x U)) "
						+ "(or (not (Q x)) (not (P x)))))"));
	}

	/**
	 * Satisfiable only with f(x) = x - 1, which is not piecewise constant; the old quantifier_models branch answered
	 * unsat (doc/piecewise-constant-models.md, "lambda in proofs"). Outside the solvable fragment, so the solver must
	 * stop with unknown, either at the timeout or because the model cannot decide all instances.
	 */
	@Test
	public void testNoWrongUnsat() {
		Assert.assertEquals(LBool.UNKNOWN,
				check(1000, "(assert (forall ((x Int) (y Int)) (or (< y x) (= (h x y) 1))))"
						+ "(assert (forall ((x Int)) (= (h x (f x)) 0)))"));
	}
}
