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
import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.Set;
import java.util.TreeSet;

import org.junit.Assert;
import org.junit.Rule;
import org.junit.Test;
import org.junit.rules.Timeout;
import org.junit.runner.RunWith;
import org.junit.runners.JUnit4;

import de.uni_freiburg.informatik.ultimate.logic.ConstantTerm;
import de.uni_freiburg.informatik.ultimate.logic.FormulaUnLet;
import de.uni_freiburg.informatik.ultimate.logic.FunctionSymbol;
import de.uni_freiburg.informatik.ultimate.logic.QuantifiedFormula;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.logic.Theory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.DefaultLogger;
import de.uni_freiburg.informatik.ultimate.smtinterpol.model.FiniteSortInterpretation;
import de.uni_freiburg.informatik.ultimate.smtinterpol.model.FunctionValue;
import de.uni_freiburg.informatik.ultimate.smtinterpol.model.Model;
import de.uni_freiburg.informatik.ultimate.smtinterpol.model.NumericSortInterpretation;
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
		return createScript(timeout, DECLS + asserts).checkSat();
	}

	private SMTInterpol createScript(final int timeout, final String input) {
		final OptionMap options = new OptionMap(new DefaultLogger(), true);
		final SMTInterpol script = new SMTInterpol(null, options);
		final String setup = "(set-option :produce-models true)(set-option :interactive-mode true)"
				+ "(set-option :quant-fc-method model_based)"
				+ "(set-option :timeout " + timeout + ")";
		new ParseEnvironment(script, options).parseStream(new StringReader(setup + input), "test");
		return script;
	}

	/**
	 * Check that the assertions are satisfiable and that the model satisfies them. A quantified assertion is checked
	 * at all combinations of candidate values: for numeric variables every step coordinate, function value and
	 * constant of the model, plus and minus one (and one half for Real), and a value below all of them; for an
	 * uninterpreted sort every element. As the functions are piecewise constant with steps at the coordinates, this
	 * covers every cell.
	 */
	private void checkSatWithModel(final String asserts) {
		checkSatWithModel(DECLS, asserts);
	}

	private void checkSatWithModel(final String decls, final String asserts) {
		final SMTInterpol script = createScript(10000, decls + asserts);
		Assert.assertEquals(LBool.SAT, script.checkSat());
		final Model model = (Model) script.getModel();
		final Theory theory = script.getTheory();
		final TreeSet<Rational> points = new TreeSet<>();
		for (final FunctionSymbol fs : model.getDefinedFunctions()) {
			final FunctionValue value = model.getFunctionValue(fs);
			addPoint(points, value.getDefault());
			for (final FunctionValue.Step step : value.getSteps()) {
				addPoint(points, step.getValue());
				for (final Term coordinate : step.getCoordinates()) {
					addPoint(points, coordinate);
				}
			}
		}
		for (final Term assertion : script.getAssertions()) {
			final Term term = new FormulaUnLet().unlet(assertion);
			if (term instanceof QuantifiedFormula) {
				final QuantifiedFormula qf = (QuantifiedFormula) term;
				Assert.assertEquals(QuantifiedFormula.FORALL, qf.getQuantifier());
				final TermVariable[] vars = qf.getVariables();
				final List<List<Term>> candidates = new ArrayList<>();
				for (final TermVariable var : vars) {
					candidates.add(getCandidates(model, var.getSort(), points));
				}
				checkInstances(model, qf, candidates, new Term[vars.length], 0);
			} else {
				Assert.assertEquals(assertion.toString(), theory.mTrue, model.evaluate(term));
			}
		}
	}

	private static void addPoint(final Set<Rational> points, final Term term) {
		if (term instanceof ConstantTerm && term.getSort().isNumericSort()) {
			points.add(NumericSortInterpretation.toRational(term));
		}
	}

	private static List<Term> getCandidates(final Model model, final Sort sort, final TreeSet<Rational> points) {
		final List<Term> candidates = new ArrayList<>();
		if (sort.isNumericSort()) {
			final Set<Rational> values = new TreeSet<>();
			values.add(points.isEmpty() ? Rational.ZERO : points.first().sub(Rational.TWO));
			final boolean isInt = sort.getName().equals("Int");
			final Rational half = Rational.valueOf(1, 2);
			for (final Rational p : points) {
				if (isInt && !p.isIntegral()) {
					values.add(p.floor());
					values.add(p.ceil());
					continue;
				}
				values.add(p);
				values.add(p.sub(Rational.ONE));
				values.add(p.add(Rational.ONE));
				if (!isInt) {
					values.add(p.sub(half));
					values.add(p.add(half));
				}
			}
			for (final Rational value : values) {
				candidates.add(value.toTerm(sort));
			}
		} else if (sort == sort.getTheory().getBooleanSort()) {
			candidates.add(sort.getTheory().mTrue);
			candidates.add(sort.getTheory().mFalse);
		} else {
			candidates.addAll(((FiniteSortInterpretation) model.provideSortInterpretation(sort)).getValues());
		}
		return candidates;
	}

	private static void checkInstances(final Model model, final QuantifiedFormula qf,
			final List<List<Term>> candidates, final Term[] values, final int pos) {
		if (pos == values.length) {
			final Theory theory = qf.getTheory();
			final Term instance = theory.let(qf.getVariables(), values.clone(), qf.getSubformula());
			Assert.assertEquals(qf + " at " + Arrays.toString(values), theory.mTrue, model.evaluate(instance));
			return;
		}
		for (final Term value : candidates.get(pos)) {
			values[pos] = value;
			checkInstances(model, qf, candidates, values, pos + 1);
		}
	}

	@Test
	public void testSatBelowBound() {
		checkSatWithModel("(assert (forall ((x Int)) (or (< x a) (<= 0 (f x)))))(assert (= (f b) (- 1)))(assert (< b a))");
	}

	@Test
	public void testUnsatAboveBound() {
		Assert.assertEquals(LBool.UNSAT,
				check("(assert (forall ((x Int)) (or (< x a) (<= 0 (f x)))))(assert (= (f (+ a 3)) (- 1)))"));
	}

	@Test
	public void testSatArray() {
		final SMTInterpol script = createScript(10000, DECLS + "(assert (forall ((x Int)) (or (< x 0) "
				+ "(<= 0 (select arr x)))))(assert (= (select arr (- 1)) (- 5)))");
		Assert.assertEquals(LBool.SAT, script.checkSat());
		// the piecewise-constant model of an array is not a store chain yet (Step 4c)
		try {
			script.getModel();
			Assert.fail("model with arrays");
		} catch (final UnsupportedOperationException expected) {
			// expected
		}
	}

	@Test
	public void testUnsatArrayStore() {
		Assert.assertEquals(LBool.UNSAT, check("(assert (forall ((x Int)) (or (< x 0) (<= 0 (select arr x)))))"
				+ "(assert (= (select (store arr 3 (- 2)) b) (- 1)))(assert (<= 0 b))"));
	}

	@Test
	public void testSatUninterpretedSort() {
		checkSatWithModel("(assert (forall ((x U)) (or (P x) (Q x))))(assert (not (P c)))(assert (forall ((x U)) "
				+ "(or (not (Q x)) (not (P x)))))");
	}

	/**
	 * The values of f at the CC-only classes {@code (f c)}, {@code (f d)} are compared with lambda and with each other
	 * through sums, so their concrete values must keep the order and the gaps the final check assumed.
	 */
	@Test
	public void testSatCCOnlyValues() {
		checkSatWithModel("(assert (forall ((x Int)) (or (< x a) (< (f x) (h x x)))))"
				+ "(assert (forall ((x Int)) (<= (* 2 (h x 0)) (+ (f b) 7))))(assert (distinct (f a) (f b)))");
	}

	/** Real arguments and values, where steps are not at integral points. */
	@Test
	public void testSatReal() {
		checkSatWithModel("(set-logic UFLRA)(declare-fun g (Real) Real)(declare-fun r () Real)", "(assert (forall ((x Real)) (or (< x r) (< (+ (g x) 1.5) r))))(assert (< (g (- r 0.5)) (g r)))");
	}

	/** A function with an uninterpreted and a numeric argument, with steps that differ per element. */
	@Test
	public void testSatMixedArguments() {
		checkSatWithModel("(declare-fun d () U)(declare-fun k (U Int) Int)"
				+ "(assert (forall ((u U) (x Int)) (or (P u) (< x 3) (= (k u x) 5))))"
				+ "(assert (= (k c 4) 2))(assert (not (P d)))");
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
