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

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.ConstantTerm;
import de.uni_freiburg.informatik.ultimate.logic.FormulaUnLet;
import de.uni_freiburg.informatik.ultimate.logic.FunctionSymbol;
import de.uni_freiburg.informatik.ultimate.logic.LambdaTerm;
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
	private SMTInterpol checkSatWithModel(final String asserts) {
		return checkSatWithModel(DECLS, asserts);
	}

	private SMTInterpol checkSatWithModel(final String decls, final String asserts) {
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
		return script;
	}

	/** Add the numeric constants in a value, including the indices and steps of array values. */
	private static void addPoint(final Set<Rational> points, final Term term) {
		if (term instanceof ConstantTerm && term.getSort().isNumericSort()) {
			points.add(NumericSortInterpretation.toRational(term));
		} else if (term instanceof ApplicationTerm) {
			for (final Term param : ((ApplicationTerm) term).getParameters()) {
				addPoint(points, param);
			}
		} else if (term instanceof LambdaTerm) {
			addPoint(points, ((LambdaTerm) term).getSubterm());
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
		checkSatWithModel("(assert (forall ((x Int)) (or (< x 0) (<= 0 (select arr x)))))"
				+ "(assert (= (select arr (- 1)) (- 5)))");
	}

	/** An array that is not a store chain over a const array, so it is printed with {@code .as-array}. */
	@Test
	public void testSatArraySteps() {
		final SMTInterpol script = checkSatWithModel("(assert (forall ((x Int)) (or (< x 3) (= (select arr x) 7))))"
				+ "(assert (= (select arr 1) 2))");
		Assert.assertTrue(script.getModel().toString().contains(".as-array"));
	}

	/** Stores on top of the weak representative, at an index in its step and below it. */
	@Test
	public void testSatArrayStore() {
		checkSatWithModel("(declare-fun arr2 () (Array Int Int))"
				+ "(assert (forall ((x Int)) (or (< x 3) (= (select arr x) 7))))"
				+ "(assert (= arr2 (store (store arr 5 0) a b)))(assert (< a 0))(assert (distinct (select arr a) b))");
	}

	private static final String REAL_ARRAY_DECLS = "(set-logic AUFLIRA)(declare-fun ra () (Array Real Real))"
			+ "(declare-fun rb () (Array Real Real))(declare-fun rc () (Array Real Real))(declare-fun r () Real)";

	/**
	 * Real indices, where a store is a point between steps. The store is on an array the quantifier does not select
	 * from, since the final check cannot decide the cell just above a store index (see
	 * {@link #testUnknownArrayRealStore()}).
	 */
	@Test
	public void testSatArrayReal() {
		checkSatWithModel(REAL_ARRAY_DECLS, "(assert (forall ((x Real)) (or (< x r) (< 1.5 (select ra x)))))"
				+ "(assert (= rb (store rc (- r 0.5) 0.0)))(assert (= (select rc (- r 1.0)) 0.0))"
				+ "(assert (= (select ra (- r 1.0)) 0.0))");
	}

	/**
	 * A store at a Real index of the selected array: the model is the weak representative's value just above the
	 * store index, which has no grid point without a symbolic {@code i + ε}, so the final check must not answer sat.
	 * The instance is satisfiable, but with the old check the model had ra = 0 above r + 0.5.
	 */
	@Test
	public void testUnknownArrayRealStore() {
		Assert.assertEquals(LBool.UNKNOWN,
				createScript(1000, REAL_ARRAY_DECLS + "(assert (forall ((x Real)) (or (< x r) (< 1.5 (select ra x)))))"
						+ "(assert (= rb (store ra (+ r 0.5) 0.0)))").checkSat());
	}

	/** A Real equality {@code x = t} has a point cell without grid point next to it, so the check answers unknown. */
	@Test
	public void testUnknownRealEquality() {
		Assert.assertEquals(LBool.UNKNOWN,
				createScript(1000, "(set-logic UFLRA)(declare-fun g (Real) Real)(declare-fun r () Real)"
						+ "(assert (forall ((x Real)) (or (= x r) (< 0.0 (g x)))))(assert (= (g r) (- 1.0)))")
								.checkSat());
	}

	/**
	 * The model is false for x = lambda (g is λ there), but the instance {@code λ + 5 < (g λ)} would put λ into
	 * linear arithmetic. It is not built (nor retried), so λ stays CC-only and the check answers unknown.
	 */
	@Test
	public void testLambdaNotInArithmetic() {
		final SMTInterpol script = createScript(1000, DECLS + "(declare-fun g (Int) Int)"
				+ "(assert (forall ((x Int)) (< (+ x 5) (g x))))(assert (= (g 0) 10))");
		Assert.assertEquals(LBool.UNKNOWN, script.checkSat());
		final Term lambda = script.getClausifier().getQuantifierTheory().getLambda(script.getTheory().getNumericSort());
		Assert.assertNull(script.getClausifier().getLATerm(lambda));
	}

	/**
	 * The model is false for x = lambda, but the instance would store at λ, which the array theory would compare with
	 * the other indices. It is not built, so there is no such store and the check answers unknown.
	 */
	@Test
	public void testLambdaNotStoreIndex() {
		final SMTInterpol script =
				createScript(1000, DECLS + "(assert (forall ((x Int)) (= (select (store arr x 1) b) 1)))"
						+ "(assert (= (select arr b) 0))(assert (= (select arr (+ b 1)) 0))");
		Assert.assertEquals(LBool.UNKNOWN, script.checkSat());
		final Theory theory = script.getTheory();
		final Term lambda = script.getClausifier().getQuantifierTheory().getLambda(theory.getNumericSort());
		Assert.assertNull(script.getClausifier().getCCTerm(theory.term("store", theory.term("arr"), lambda,
				theory.numeral("1"))));
	}

	/** An uninterpreted index sort, where the array is a store chain over the default. */
	@Test
	public void testSatArrayUninterpretedIndex() {
		checkSatWithModel("(declare-fun m () (Array U Int))(declare-fun d () U)"
				+ "(assert (forall ((u U)) (or (Q u) (<= 0 (select m u)))))"
				+ "(assert (= (select m c) (- 1)))(assert (not (Q d)))");
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
