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
import java.util.ArrayDeque;
import java.util.HashSet;
import java.util.Set;

import org.junit.Assert;
import org.junit.Rule;
import org.junit.Test;
import org.junit.rules.Timeout;
import org.junit.runner.RunWith;
import org.junit.runners.JUnit4;

import de.uni_freiburg.informatik.ultimate.logic.AnnotatedTerm;
import de.uni_freiburg.informatik.ultimate.logic.Annotation;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.SMTLIBException;
import de.uni_freiburg.informatik.ultimate.logic.SMTLIBConstants;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.smtinterpol.DefaultLogger;
import de.uni_freiburg.informatik.ultimate.smtinterpol.option.OptionMap;
import de.uni_freiburg.informatik.ultimate.smtinterpol.option.SMTInterpolConstants;
import de.uni_freiburg.informatik.ultimate.smtinterpol.proof.ProofConstants;
import de.uni_freiburg.informatik.ultimate.smtinterpol.proof.resolute.PrintProof;
import de.uni_freiburg.informatik.ultimate.smtinterpol.smtlib2.ParseEnvironment;
import de.uni_freiburg.informatik.ultimate.smtinterpol.smtlib2.SMTInterpol;

/**
 * Tests for instances with λ whose comparisons with λ-free terms are decided by smallness of λ. The low-level proof
 * then defines λ below all bounds, and the proof check mode checks it.
 *
 * @author Jochen Hoenicke
 */
@RunWith(JUnit4.class)
public class LambdaProofTest {

	/** Fails a test that hangs, e.g., in a loop that ignores the solver timeout. */
	@Rule
	public final Timeout mTimeout = Timeout.seconds(30);

	private Term getProof(final String proofLevel, final String logic, final String input) {
		final OptionMap options = new OptionMap(new DefaultLogger(), true);
		final SMTInterpol script = new SMTInterpol(null, options);
		final String setup = "(set-option :produce-proofs true)(set-option :proof-check-mode true)"
				+ "(set-option :proof-level " + proofLevel + ")(set-logic " + logic + ")";
		new ParseEnvironment(script, options).parseStream(new StringReader(setup + input), "test");
		Assert.assertEquals(LBool.UNSAT, script.checkSat());
		return script.getProof();
	}

	private String proveUnsat(final String logic, final String input) {
		final StringBuilder sb = new StringBuilder();
		new PrintProof().append(sb, getProof("lowlevel", logic, input));
		return sb.toString();
	}

	/**
	 * Check that the full proof rewrites an equality with λ to false, so that the low-level proof must prove it from
	 * the definition of λ.
	 */
	private void assertLambdaEqualityRewrite(final String logic, final String input) {
		final ArrayDeque<Term> todo = new ArrayDeque<>();
		final Set<Term> seen = new HashSet<>();
		todo.add(getProof("full", logic, input));
		while (!todo.isEmpty()) {
			final Term t = todo.removeLast();
			if (!seen.add(t)) {
				continue;
			}
			if (t instanceof AnnotatedTerm) {
				final AnnotatedTerm annot = (AnnotatedTerm) t;
				if (annot.getAnnotations()[0].getKey().equals(ProofConstants.RW_LAMBDA_BOUND.getKey())
						&& annot.getSubterm() instanceof ApplicationTerm && ((ApplicationTerm) annot.getSubterm())
								.getFunction().getName().equals(SMTLIBConstants.EQUALS)) {
					return;
				}
				todo.add(annot.getSubterm());
				for (final Annotation a : annot.getAnnotations()) {
					addTerms(todo, a.getValue());
				}
			} else if (t instanceof ApplicationTerm) {
				for (final Term p : ((ApplicationTerm) t).getParameters()) {
					todo.add(p);
				}
			}
		}
		Assert.fail("no :lambdaBound rewrite of an equality");
	}

	/** Add the terms in an annotation value, e.g., the subproof of an instantiation. */
	private static void addTerms(final ArrayDeque<Term> todo, final Object value) {
		if (value instanceof Term) {
			todo.add((Term) value);
		} else if (value instanceof Object[]) {
			for (final Object v : (Object[]) value) {
				addTerms(todo, v);
			}
		}
	}

	@Test
	public void testIntBound() {
		final String proof = proveUnsat("UFLIA", "(declare-fun P (Int) Bool)(declare-fun a () Int)"
				+ "(declare-fun b () Int)(assert (forall ((x Int)) (or (<= a x) (P x))))"
				+ "(assert (forall ((x Int)) (or (<= (* 2 b) (* 3 x)) (not (P x)))))");
		Assert.assertTrue(proof.contains("(define-fun @lambda ()"));
	}

	@Test
	public void testRealFractionalBound() {
		final String proof = proveUnsat("UFLRA", "(declare-fun P (Real) Bool)(declare-fun a () Real)"
				+ "(declare-fun b () Real)(assert (forall ((x Real)) (or (<= a (* (/ 1 3) x)) (P x))))"
				+ "(assert (forall ((x Real)) (or (<= (* 2 b) (* 5 x)) (not (P x)))))");
		Assert.assertTrue(proof.contains("(define-fun @lambda ()"));
	}

	@Test
	public void testUninterpretedLambda() {
		final String proof = proveUnsat("UFLIA", "(declare-sort U 0)(declare-fun Q (U) Bool)"
				+ "(declare-fun P (Int) Bool)(declare-fun a () Int)"
				+ "(assert (forall ((u U) (x Int)) (or (<= a x) (and (Q u) (P x)))))"
				+ "(assert (forall ((u U)) (not (Q u))))");
		Assert.assertTrue(proof.contains("(as @lambda U)"));
	}

	/** Equality with positive coefficient c > 1, proved via symm. */
	@Test
	public void testIntEqualityPositive() {
		final String input = "(declare-fun P (Int) Bool)(declare-fun a () Int)"
				+ "(assert (forall ((x Int)) (or (= (* 2 x) a) (P x))))(assert (forall ((x Int)) (not (P x))))";
		assertLambdaEqualityRewrite("UFLIA", input);
		Assert.assertTrue(proveUnsat("UFLIA", input).contains("(define-fun @lambda ()"));
	}

	/** Equality with negative coefficient of λ. */
	@Test
	public void testIntEqualityNegative() {
		final String input = "(declare-fun P (Int) Bool)(declare-fun a () Int)"
				+ "(assert (forall ((x Int)) (or (= (* (- 3) x) a) (P x))))(assert (forall ((x Int)) (not (P x))))";
		assertLambdaEqualityRewrite("UFLIA", input);
		Assert.assertTrue(proveUnsat("UFLIA", input).contains("(define-fun @lambda ()"));
	}

	/** Equality on the left side, normalized as {@code (= a (* 2 λ))}. */
	@Test
	public void testIntEqualitySwapped() {
		final String input = "(declare-fun P (Int) Bool)(declare-fun a () Int)"
				+ "(assert (forall ((x Int)) (or (= a (* 2 x)) (P x))))(assert (forall ((x Int)) (not (P x))))";
		assertLambdaEqualityRewrite("UFLIA", input);
		Assert.assertTrue(proveUnsat("UFLIA", input).contains("(define-fun @lambda ()"));
	}

	@Test
	public void testRealEquality() {
		final String input = "(declare-fun P (Real) Bool)(declare-fun a () Real)"
				+ "(assert (forall ((x Real)) (or (= x a) (P x))))(assert (forall ((x Real)) (not (P x))))";
		assertLambdaEqualityRewrite("UFLRA", input);
		Assert.assertTrue(proveUnsat("UFLRA", input).contains("(define-fun @lambda ()"));
	}

	/** λ is internal to the solver, so the parser accepts it (e.g., for proofs) but the input must not contain it. */
	@Test
	public void testRejectLambdaInput() {
		final SMTInterpol script = new SMTInterpol(null, new OptionMap(new DefaultLogger(), true));
		script.setLogic("UFLIA");
		final Sort intSort = script.sort(SMTLIBConstants.INT);
		script.declareFun("P", new Sort[] { intSort }, script.sort(SMTLIBConstants.BOOL));
		final Term lambda = script.term(SMTInterpolConstants.LAMBDA, null, intSort);
		final Term pLambda = script.term("P", lambda);
		try {
			script.assertTerm(pLambda);
			Assert.fail("@lambda accepted in assertion");
		} catch (final SMTLIBException expected) {
			Assert.assertTrue(expected.getMessage().contains(SMTInterpolConstants.LAMBDA));
		}
		try {
			script.checkAllsat(new Term[] { pLambda });
			Assert.fail("@lambda accepted in all-sat input");
		} catch (final SMTLIBException expected) {
			Assert.assertTrue(expected.getMessage().contains(SMTInterpolConstants.LAMBDA));
		}
	}
}
