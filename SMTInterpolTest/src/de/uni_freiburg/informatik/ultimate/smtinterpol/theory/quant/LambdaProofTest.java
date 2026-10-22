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
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.smtinterpol.DefaultLogger;
import de.uni_freiburg.informatik.ultimate.smtinterpol.option.OptionMap;
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

	private String proveUnsat(final String logic, final String input) {
		final OptionMap options = new OptionMap(new DefaultLogger(), true);
		final SMTInterpol script = new SMTInterpol(null, options);
		final String setup = "(set-option :produce-proofs true)(set-option :proof-check-mode true)"
				+ "(set-option :proof-level lowlevel)(set-logic " + logic + ")";
		new ParseEnvironment(script, options).parseStream(new StringReader(setup + input), "test");
		Assert.assertEquals(LBool.UNSAT, script.checkSat());
		final Term proof = script.getProof();
		final StringBuilder sb = new StringBuilder();
		new PrintProof().append(sb, proof);
		return sb.toString();
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
}
