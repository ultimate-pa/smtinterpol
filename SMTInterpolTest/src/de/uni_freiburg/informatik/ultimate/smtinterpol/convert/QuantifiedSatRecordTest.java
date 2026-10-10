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
package de.uni_freiburg.informatik.ultimate.smtinterpol.convert;

import java.io.StringReader;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import org.junit.Assert;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.JUnit4;

import de.uni_freiburg.informatik.ultimate.logic.QuantifiedFormula;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.smtinterpol.DefaultLogger;
import de.uni_freiburg.informatik.ultimate.smtinterpol.option.OptionMap;
import de.uni_freiburg.informatik.ultimate.smtinterpol.proof.ProofSimplifier;
import de.uni_freiburg.informatik.ultimate.smtinterpol.proof.resolute.MinimalProofChecker;
import de.uni_freiburg.informatik.ultimate.smtinterpol.proof.resolute.ProofLiteral;
import de.uni_freiburg.informatik.ultimate.smtinterpol.smtlib2.ParseEnvironment;
import de.uni_freiburg.informatik.ultimate.smtinterpol.smtlib2.SMTInterpol;

/**
 * Tests "half 1" of the sat records of quantified assertions (SMTInterpol/doc/model-proof-plan.md, "Quantified
 * clauses and free variables"): the record of a quantified assertion must prove the assertion from the universal
 * closures of its quantified clauses, without the model. Proving the closures themselves from the model (half 2) is
 * open, so the closures are kept as hypotheses here.
 *
 * @author Jochen Hoenicke
 */
@RunWith(JUnit4.class)
public class QuantifiedSatRecordTest {

	private static final String DECLS = "(set-option :produce-proofs true)(set-option :model-proof-mode clauses)"
			+ "(set-logic UFLIA)(declare-fun f (Int) Int)(declare-fun g (Int Int) Int)(declare-fun P (Int) Bool)"
			+ "(declare-fun Q (Int) Bool)(declare-fun R (Int Int) Bool)";

	private SMTInterpol parse(final String asserts) {
		final OptionMap options = new OptionMap(new DefaultLogger(), true);
		final SMTInterpol script = new SMTInterpol(null, options);
		new ParseEnvironment(script, options).parseStream(new StringReader(DECLS + asserts), "test");
		return script;
	}

	/** Check the records of all assertions; returns the number of closures used. */
	private int checkAssertions(final SMTInterpol script) {
		final Clausifier clausifier = script.getClausifier();
		final ModelProofBuilder builder = new ModelProofBuilder(clausifier, null);
		builder.setKeepClosures(true);
		final MinimalProofChecker checker = new MinimalProofChecker(script, script.getLogger());
		final List<Term> assertions = new ArrayList<>(clausifier.mAssertionSatProofs.keySet());
		Assert.assertFalse(assertions.isEmpty());
		int closures = 0;
		for (final Term assertion : assertions) {
			final Set<ProofLiteral> clause = new HashSet<>();
			final Term proof = builder.proveAssertionKeepingClosures(assertion, clause);
			Assert.assertNotNull("incomplete record for " + assertion, proof);
			for (final ProofLiteral lit : clause) {
				if (!lit.equals(Clausifier.toProofLiteral(assertion))) {
					Assert.assertFalse("unexpected literal " + lit, lit.getPolarity());
					Assert.assertTrue("unexpected literal " + lit, lit.getAtom() instanceof QuantifiedFormula);
					closures++;
				}
			}
			Assert.assertTrue(clause.contains(Clausifier.toProofLiteral(assertion)));
			final Set<ProofLiteral> proved = new HashSet<>(Arrays.asList(checker.getProvedClause(proof)));
			Assert.assertEquals(clause, proved);
			final Term lowered = new ProofSimplifier(script).transformProof(proof);
			final Set<ProofLiteral> provedLow = new HashSet<>(Arrays.asList(checker.getProvedClause(lowered)));
			Assert.assertEquals(clause, provedLow);
			Assert.assertFalse("oracle in lowered proof", lowered.toStringDirect().contains("oracle"));
		}
		return closures;
	}

	@Test
	public void testForallOr() {
		Assert.assertEquals(1, checkAssertions(parse("(assert (forall ((x Int)) (or (P x) (Q x))))")));
	}

	@Test
	public void testForallImplies() {
		Assert.assertEquals(1, checkAssertions(parse("(assert (forall ((x Int)) (=> (P x) (> (f x) 0))))")));
	}

	@Test
	public void testForallAndSplit() {
		// split below the top-level forall: two quantified clauses
		Assert.assertEquals(2,
				checkAssertions(parse("(assert (forall ((x Int)) (and (P x) (or (Q x) (= (f x) 3)))))")));
	}

	@Test
	public void testNestedExistsSkolemized() {
		Assert.assertEquals(1, checkAssertions(
				parse("(assert (forall ((x Int)) (or (exists ((y Int)) (> (g x y) 0)) (P x))))")));
	}

	@Test
	public void testNestedForallDropped() {
		Assert.assertEquals(1,
				checkAssertions(parse("(assert (forall ((x Int)) (or (forall ((y Int)) (R x y)) (Q x))))")));
	}

	@Test
	public void testNegatedExistsDropped() {
		Assert.assertEquals(1, checkAssertions(
				parse("(assert (forall ((x Int)) (or (not (exists ((y Int)) (= (g x y) 0))) (P x))))")));
	}

	@Test
	public void testNegatedForallSkolemized() {
		Assert.assertEquals(1, checkAssertions(
				parse("(assert (forall ((x Int)) (or (not (forall ((y Int)) (> (g x y) 0))) (P x))))")));
	}

	@Test
	public void testQuantifiedAuxLiteral() {
		Assert.assertEquals(1, checkAssertions(
				parse("(assert (forall ((x Int)) (or (and (P x) (Q x)) (> (f x) 0) (= (f x) (- 5)))))")));
	}
}
