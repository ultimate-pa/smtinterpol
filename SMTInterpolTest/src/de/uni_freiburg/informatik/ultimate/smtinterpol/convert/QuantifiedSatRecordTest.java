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
import java.util.IdentityHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;

import org.junit.Assert;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.JUnit4;

import de.uni_freiburg.informatik.ultimate.logic.QuantifiedFormula;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.smtinterpol.DefaultLogger;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.ILiteral;
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

	/**
	 * Check every entry of the ground clause records reachable from the assertions: its proof proves exactly
	 * {@code {~l} ∪ rest}, also after lowering, without oracles. Returns the number of ground clause records.
	 */
	private int checkGroundClauseRecords(final SMTInterpol script) {
		final Clausifier clausifier = script.getClausifier();
		final MinimalProofChecker checker = new MinimalProofChecker(script, script.getLogger());
		final Set<Clausifier.SatRecord> seen = java.util.Collections.newSetFromMap(new IdentityHashMap<>());
		final List<Clausifier.SatRecord> todo = new ArrayList<>(clausifier.mAssertionSatProofs.values());
		int count = 0;
		while (!todo.isEmpty()) {
			final Clausifier.SatRecord record = todo.remove(todo.size() - 1);
			if (!seen.add(record)) {
				continue;
			}
			if (record instanceof Clausifier.FormulaSatProof) {
				todo.addAll(Arrays.asList(((Clausifier.FormulaSatProof) record).mHyps));
				continue;
			}
			final Clausifier.ClauseSatProof csp = (Clausifier.ClauseSatProof) record;
			Assert.assertNotNull("incomplete clause record", csp.mLiterals);
			if (csp.mClosure != null) {
				continue;
			}
			count++;
			for (final Map.Entry<ILiteral, Clausifier.SatEntry> e : csp.mLiterals.entrySet()) {
				final Clausifier.SatEntry entry = e.getValue();
				if (entry.mProof == null) {
					continue;
				}
				final Set<ProofLiteral> expected = new HashSet<>(Arrays.asList(entry.getRest(csp.mTarget)));
				expected.add(Clausifier.toProofLiteral(e.getKey().getSMTFormula(script.getTheory())).negate());
				Assert.assertEquals(expected, new HashSet<>(Arrays.asList(checker.getProvedClause(entry.mProof))));
				final Term lowered = new ProofSimplifier(script).transformProof(entry.mProof);
				Assert.assertEquals(expected, new HashSet<>(Arrays.asList(checker.getProvedClause(lowered))));
				Assert.assertFalse("oracle in lowered proof", lowered.toStringDirect().contains("oracle"));
			}
		}
		return count;
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

	@Test
	public void testDERKeepsVariable() {
		// DER eliminates x := (f y); the clause keeps y
		Assert.assertEquals(1, checkAssertions(
				parse("(assert (forall ((x Int) (y Int)) (or (not (= x (f y))) (P x) (Q y))))")));
	}

	@Test
	public void testDERChain() {
		// DER eliminates x and y through a chain of disequalities
		Assert.assertEquals(1, checkAssertions(parse(
				"(assert (forall ((x Int) (y Int) (z Int)) (or (not (= x y)) (not (= y (f z))) (R x z) (Q y))))")));
	}

	@Test
	public void testDERNestedDrop() {
		// the nested forall is dropped with a fresh variable, which DER then eliminates
		Assert.assertEquals(1, checkAssertions(
				parse("(assert (forall ((x Int)) (or (forall ((y Int)) (or (not (= y (f x))) (R x y))) (P x))))")));
	}

	@Test
	public void testDERGround() {
		// DER eliminates all variables: the clause becomes ground, an ordinary DPLL clause
		final SMTInterpol script = parse(
				"(assert (forall ((x Int)) (or (not (= x 5)) (P x) (= (g x x) 3))))"
						+ "(assert (forall ((x Int) (y Int)) (or (not (= x 5)) (not (= y (f x))) (R x y))))");
		Assert.assertEquals(2, checkGroundClauseRecords(script));
	}

	/**
	 * Check the ready-made proofs of all trivially true clause records reachable from the assertions: each proves
	 * exactly its clause, a subclause of the target, also after lowering, without oracles. Returns their number.
	 */
	private int checkReadyMadeRecords(final SMTInterpol script) {
		final Clausifier clausifier = script.getClausifier();
		final MinimalProofChecker checker = new MinimalProofChecker(script, script.getLogger());
		final Set<Clausifier.SatRecord> seen = java.util.Collections.newSetFromMap(new IdentityHashMap<>());
		final List<Clausifier.SatRecord> todo = new ArrayList<>(clausifier.mAssertionSatProofs.values());
		todo.addAll(clausifier.mLiteralSatProofs.values());
		int count = 0;
		while (!todo.isEmpty()) {
			final Clausifier.SatRecord record = todo.remove(todo.size() - 1);
			if (!seen.add(record)) {
				continue;
			}
			if (record instanceof Clausifier.FormulaSatProof) {
				for (final Clausifier.SatRecord hyp : ((Clausifier.FormulaSatProof) record).mHyps) {
					if (hyp != null) {
						todo.add(hyp);
					}
				}
				continue;
			}
			final Clausifier.ClauseSatProof csp = (Clausifier.ClauseSatProof) record;
			if (csp.mReadyMadeProof == null) {
				continue;
			}
			count++;
			final Set<ProofLiteral> expected = new HashSet<>(Arrays.asList(csp.mReadyMadeClause));
			Assert.assertTrue("not a subclause of the target",
					new HashSet<>(Arrays.asList(csp.mTarget)).containsAll(expected));
			Assert.assertEquals(expected, new HashSet<>(Arrays.asList(checker.getProvedClause(csp.mReadyMadeProof))));
			final Term lowered = new ProofSimplifier(script).transformProof(csp.mReadyMadeProof);
			Assert.assertEquals(expected, new HashSet<>(Arrays.asList(checker.getProvedClause(lowered))));
			Assert.assertFalse("oracle in lowered proof", lowered.toStringDirect().contains("oracle"));
		}
		return count;
	}

	@Test
	public void testTrivialGroundPair() {
		// (= c d) and (not (= d c)) only become complementary as literals (the same CC equality)
		Assert.assertEquals(1, checkReadyMadeRecords(
				parse("(declare-fun c () Int)(declare-fun d () Int)(assert (or (= c d) (not (= d c)) (P c)))")));
	}

	@Test
	public void testTrivialSimplifiedToTrue() {
		// the TermCompiler already simplifies the formula to true; the clause is the literal true
		Assert.assertEquals(1, checkReadyMadeRecords(
				parse("(declare-fun c () Int)(assert (or (< c 0) (P c) (>= c 0)))")));
	}

	@Test
	public void testTrivialQuantifiedSimplifiedToTrue() {
		Assert.assertEquals(1, checkReadyMadeRecords(
				parse("(assert (forall ((x Int)) (or (< (f x) 0) (P x) (>= (f x) 0))))")));
	}

	@Test
	public void testTrivialAfterDERPair() {
		// DER x := 5 turns (P x) into the negation of (not (P 5))
		Assert.assertEquals(1, checkReadyMadeRecords(
				parse("(assert (forall ((x Int)) (or (not (= x 5)) (P x) (not (P 5)))))")));
	}

	@Test
	public void testTrivialAfterDERTrue() {
		// DER x := 5 turns (= (f x) (f 5)) into true
		Assert.assertEquals(1, checkReadyMadeRecords(
				parse("(assert (forall ((x Int)) (or (not (= x 5)) (= (f x) (f 5)) (P x))))")));
	}
}
