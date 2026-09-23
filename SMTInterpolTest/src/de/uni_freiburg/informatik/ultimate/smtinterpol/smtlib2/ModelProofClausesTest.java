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
package de.uni_freiburg.informatik.ultimate.smtinterpol.smtlib2;

import org.junit.Assert;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.JUnit4;

import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.smtinterpol.DefaultLogger;
import de.uni_freiburg.informatik.ultimate.smtinterpol.proof.resolute.MinimalProofChecker;

/**
 * End-to-end tests for Phase 1 of the model-proof plan
 * (SMTInterpol/doc/model-proof-plan.md): with {@code :model-proof-mode
 * clauses}, {@code get-proof} on a SAT result should produce a proof that
 * {@link MinimalProofChecker#checkModelProof} accepts with no remaining
 * oracles, for quantifier-free inputs without aux literals (propositional
 * and/or/=> splits over CC/LA atoms).
 *
 * @author Jochen Hoenicke
 */
@RunWith(JUnit4.class)
public class ModelProofClausesTest {

	private SMTInterpol newScript() {
		final SMTInterpol script = new SMTInterpol(new DefaultLogger());
		script.setOption(":produce-models", true);
		script.setOption(":interactive-mode", true);
		script.setOption(":produce-proofs", true);
		script.setOption(":proof-level", "full");
		script.setOption(":model-proof-mode", "clauses");
		return script;
	}

	private void checkSatAndProof(final SMTInterpol script) {
		Assert.assertEquals(LBool.SAT, script.checkSat());
		final Term proof = script.getProof();
		final MinimalProofChecker checker = new MinimalProofChecker(script, script.getLogger());
		// The reversed-rewrite/tautology steps built via ProofTracker aren't (yet) run
		// through ProofSimplifier for :model-proof-mode clauses (see SMTInterpol.getProof),
		// so a few :rewriteRev oracles may legitimately remain; checkModelProof still
		// accepts them (same as it accepts theory-axiom oracles elsewhere).
		Assert.assertTrue("checkModelProof", checker.checkModelProof(proof));
	}

	@Test
	public void testConjunctionWithNegatedConjunct() {
		final SMTInterpol s = newScript();
		s.setLogic("QF_UFLIA");
		final Sort intSort = s.sort("Int");
		final Sort boolSort = s.sort("Bool");
		s.declareFun("x", Script.EMPTY_SORT_ARRAY, intSort);
		s.declareFun("y", Script.EMPTY_SORT_ARRAY, intSort);
		s.declareFun("p", Script.EMPTY_SORT_ARRAY, boolSort);
		final Term x = s.term("x"), y = s.term("y"), p = s.term("p");
		s.assertTerm(s.term("and", s.term("<=", x, y), s.term("not", s.term("=", x, y)), p));
		checkSatAndProof(s);
	}

	@Test
	public void testNegatedOr() {
		final SMTInterpol s = newScript();
		s.setLogic("QF_UFLIA");
		final Sort intSort = s.sort("Int");
		s.declareFun("x", Script.EMPTY_SORT_ARRAY, intSort);
		s.declareFun("y", Script.EMPTY_SORT_ARRAY, intSort);
		final Term x = s.term("x"), y = s.term("y");
		// not (x > y or x = y)  ==  x <= y and x != y
		s.assertTerm(s.term("not", s.term("or", s.term(">", x, y), s.term("=", x, y))));
		checkSatAndProof(s);
	}

	@Test
	public void testNegatedImplies() {
		final SMTInterpol s = newScript();
		s.setLogic("QF_UFLIA");
		final Sort intSort = s.sort("Int");
		final Sort boolSort = s.sort("Bool");
		s.declareFun("x", Script.EMPTY_SORT_ARRAY, intSort);
		s.declareFun("p", Script.EMPTY_SORT_ARRAY, boolSort);
		final Term x = s.term("x"), p = s.term("p");
		// not (p => x > 0)  ==  p and x <= 0
		s.assertTerm(s.term("not", s.term("=>", p, s.term(">", x, s.numeral("0")))));
		checkSatAndProof(s);
	}

	@Test
	public void testMultipleAssertions() {
		final SMTInterpol s = newScript();
		s.setLogic("QF_UFLIA");
		final Sort intSort = s.sort("Int");
		s.declareFun("x", Script.EMPTY_SORT_ARRAY, intSort);
		s.declareFun("y", Script.EMPTY_SORT_ARRAY, intSort);
		final Term x = s.term("x"), y = s.term("y");
		s.assertTerm(s.term("<=", x, y));
		s.assertTerm(s.term("not", s.term("=", x, y)));
		// >= compiles to a negatively-interned LA literal: exercises the polarity
		// handling in ModelProofBuilder.proveFromLiterals.
		s.assertTerm(s.term(">=", y, s.numeral("0")));
		checkSatAndProof(s);
	}

	@Test
	public void testNestedAndInsideNegatedOr() {
		final SMTInterpol s = newScript();
		s.setLogic("QF_UFLIA");
		final Sort intSort = s.sort("Int");
		s.declareFun("x", Script.EMPTY_SORT_ARRAY, intSort);
		s.declareFun("y", Script.EMPTY_SORT_ARRAY, intSort);
		s.declareFun("z", Script.EMPTY_SORT_ARRAY, intSort);
		final Term x = s.term("x"), y = s.term("y"), z = s.term("z");
		s.assertTerm(s.term("and", s.term("<=", x, y),
				s.term("and", s.term("<=", y, z), s.term("not", s.term("=", x, z)))));
		checkSatAndProof(s);
	}

	@Test
	public void testNegatedOrWithNegatedDisjunct() {
		final SMTInterpol s = newScript();
		s.setLogic("QF_UFLIA");
		final Sort intSort = s.sort("Int");
		s.declareFun("x", Script.EMPTY_SORT_ARRAY, intSort);
		s.declareFun("y", Script.EMPTY_SORT_ARRAY, intSort);
		final Term x = s.term("x"), y = s.term("y");
		// a disjunct that is itself negated: exercises the "double not" case in
		// AddAsAxiom's or-negative child bridging.
		s.assertTerm(s.term("not", s.term("or", s.term(">", x, y), s.term("not", s.term("=", x, y)))));
		checkSatAndProof(s);
	}

	@Test
	public void testDnfWithConjunctiveDisjuncts() {
		final SMTInterpol s = newScript();
		s.setLogic("QF_UFLIA");
		final Sort intSort = s.sort("Int");
		s.declareFun("a", Script.EMPTY_SORT_ARRAY, intSort);
		s.declareFun("b", Script.EMPTY_SORT_ARRAY, intSort);
		s.declareFun("c", Script.EMPTY_SORT_ARRAY, intSort);
		s.declareFun("d", Script.EMPTY_SORT_ARRAY, intSort);
		final Term a = s.term("a"), b = s.term("b"), c = s.term("c"), d = s.term("d");
		// A DNF top-level clause (or (and ...) (and ...)): AddAsAxiom hands the top "or"
		// to buildClause, and each "and" disjunct is not inline-eligible (only a
		// negative "and" or a positive or/=> inlines), so CollectLiteral must fall back
		// to a Tseitin aux literal per disjunct -- exercising the inline sat-dual fix in
		// CollectLiteral (positive occurrence; the aux literal's own defining-clause
		// proof is not required here since ModelProver can still evaluate "and" directly).
		final Term and1 = s.term("and", s.term(">", a, b), s.term("<", a, s.numeral("10")));
		final Term and2 = s.term("and", s.term(">", c, d), s.term("<", c, s.numeral("10")));
		s.assertTerm(s.term("or", and1, and2));
		s.assertTerm(s.term(">", a, b));
		s.assertTerm(s.term("<", a, s.numeral("10")));
		s.assertTerm(s.term("<=", c, d));
		checkSatAndProof(s);
	}

	@Test
	public void testAuxLiteralSharedOrBothPolarities() {
		final SMTInterpol s = newScript();
		s.setLogic("QF_UFLIA");
		final Sort intSort = s.sort("Int");
		s.declareFun("x", Script.EMPTY_SORT_ARRAY, intSort);
		s.declareFun("y", Script.EMPTY_SORT_ARRAY, intSort);
		s.declareFun("z", Script.EMPTY_SORT_ARRAY, intSort);
		final Term x = s.term("x"), y = s.term("y"), z = s.term("z");
		// (or (> x y) (= x y)) occurs twice -- once as a direct (positive) "and" conjunct,
		// once (negated) as the antecedent of an inlined "=>" -- forcing a Tseitin aux
		// literal used at both polarities. Exercises both the inline sat-dual fix in
		// CollectLiteral and BuildClause.addLiteral's mLitSatProofs key (must use the
		// already-signed "lit" directly, not re-apply "positive").
		final Term orTerm = s.term("or", s.term(">", x, y), s.term("=", x, y));
		s.assertTerm(s.term("and", orTerm, s.term("=>", orTerm, s.term("<=", z, x))));
		checkSatAndProof(s);
	}

	@Test
	public void testAuxLiteralSharedOrForcedFalse() {
		final SMTInterpol s = newScript();
		s.setLogic("QF_UFLIA");
		final Sort intSort = s.sort("Int");
		s.declareFun("x", Script.EMPTY_SORT_ARRAY, intSort);
		s.declareFun("y", Script.EMPTY_SORT_ARRAY, intSort);
		s.declareFun("z", Script.EMPTY_SORT_ARRAY, intSort);
		final Term x = s.term("x"), y = s.term("y"), z = s.term("z");
		// (or (> x y) (= x y)) is forced false and shared (occurs twice), exercising
		// createDefiningClausesForLiteral's "or" branch with the aux literal's negation
		// as the one satisfied by the model.
		final Term orTerm = s.term("or", s.term(">", x, y), s.term("=", x, y));
		s.assertTerm(
				s.term("and", s.term("not", orTerm), s.term("or", orTerm, s.term("<=", z, x))));
		checkSatAndProof(s);
	}

	@Test
	public void testAuxLiteralSharedAnd() {
		final SMTInterpol s = newScript();
		s.setLogic("QF_UFLIA");
		final Sort intSort = s.sort("Int");
		s.declareFun("x", Script.EMPTY_SORT_ARRAY, intSort);
		s.declareFun("y", Script.EMPTY_SORT_ARRAY, intSort);
		s.declareFun("z", Script.EMPTY_SORT_ARRAY, intSort);
		final Term x = s.term("x"), y = s.term("y"), z = s.term("z");
		// (and (<= x y) (<= y z)) occurs twice, forcing a Tseitin aux literal: exercises
		// createDefiningClausesForLiteral's "and" branch (Phase 2), both polarities.
		final Term andTerm = s.term("and", s.term("<=", x, y), s.term("<=", y, z));
		s.assertTerm(s.term("or", andTerm, s.term("=>", andTerm, s.term("=", x, z))));
		checkSatAndProof(s);
	}

	@Test
	public void testAuxLiteralSharedImplies() {
		final SMTInterpol s = newScript();
		s.setLogic("QF_UFLIA");
		final Sort intSort = s.sort("Int");
		final Sort boolSort = s.sort("Bool");
		s.declareFun("x", Script.EMPTY_SORT_ARRAY, intSort);
		s.declareFun("p", Script.EMPTY_SORT_ARRAY, boolSort);
		final Term x = s.term("x"), p = s.term("p");
		// (=> p (> x 0)) occurs twice, forcing a Tseitin aux literal: exercises
		// createDefiningClausesForLiteral's "=>" branch (Phase 2), both polarities.
		final Term impTerm = s.term("=>", p, s.term(">", x, s.numeral("0")));
		s.assertTerm(s.term("and", impTerm, s.term("or", impTerm, s.term("not", p))));
		checkSatAndProof(s);
	}

	@Test
	public void testAndNWayNegative() {
		final SMTInterpol s = newScript();
		s.setLogic("QF_UFLIA");
		final Sort intSort = s.sort("Int");
		s.declareFun("p", Script.EMPTY_SORT_ARRAY, intSort);
		s.declareFun("q", Script.EMPTY_SORT_ARRAY, intSort);
		s.declareFun("r", Script.EMPTY_SORT_ARRAY, intSort);
		final Term p = s.term("p"), q = s.term("q"), r = s.term("r");
		// (and (p>0) (q>0)) occurs bare (positive, forcing its "and-negative" aux
		// clauses) and negated-and-shared elsewhere; forced false via p<=0, so its
		// negation is the literal the assembler actually needs to justify --
		// exercises createDefiningClausesForLiteral's "and-negative" N-way case
		// (Clausifier.NWayAuxProof / ModelProofBuilder.proveNWay), picking the
		// false conjunct (q here would also work) at assembly time.
		final Term andTerm = s.term("and", s.term(">", p, s.numeral("0")), s.term(">", q, s.numeral("0")));
		s.assertTerm(s.term("and", s.term("or", andTerm, s.term(">", r, s.numeral("0"))),
				s.term("or", s.term("not", andTerm), s.term("=", r, s.numeral("5"))),
				s.term("or", s.term("not", andTerm), s.term("=", r, s.numeral("6")))));
		s.assertTerm(s.term("<=", p, s.numeral("0")));
		s.assertTerm(s.term(">", r, s.numeral("0")));
		checkSatAndProof(s);
	}

	@Test
	public void testImpliesNWayPositive() {
		final SMTInterpol s = newScript();
		s.setLogic("QF_UFLIA");
		final Sort intSort = s.sort("Int");
		s.declareFun("p", Script.EMPTY_SORT_ARRAY, intSort);
		s.declareFun("q", Script.EMPTY_SORT_ARRAY, intSort);
		s.declareFun("r", Script.EMPTY_SORT_ARRAY, intSort);
		s.declareFun("t", Script.EMPTY_SORT_ARRAY, intSort);
		final Term p = s.term("p"), q = s.term("q"), r = s.term("r"), t = s.term("t");
		// (=> (p>0) (q>0) (r>0)) occurs bare-and-shared (forcing "=>-positive" aux
		// clauses) and negated elsewhere; forced true via the *first premise* being
		// false (p<=0) -- exercises createDefiningClausesForLiteral's "=>-positive"
		// N-way case picking a premise (as opposed to the conclusion).
		final Term impTerm = s.term("=>", s.term(">", p, s.numeral("0")), s.term(">", q, s.numeral("0")),
				s.term(">", r, s.numeral("0")));
		s.assertTerm(s.term("and", s.term("or", impTerm, s.term("=", t, s.numeral("1"))),
				s.term("or", impTerm, s.term("=", t, s.numeral("2"))),
				s.term("or", s.term("not", impTerm), s.term("=", t, s.numeral("3")))));
		s.assertTerm(s.term("<=", p, s.numeral("0")));
		s.assertTerm(s.term("=", t, s.numeral("3")));
		checkSatAndProof(s);
	}

	@Test
	public void testIteAuxLiteralCondTrue() {
		final SMTInterpol s = newScript();
		s.setLogic("QF_UFLIA");
		final Sort intSort = s.sort("Int");
		s.declareFun("c", Script.EMPTY_SORT_ARRAY, intSort);
		s.declareFun("x", Script.EMPTY_SORT_ARRAY, intSort);
		s.declareFun("y", Script.EMPTY_SORT_ARRAY, intSort);
		s.declareFun("r", Script.EMPTY_SORT_ARRAY, intSort);
		final Term c = s.term("c"), x = s.term("x"), y = s.term("y"), r = s.term("r");
		// "ite" has no direct checked axiom, so its aux-literal proof has to bridge a
		// tautology() oracle into the opaque convention -- exercises
		// createIteSatProof's "case split via final resolution on cond" derivation,
		// with cond/thenTerm/elseTerm themselves ">"-compiled (i.e. already
		// "not"-headed) to exercise the wrapNot-recursive-over-peel pitfall too.
		final Term cond = s.term(">", c, s.numeral("0"));
		final Term thenTerm = s.term(">", x, s.numeral("0"));
		final Term elseTerm = s.term(">", y, s.numeral("0"));
		final Term iteTerm = s.term("ite", cond, thenTerm, elseTerm);
		s.assertTerm(s.term("and", s.term("or", iteTerm, s.term("=", r, s.numeral("1"))),
				s.term("or", s.term("not", iteTerm), s.term("=", r, s.numeral("2")))));
		s.assertTerm(cond);
		s.assertTerm(thenTerm);
		s.assertTerm(s.term("=", r, s.numeral("2")));
		checkSatAndProof(s);
	}

	@Test
	public void testIteAuxLiteralCondFalseNegated() {
		final SMTInterpol s = newScript();
		s.setLogic("QF_UFLIA");
		final Sort intSort = s.sort("Int");
		s.declareFun("c", Script.EMPTY_SORT_ARRAY, intSort);
		s.declareFun("x", Script.EMPTY_SORT_ARRAY, intSort);
		s.declareFun("y", Script.EMPTY_SORT_ARRAY, intSort);
		s.declareFun("r", Script.EMPTY_SORT_ARRAY, intSort);
		final Term c = s.term("c"), x = s.term("x"), y = s.term("y"), r = s.term("r");
		// Same as testIteAuxLiteralCondTrue, but forces cond false (the "else" branch)
		// and thenTerm false so the ite as a whole is false -- exercises the
		// negative-litTerm ("not ite") side of createIteSatProof.
		final Term cond = s.term(">", c, s.numeral("0"));
		final Term thenTerm = s.term(">", x, s.numeral("0"));
		final Term elseTerm = s.term(">", y, s.numeral("0"));
		final Term iteTerm = s.term("ite", cond, thenTerm, elseTerm);
		s.assertTerm(s.term("and", s.term("or", iteTerm, s.term("=", r, s.numeral("1"))),
				s.term("or", s.term("not", iteTerm), s.term("=", r, s.numeral("2")))));
		s.assertTerm(cond);
		s.assertTerm(s.term("<=", x, s.numeral("0")));
		s.assertTerm(s.term("=", r, s.numeral("1")));
		checkSatAndProof(s);
	}

	@Test
	public void testXorAuxLiteralTrue() {
		final SMTInterpol s = newScript();
		s.setLogic("QF_UFLIA");
		final Sort intSort = s.sort("Int");
		s.declareFun("a", Script.EMPTY_SORT_ARRAY, intSort);
		s.declareFun("b", Script.EMPTY_SORT_ARRAY, intSort);
		s.declareFun("r", Script.EMPTY_SORT_ARRAY, intSort);
		final Term a = s.term("a"), b = s.term("b"), r = s.term("r");
		// "xor" also has no direct checked axiom -- exercises createXorSatProof's
		// same case-split derivation, splitting on p1.
		final Term p1 = s.term(">", a, s.numeral("0"));
		final Term p2 = s.term(">", b, s.numeral("0"));
		final Term xorTerm = s.term("xor", p1, p2);
		s.assertTerm(s.term("and", s.term("or", xorTerm, s.term("=", r, s.numeral("1"))),
				s.term("or", s.term("not", xorTerm), s.term("=", r, s.numeral("2")))));
		s.assertTerm(p1);
		s.assertTerm(s.term("<=", b, s.numeral("0")));
		s.assertTerm(s.term("=", r, s.numeral("2")));
		checkSatAndProof(s);
	}

	@Test
	public void testXorAuxLiteralFalseNegated() {
		final SMTInterpol s = newScript();
		s.setLogic("QF_UFLIA");
		final Sort intSort = s.sort("Int");
		s.declareFun("a", Script.EMPTY_SORT_ARRAY, intSort);
		s.declareFun("b", Script.EMPTY_SORT_ARRAY, intSort);
		s.declareFun("r", Script.EMPTY_SORT_ARRAY, intSort);
		final Term a = s.term("a"), b = s.term("b"), r = s.term("r");
		// Forces both p1/p2 true (xor false) -- exercises the negative-litTerm
		// ("not xor") side of createXorSatProof.
		final Term p1 = s.term(">", a, s.numeral("0"));
		final Term p2 = s.term(">", b, s.numeral("0"));
		final Term xorTerm = s.term("xor", p1, p2);
		s.assertTerm(s.term("and", s.term("or", xorTerm, s.term("=", r, s.numeral("1"))),
				s.term("or", s.term("not", xorTerm), s.term("=", r, s.numeral("2")))));
		s.assertTerm(p1);
		s.assertTerm(p2);
		s.assertTerm(s.term("=", r, s.numeral("1")));
		checkSatAndProof(s);
	}

	@Test
	public void testModelProofModeDefaultsToEvaluate() {
		// Sanity check that the default (":model-proof-mode" unset) is unaffected by
		// Phase 1: it should keep using the whole-formula evaluating ModelProver path.
		final SMTInterpol s = new SMTInterpol(new DefaultLogger());
		s.setOption(":produce-models", true);
		s.setOption(":interactive-mode", true);
		s.setOption(":produce-proofs", true);
		s.setOption(":proof-level", "full");
		s.setLogic("QF_UFLIA");
		final Sort intSort = s.sort("Int");
		s.declareFun("x", Script.EMPTY_SORT_ARRAY, intSort);
		s.declareFun("y", Script.EMPTY_SORT_ARRAY, intSort);
		final Term x = s.term("x"), y = s.term("y");
		s.assertTerm(s.term("<=", x, y));
		checkSatAndProof(s);
	}
}
