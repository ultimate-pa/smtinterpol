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
import java.util.List;

import org.junit.Assert;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.JUnit4;

import de.uni_freiburg.informatik.ultimate.smtinterpol.DefaultLogger;
import de.uni_freiburg.informatik.ultimate.smtinterpol.option.OptionMap;
import de.uni_freiburg.informatik.ultimate.smtinterpol.smtlib2.ParseEnvironment;
import de.uni_freiburg.informatik.ultimate.smtinterpol.smtlib2.SMTInterpol;

/**
 * Tests for destructive equality reasoning: the substitution is applied simultaneously, so it must be idempotent,
 * otherwise variables are only renamed instead of eliminated.
 *
 * @author Jochen Hoenicke
 */
@RunWith(JUnit4.class)
public class DestructiveEqualityReasoningTest {

	private static final String DECLS = "(set-logic UFLIA)(declare-fun f (Int) Int)(declare-fun g (Int) Int)"
			+ "(declare-fun h (Int) Int)(declare-fun P (Int) Bool)(declare-fun Q (Int) Bool)"
			+ "(declare-fun R (Int Int) Bool)";

	private List<QuantClause> quantClauses(final String asserts) {
		final OptionMap options = new OptionMap(new DefaultLogger(), true);
		final SMTInterpol script = new SMTInterpol(null, options);
		new ParseEnvironment(script, options).parseStream(new StringReader(DECLS + asserts), "test");
		return new ArrayList<>(script.getClausifier().getQuantifierTheory().getQuantClauses());
	}

	@Test
	public void testChainWithPotentialSubstitution() {
		// x -> y (step 2 (i)) and y -> (f z) (step 2 (ii)): x must become (f z) as well
		final List<QuantClause> clauses = quantClauses(
				"(assert (forall ((x Int) (y Int) (z Int)) (or (not (= x y)) (not (= y (f z))) (R x z) (Q y))))");
		Assert.assertEquals(clauses.toString(), 1, clauses.size());
		Assert.assertEquals(1, clauses.get(0).getVars().length);
		Assert.assertEquals(".z.2", clauses.get(0).getVars()[0].getName());
	}

	@Test
	public void testChainEndingInSubstitutedVariable() {
		// y -> 5 and x -> y in either order: x must become 5
		for (final String lits : new String[] { "(not (= y 5)) (not (= x y))", "(not (= x y)) (not (= y 5))" }) {
			final List<QuantClause> clauses = quantClauses(
					"(assert (forall ((x Int) (y Int) (z Int)) (or " + lits + " (R x z) (Q (+ x z)))))");
			Assert.assertEquals(clauses.toString(), 1, clauses.size());
			Assert.assertEquals(clauses.toString(), 1, clauses.get(0).getVars().length);
		}
	}

	@Test
	public void testCycle() {
		// x -> (f y), y -> (g w), and w -> (h x) would close a cycle: one of the variables must remain
		final List<QuantClause> clauses = quantClauses("(assert (forall ((x Int) (y Int) (w Int)) (or "
				+ "(not (= x (f y))) (not (= y (g w))) (not (= w (h x))) (R x w))))");
		Assert.assertEquals(clauses.toString(), 1, clauses.size());
		Assert.assertEquals(clauses.toString(), 1, clauses.get(0).getVars().length);
	}
}
