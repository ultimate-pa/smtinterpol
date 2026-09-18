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
package de.uni_freiburg.informatik.ultimate.smtinterpol.model;

import java.util.HashMap;
import java.util.Map;

import org.junit.Assert;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.JUnit4;

import de.uni_freiburg.informatik.ultimate.logic.FunctionSymbol;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.smtinterpol.DefaultLogger;
import de.uni_freiburg.informatik.ultimate.smtinterpol.proof.resolute.MinimalProofChecker;
import de.uni_freiburg.informatik.ultimate.smtinterpol.proof.resolute.ProofLiteral;
import de.uni_freiburg.informatik.ultimate.smtinterpol.smtlib2.SMTInterpol;

/**
 * Tests for {@link ModelProver#proveAtom}, the atom-level entry point added in
 * Phase 0 of the model-proof plan (SMTInterpol/doc/model-proof-plan.md).
 *
 * @author Jochen Hoenicke
 */
@RunWith(JUnit4.class)
public class ModelProverTest {

	private void checkAtom(final MinimalProofChecker checker, final Map<FunctionSymbol, Term> funcDefs,
			final ModelProver prover, final Model model, final Term atom) {
		final Term proof = prover.proveAtom(atom);
		// mirror the refineFun prefix buildModelProof adds, so the checker knows the
		// definitions of the (uninterpreted) functions the model assigned a value to.
		final ProofLiteral[] clause = checker.getProvedClause(funcDefs, proof);
		Assert.assertEquals(1, clause.length);
		Assert.assertEquals(atom, clause[0].getAtom());
		final boolean expectedPolarity = model.evaluate(atom) == model.getTheory().mTrue;
		Assert.assertEquals(expectedPolarity, clause[0].getPolarity());
	}

	@Test
	public void testProveAtom() {
		final SMTInterpol script = new SMTInterpol(new DefaultLogger());
		script.setOption(":produce-models", true);
		script.setLogic("QF_UFLIA");
		final Sort intSort = script.sort("Int");
		final Sort boolSort = script.sort("Bool");
		script.declareFun("x", Script.EMPTY_SORT_ARRAY, intSort);
		script.declareFun("y", Script.EMPTY_SORT_ARRAY, intSort);
		script.declareFun("f", new Sort[] { intSort }, intSort);
		script.declareFun("p", Script.EMPTY_SORT_ARRAY, boolSort);

		final Term x = script.term("x");
		final Term y = script.term("y");
		final Term p = script.term("p");
		final Term fx = script.term("f", x);
		final Term fy = script.term("f", y);

		script.assertTerm(script.term("<=", x, y));
		script.assertTerm(script.term("not", script.term("=", x, y)));
		script.assertTerm(p);

		Assert.assertEquals(LBool.SAT, script.checkSat());
		final Model model = (Model) script.getModel();

		final ModelProver prover = new ModelProver(model);
		final MinimalProofChecker checker = new MinimalProofChecker(script, script.getLogger());
		final Map<FunctionSymbol, Term> funcDefs = new HashMap<>();
		for (final FunctionSymbol fs : model.getDefinedFunctions()) {
			funcDefs.put(fs, model.getFunctionDefinition(fs));
		}

		// atoms directly asserted (or their negation)
		checkAtom(checker, funcDefs, prover, model, script.term("<=", x, y));
		checkAtom(checker, funcDefs, prover, model, script.term("=", x, y));
		checkAtom(checker, funcDefs, prover, model, p);
		// derived atoms not directly asserted, evaluated via congruence/LA
		checkAtom(checker, funcDefs, prover, model, script.term("=", fx, fy));
		checkAtom(checker, funcDefs, prover, model, script.term("<=", y, x));
		checkAtom(checker, funcDefs, prover, model, script.term(">=", script.term("+", x, script.numeral("1")), y));
	}
}
