/*
 * Copyright (C) 2009-2017 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.smtinterpol.proof;

import java.util.Arrays;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Stack;

import de.uni_freiburg.informatik.ultimate.logic.AnnotatedTerm;
import de.uni_freiburg.informatik.ultimate.logic.Annotation;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.FormulaUnLet;
import de.uni_freiburg.informatik.ultimate.logic.FunctionSymbol;
import de.uni_freiburg.informatik.ultimate.logic.NonRecursive;
import de.uni_freiburg.informatik.ultimate.logic.SMTLIBConstants;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.Theory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.LogProxy;

/**
 * This proof checker checks compliance of SMTInterpol proofs with the minimal
 * proof format.
 *
 * @author Jochen Hoenicke
 */
public class MinimalProofChecker extends NonRecursive {

	/*
	 * The proof checker uses a non-recursive iteration through the proof tree. The main type in a proof tree is the
	 * sort {@literal @}Proof. Each term of this sort proves a formula and the main task of this code is to compute the
	 * proven formula. The whole proof term should prove the formula false.
	 *
	 * The main idea of this non-recursive algorithm is to push a proof walker for the {@literal @}Proof terms on the
	 * todo stack, which will push the proved term of type Bool onto the result stack mStackResults. To handle functions
	 * like {@literal @}eq, {@literal @}cong, {@literal @}trans that take a {@literal @}Proof term as input, first a
	 * XYWalker the function XY is pushed on the todo stack and then the ProofWalker for the {@literal @}Proof terms are
	 * pushed. The Walker will then call the corresponding walkXY function which checks the proved arguments, computes
	 * the final proved formula and pushes that on the result stack.
	 *
	 * Simple functions that don't take {@literal @}Proof arguments are handled directly by calling the walkXY function.
	 */

	/**
	 * The set of all asserted terms (collected from the script by calling getAssertions()). This is used to check the
	 * {@literal @}asserted rules.
	 */
	HashSet<Term> mAssertions;

	/**
	 * The SMT script (mainly used to create terms).
	 */
	Script mSkript;
	/**
	 * The logger where errors are reported.
	 */
	LogProxy mLogger;
	/**
	 * The ProofRules object.
	 */
	ProofRules mProofRules;
	/**
	 * The number of reported errors.
	 */
	int mError;

	/**
	 * The proof cache. It maps each converted proof to the clause it proves.
	 */
	HashMap<Term, ProofLiteral[]> mCacheConv;

	/**
	 * The result stack. This contains the terms proved by the proof terms.
	 */
	Stack<ProofLiteral[]> mStackResults = new Stack<>();

	/**
	 * Create a proof checker.
	 *
	 * @param script
	 *            An SMT2 script.
	 * @param logger
	 *            The logger where errors are reported.
	 */
	public MinimalProofChecker(final Script script, final LogProxy logger) {
		mSkript = script;
		mLogger = logger;
		mProofRules = new ProofRules(script.getTheory());
	}

	/**
	 * Check a proof for consistency. This reports errors on the logger.
	 *
	 * @param proof
	 *            the proof to check.
	 * @return true, if no errors were found.
	 */
	public boolean check(Term proof) {
		final FormulaUnLet unletter = new FormulaUnLet();
		final Term[] assertions = mSkript.getAssertions();
		mAssertions = new HashSet<>(assertions.length);
		for (final Term ass : assertions) {
			mAssertions.add(unletter.transform(ass));
		}

		// Initializing the proof-checker-cache
		mCacheConv = new HashMap<>();
		mError = 0;
		// Now non-recursive:
		proof = unletter.unlet(proof);
		run(new ProofWalker(proof));

		assert (mStackResults.size() == 1);
		final ProofLiteral[] result = stackPop();
		if (result != null && result.length > 0) {
			reportError("The proof did not yield a contradiction but " + Arrays.toString(result));
		}
		// clear state
		mAssertions = null;
		mCacheConv = null;

		return mError == 0;
	}

	/**
	 * Check a proof for consistency and compute the proved clause. This prints
	 * warnings for missing pivot literals.
	 *
	 * @param proof the proof to check.
	 * @return the proved clause.
	 */
	public ProofLiteral[] getProvedClause(Term proof) {
		final FormulaUnLet unletter = new FormulaUnLet();
		final Term[] assertions = mSkript.getAssertions();
		mAssertions = new HashSet<>(assertions.length);
		for (final Term ass : assertions) {
			mAssertions.add(unletter.transform(ass));
		}

		// Initializing the proof-checker-cache
		mCacheConv = new HashMap<>();
		mError = 0;
		// Now non-recursive:
		proof = unletter.unlet(proof);
		run(new ProofWalker(proof));

		assert (mStackResults.size() == 1);
		// clear state
		mAssertions = null;
		mCacheConv = null;

		return stackPop();
	}

	private void reportError(final String msg) {
		mLogger.error(msg);
		mError++;
	}

	private void reportWarning(final String msg) {
		mLogger.warn(msg);
	}

	/**
	 * The proof walker. This takes a proof term and pushes the proven formula on the result stack. It also checks the
	 * proof cache to prevent running over the same term twice.
	 *
	 * @param proofTerm
	 *            The proof term. Its sort must be {@literal @}Proof.
	 */
	void walk(Term proofTerm) {
		while (proofTerm instanceof AnnotatedTerm && !mProofRules.isAxiom(proofTerm)) {
			proofTerm = ((AnnotatedTerm) proofTerm).getSubterm();
		}
		/* Check the cache, if the unfolding step was already done */
		if (mCacheConv.containsKey(proofTerm)) {
			stackPush(mCacheConv.get(proofTerm), proofTerm);
			return;
		}
		if (mProofRules.isAxiom(proofTerm)) {
			stackPush(computeAxiom(proofTerm), proofTerm);
		} else if (mProofRules.isProofRule(ProofRules.RES, proofTerm)) {
			new ResolutionWalker((ApplicationTerm) proofTerm).enqueue(this);
		} else {
			stackPush(checkAssert(proofTerm), proofTerm);
		}
	}

	/**
	 * Handle the resolution rule. The stack should contain the converted input clauses.
	 *
	 * @param resApp
	 *            The <code>{@literal @}res</code> application from the original proof.
	 */
	ProofLiteral[] walkResolution(final ApplicationTerm resApp, final ProofLiteral[] posClause,
			final ProofLiteral[] negClause) {
		/*
		 * allDisjuncts is the currently computed resolution result.
		 */
		final HashSet<ProofLiteral> allDisjuncts = new HashSet<>();

		/* Now get the disjuncts of the first argument. */
		allDisjuncts.addAll(Arrays.asList(posClause));

		final Term pivot = resApp.getParameters()[0];
		final ProofLiteral posPivot = new ProofLiteral(pivot, true);
		final ProofLiteral negPivot = new ProofLiteral(pivot, false);

		/* Remove the pivot from allDisjuncts */
		if (!allDisjuncts.remove(posPivot)) {
			reportWarning("Could not find pivot " + posPivot + " in " + Arrays.asList(posClause));
		}

		boolean pivotFound = false;
		for (final ProofLiteral lit : negClause) {
			if (lit.equals(negPivot)) {
				pivotFound = true;
			} else {
				allDisjuncts.add(lit);
			}
		}

		if (!pivotFound) {
			reportWarning("Could not find pivot " + negPivot + " in " + Arrays.asList(negClause));
		}
		return allDisjuncts.toArray(new ProofLiteral[allDisjuncts.size()]);
	}

	/* === Auxiliary functions === */

	void stackPush(final ProofLiteral[] pushClause, final Term keyTerm) {
		mCacheConv.put(keyTerm, pushClause);
		mStackResults.push(pushClause);
	}

	ProofLiteral[] stackPop() {
		return mStackResults.pop();
	}

	public ProofLiteral[] computeAxiom(final Term axiom) {
		final Theory theory = axiom.getTheory();
		assert mProofRules.isAxiom(axiom);
		final Annotation[] annots = ((AnnotatedTerm) axiom).getAnnotations();
		switch (annots[0].getKey()) {
		case ":" + ProofRules.TRUEI: {
			return new ProofLiteral[] { new ProofLiteral(theory.term(SMTLIBConstants.TRUE), true) };
		}
		case ":" + ProofRules.FALSEE: {
			return new ProofLiteral[] { new ProofLiteral(theory.term(SMTLIBConstants.FALSE), false) };
		}
		case ":" + ProofRules.NOTI: {
			assert annots.length == 1;
			final Term[] params = (Term[]) annots[0].getValue();
			assert params.length == 1;
			final Term term = params[0];

			// (not t), t
			return new ProofLiteral[] { new ProofLiteral(theory.term(SMTLIBConstants.NOT, term), true),
					new ProofLiteral(term, true) };
		}
		case ":" + ProofRules.NOTE: {
			assert annots.length == 1;
			final Term[] params = (Term[]) annots[0].getValue();
			assert params.length == 1;
			final Term term = params[0];

			// ~(not t), ~t
			return new ProofLiteral[] { new ProofLiteral(theory.term(SMTLIBConstants.NOT, term), false),
					new ProofLiteral(term, false) };
		}
		case ":" + ProofRules.ORI: {
			assert annots.length == 2;
			final Term[] params = (Term[]) annots[0].getValue();
			assert annots[1].getKey().equals(ProofRules.ANNOT_POS);
			final int pos = (Integer) annots[1].getValue();
			assert pos >= 0 && pos < params.length;

			// (or t1 ... tn), ~tpos
			return new ProofLiteral[] { new ProofLiteral(theory.term(SMTLIBConstants.OR, params), true),
					new ProofLiteral(params[pos], false) };
		}
		case ":" + ProofRules.ORE: {
			assert annots.length == 1;
			final Term[] params = (Term[]) annots[0].getValue();

			// ~(or t1 ... tn), t1, ..., tn
			final ProofLiteral[] clause = new ProofLiteral[params.length + 1];
			clause[0] = new ProofLiteral(theory.term(SMTLIBConstants.OR, params), false);
			for (int i = 0; i < params.length; i++) {
				clause[i + 1] = new ProofLiteral(params[i], true);
			}
			return clause;
		}
		case ":" + ProofRules.ANDI: {
			assert annots.length == 1;
			final Term[] params = (Term[]) annots[0].getValue();

			// (and t1 ... tn), ~t1, ..., ~tn
			final ProofLiteral[] clause = new ProofLiteral[params.length + 1];
			clause[0] = new ProofLiteral(theory.term(SMTLIBConstants.AND, params), true);
			for (int i = 0; i < params.length; i++) {
				clause[i + 1] = new ProofLiteral(params[i], false);
			}
			return clause;
		}
		case ":" + ProofRules.ANDE: {
			assert annots.length == 2;
			final Term[] params = (Term[]) annots[0].getValue();
			assert annots[1].getKey().equals(ProofRules.ANNOT_POS);
			final int pos = (Integer) annots[1].getValue();
			assert pos >= 0 && pos < params.length;

			// ~(and t1 ... tn), tpos
			return new ProofLiteral[] { new ProofLiteral(theory.term(SMTLIBConstants.AND, params), false),
					new ProofLiteral(params[pos], true) };
		}
		case ":" + ProofRules.IMPI: {
			assert annots.length == 2;
			final Term[] params = (Term[]) annots[0].getValue();
			assert annots[1].getKey().equals(ProofRules.ANNOT_POS);
			final int pos = (Integer) annots[1].getValue();
			assert pos >= 0 && pos < params.length;

			// (=> t1 ... tn), tpos (~tpos if pos == n)
			return new ProofLiteral[] { new ProofLiteral(theory.term(SMTLIBConstants.IMPLIES, params), true),
					new ProofLiteral(params[pos], pos < params.length - 1) };
		}
		case ":" + ProofRules.IMPE: {
			assert annots.length == 2;
			final Term[] params = (Term[]) annots[0].getValue();

			// ~(=> t1 ... tn), ~t1, ..., ~tn-1, tn
			final ProofLiteral[] clause = new ProofLiteral[params.length + 1];
			clause[0] = new ProofLiteral(theory.term(SMTLIBConstants.IMPLIES, params), false);
			for (int i = 0; i < params.length; i++) {
				clause[i + 1] = new ProofLiteral(params[i], i == params.length - 1);
			}
			return clause;
		}
		case ":" + ProofRules.IFFI1: {
			assert annots.length == 1;
			final Term[] params = (Term[]) annots[0].getValue();
			if (params.length != 2 || params[0].getSort().getName() != SMTLIBConstants.BOOL) {
				throw new AssertionError("Invalid Rule: " + axiom);
			}

			// (= t1 t2), t1, t2
			return new ProofLiteral[] { new ProofLiteral(theory.term(SMTLIBConstants.EQUALS, params), true),
					new ProofLiteral(params[0], true), new ProofLiteral(params[1], true) };
		}
		case ":" + ProofRules.IFFI2: {
			assert annots.length == 1;
			final Term[] params = (Term[]) annots[0].getValue();
			if (params.length != 2 || params[0].getSort().getName() != SMTLIBConstants.BOOL) {
				throw new AssertionError("Invalid Rule: " + axiom);
			}

			// (= t1 t2), ~t1, ~t2
			return new ProofLiteral[] { new ProofLiteral(theory.term(SMTLIBConstants.EQUALS, params), true),
					new ProofLiteral(params[0], false), new ProofLiteral(params[1], false) };
		}
		case ":" + ProofRules.IFFE1: {
			assert annots.length == 1;
			final Term[] params = (Term[]) annots[0].getValue();
			if (params.length != 2 || params[0].getSort().getName() != SMTLIBConstants.BOOL) {
				throw new AssertionError("Invalid Rule: " + axiom);
			}

			// ~(= t1 t2), t1, ~t2
			return new ProofLiteral[] { new ProofLiteral(theory.term(SMTLIBConstants.EQUALS, params), false),
					new ProofLiteral(params[0], true), new ProofLiteral(params[1], false) };
		}
		case ":" + ProofRules.IFFE2: {
			assert annots.length == 1;
			final Term[] params = (Term[]) annots[0].getValue();
			if (params.length != 2 || params[0].getSort().getName() != SMTLIBConstants.BOOL) {
				throw new AssertionError("Invalid Rule: " + axiom);
			}

			// ~(= t1 t2), ~t1, t2
			return new ProofLiteral[] { new ProofLiteral(theory.term(SMTLIBConstants.EQUALS, params), false),
					new ProofLiteral(params[0], false), new ProofLiteral(params[1], true) };
		}
		case ":" + ProofRules.XORI: {
			assert annots.length == 1;
			final Term[][] xorLists = (Term[][]) annots[0].getValue();
			assert xorLists.length == 3;
			if (!ProofRules.checkXorParams(xorLists)) {
				throw new AssertionError("Invalid Rule: " + axiom);
			}
			// (xor set0), (xor set1), ~(xor set2)
			final ProofLiteral[] clause = new ProofLiteral[3];
			for (int i = 0; i < 3; i++) {
				final Term term = xorLists[i].length == 1 ? xorLists[i][0]
						: theory.term(SMTLIBConstants.XOR, xorLists[i]);
				assert term != null;
				clause[i] = new ProofLiteral(term, i < 2);
			}
			return clause;
		}
		case ":" + ProofRules.XORE: {
			assert annots.length == 1;
			final Term[][] xorLists = (Term[][]) annots[0].getValue();
			assert xorLists.length == 3;
			if (!ProofRules.checkXorParams(xorLists)) {
				throw new AssertionError("Invalid Rule: " + axiom);
			}
			// ~(xor set0), ~(xor set1), ~(xor set2)
			final ProofLiteral[] clause = new ProofLiteral[3];
			for (int i = 0; i < 3; i++) {
				final Term term = xorLists[i].length == 1 ? xorLists[i][0]
						: theory.term(SMTLIBConstants.XOR, xorLists[i]);
				assert term != null;
				clause[i] = new ProofLiteral(term, false);
			}
			return clause;
		}
		case ":" + ProofRules.EQI: {
			assert annots.length == 1;
			final Term[] params = (Term[]) annots[0].getValue();

			// (= t1 ... tn), ~(= t1 t2), ~(tn-1 tn)
			final ProofLiteral[] clause = new ProofLiteral[params.length];
			clause[0] = new ProofLiteral(theory.term(SMTLIBConstants.EQUALS, params), true);
			for (int i = 0; i < params.length - 1; i++) {
				clause[i + 1] = new ProofLiteral(theory.term(SMTLIBConstants.EQUALS, params[i], params[i + 1]), false);
			}
			return clause;
		}
		case ":" + ProofRules.EQE: {
			assert annots.length == 2;
			final Term[] params = (Term[]) annots[0].getValue();
			assert annots[1].getKey().equals(ProofRules.ANNOT_POS);
			final Integer[] positions = (Integer[]) annots[1].getValue();
			assert positions.length == 2;
			final int pos0 = positions[0];
			final int pos1 = positions[1];
			assert 0 <= pos0 && pos0 < params.length && 0 <= pos1 && pos1 < params.length;

			// ~(= t1 ... tn), (= ti tj)
			return new ProofLiteral[] { new ProofLiteral(theory.term(SMTLIBConstants.EQUALS, params), false),
					new ProofLiteral(theory.term(SMTLIBConstants.EQUALS, params[pos0], params[pos1]), true) };
		}
		case ":" + ProofRules.DISTINCTI: {
			assert annots.length == 1;
			final Term[] params = (Term[]) annots[0].getValue();
			final int len = params.length;

			// (distinct t1 ... tn), (= t1 t2),...
			final ProofLiteral[] clause = new ProofLiteral[1 + len * (len - 1) / 2];
			clause[0] = new ProofLiteral(theory.term(SMTLIBConstants.DISTINCT, params), true);
			int pos = 1;
			for (int i = 0; i < len - 1; i++) {
				for (int j = i + 1; j < len; j++) {
					clause[pos++] = new ProofLiteral(theory.term(SMTLIBConstants.EQUALS, params[i], params[j]), true);
				}
			}
			assert pos == clause.length;
			return clause;
		}
		case ":" + ProofRules.DISTINCTE: {
			assert annots.length == 2;
			final Term[] params = (Term[]) annots[0].getValue();
			assert annots[1].getKey().equals(ProofRules.ANNOT_POS);
			final Integer[] positions = (Integer[]) annots[1].getValue();
			assert positions.length == 2;
			final int pos0 = positions[0];
			final int pos1 = positions[1];
			assert 0 <= pos0 && pos0 < params.length && 0 <= pos1 && pos1 < params.length;

			// ~(distinct t1 ... tn), ~(= ti tj)
			return new ProofLiteral[] { new ProofLiteral(theory.term(SMTLIBConstants.DISTINCT, params), false),
					new ProofLiteral(theory.term(SMTLIBConstants.EQUALS, params[pos0], params[pos1]), false) };
		}
		case ":" + ProofRules.ITE1: {
			assert annots.length == 1;
			final Term[] params = (Term[]) annots[0].getValue();
			assert params.length == 3;
			final Term ite = theory.term(SMTLIBConstants.ITE, params);

			// (= (ite c t e) t), ~c
			return new ProofLiteral[] { new ProofLiteral(theory.term(SMTLIBConstants.EQUALS, ite, params[1]), true),
					new ProofLiteral(params[0], false) };
		}
		case ":" + ProofRules.ITE2: {
			assert annots.length == 1;
			final Term[] params = (Term[]) annots[0].getValue();
			assert params.length == 3;
			final Term ite = theory.term(SMTLIBConstants.ITE, params);

			// (= (ite c t e) e), c
			return new ProofLiteral[] { new ProofLiteral(theory.term(SMTLIBConstants.EQUALS, ite, params[2]), true),
					new ProofLiteral(params[0], true) };
		}
		case ":" + ProofRules.DELANNOT: {
			final Term subterm = (Term) annots[0].getValue();
			final Annotation[] subAnnots = new Annotation[annots.length - 1];
			System.arraycopy(annots, 1, subAnnots, 0, subAnnots.length);
			final Term annotTerm = theory.annotatedTerm(subAnnots, subterm);

			// (= (! t :...) t)
			return new ProofLiteral[] {
					new ProofLiteral(theory.term(SMTLIBConstants.EQUALS, annotTerm, subterm), true) };
		}
		case ":" + ProofRules.REFL: {
			assert annots.length == 1;
			final Term[] params = (Term[]) annots[0].getValue();
			assert params.length == 1;

			// (= a a)
			return new ProofLiteral[] {
					new ProofLiteral(theory.term(SMTLIBConstants.EQUALS, params[0], params[0]), true) };
		}
		case ":" + ProofRules.SYMM: {
			assert annots.length == 1;
			final Term[] params = (Term[]) annots[0].getValue();
			assert params.length == 2;

			// (= a0 a1), ~(= a1 a0)
			return new ProofLiteral[] { new ProofLiteral(theory.term(SMTLIBConstants.EQUALS, params), true),
					new ProofLiteral(theory.term(SMTLIBConstants.EQUALS, params[1], params[0]), false) };
		}
		case ":" + ProofRules.TRANS: {
			assert annots.length == 1;
			final Term[] params = (Term[]) annots[0].getValue();
			assert params.length > 2;
			final int len = params.length;

			// (= a0 alen-1), ~(= a0 a1), ..., ~(= alen-2 alen-1)
			final ProofLiteral[] clause = new ProofLiteral[len];
			clause[0] = new ProofLiteral(theory.term(SMTLIBConstants.EQUALS, params[0], params[len - 1]), true);
			for (int i = 0; i < len - 1; i++) {
				clause[i + 1] = new ProofLiteral(theory.term(SMTLIBConstants.EQUALS, params[i], params[i + 1]), false);
			}
			return clause;
		}
		case ":" + ProofRules.CONG: {
			assert annots.length == 1;
			final Object[] congArgs = (Object[]) annots[0].getValue();
			assert congArgs.length == 3;
			final FunctionSymbol func = (FunctionSymbol) congArgs[0];
			final Term[] params0 = (Term[]) congArgs[1];
			final Term[] params1 = (Term[]) congArgs[2];
			assert params0.length == params1.length;
			final Term app0 = theory.term(func, params0);
			final Term app1 = theory.term(func, params1);

			// (= (f a0...an) (f b0... bn)), ~(= a0 b0), ..., ~(= an bn)
			final ProofLiteral[] clause = new ProofLiteral[params0.length + 1];
			clause[0] = new ProofLiteral(theory.term(SMTLIBConstants.EQUALS, app0, app1), true);
			for (int i = 0; i < params0.length; i++) {
				clause[i + 1] = new ProofLiteral(theory.term(SMTLIBConstants.EQUALS, params0[i], params1[i]), false);
			}
			return clause;
		}
		case ":" + ProofRules.EXPAND: {
			assert annots.length == 1;
			final Object[] expandArgs = (Object[]) annots[0].getValue();
			assert expandArgs.length == 2;
			final FunctionSymbol func = (FunctionSymbol) expandArgs[0];
			final Term[] params = (Term[]) expandArgs[1];
			final Term app = theory.term(func, params);
			Term rhs;
			if (func.getDefinition() != null) {
				rhs = theory.let(func.getDefinitionVars(), params, func.getDefinition());
				rhs = new FormulaUnLet().unlet(rhs);
			} else if (func.isLeftAssoc() && params.length > 2) {
				rhs = params[0];
				for (int i = 1; i < params.length; i++) {
					rhs = theory.term(func, rhs, params[i]);
				}
			} else if (func.isRightAssoc() && params.length > 2) {
				rhs = params[params.length - 1];
				for (int i = params.length - 2; i >= 0; i--) {
					rhs = theory.term(func, params[i], rhs);
				}
			} else if (func.isChainable() && params.length > 2) {
				final Term[] chain = new Term[params.length - 1];
				for (int i = 0; i < chain.length; i++) {
					chain[i] = theory.term(func, params[i], params[i + 1]);
				}
				rhs = theory.term("and", chain);
			} else {
				throw new AssertionError();
			}
			return new ProofLiteral[] { new ProofLiteral(theory.term("=", app, rhs), true) };
		}
		default:
			throw new AssertionError("Unknown axiom " + axiom);
		}
	}

	public ProofLiteral[] checkAssert(final Term axiom) {
		final ApplicationTerm appTerm = (ApplicationTerm) axiom;
		final Term[] params = appTerm.getParameters();
		assert appTerm.getFunction().getName() == ProofRules.PREFIX + ProofRules.ASSUME;
		assert params.length == 1;
		if (!mAssertions.contains(params[0])) {
			reportWarning("Unknown assumption: " + params[0]);
		}
		return new ProofLiteral[] { new ProofLiteral(params[0], true) };
	}

	public static class ProofLiteral {
		Term mAtom;
		boolean mPositive;

		public ProofLiteral(final Term atom, final boolean positive) {
			mAtom = atom;
			mPositive = positive;
		}

		public ProofLiteral negate() {
			return new ProofLiteral(mAtom, !mPositive);
		}

		@Override
		public int hashCode() {
			return mAtom.hashCode() ^ (mPositive ? 0 : 0xffffffff);
		}

		@Override
		public boolean equals(final Object other) {
			if (!(other instanceof ProofLiteral)) {
				return false;
			}
			final ProofLiteral otherLit = (ProofLiteral) other;
			return mAtom == otherLit.mAtom && mPositive == otherLit.mPositive;
		}

		@Override
		public String toString() {
			return mPositive ? mAtom.toString() : "~" + mAtom.toString();
		}
	}

	/**
	 * The main proof walker that handles a term of sort {@literal @}Proof. It just
	 * calls the walk function.
	 */
	static class ProofWalker implements Walker {
		final Term mTerm;

		public ProofWalker(final Term term) {
			assert term.getSort().getName().equals(ProofRules.PREFIX + ProofRules.PROOF);
			mTerm = term;
		}

		@Override
		public void walk(final NonRecursive engine) {
			((MinimalProofChecker) engine).walk(mTerm);
		}
	}

	/**
	 * The proof walker that handles the resolution rule after its arguments are
	 * converted. It just calls the walkResolution function.
	 */
	static class ResolutionWalker implements Walker {
		final ApplicationTerm mTerm;

		public ResolutionWalker(final ApplicationTerm term) {
			mTerm = term;
		}

		public void enqueue(final MinimalProofChecker engine) {
			final Term[] params = mTerm.getParameters();
			engine.enqueueWalker(this);
			engine.enqueueWalker(new ProofWalker(params[2]));
			engine.enqueueWalker(new ProofWalker(params[1]));
		}

		@Override
		public void walk(final NonRecursive engine) {
			final MinimalProofChecker checker = (MinimalProofChecker) engine;
			final ProofLiteral[] negClause = checker.stackPop();
			final ProofLiteral[] posClause = checker.stackPop();
			checker.stackPush(checker.walkResolution(mTerm, posClause, negClause), mTerm);
		}
	}
}