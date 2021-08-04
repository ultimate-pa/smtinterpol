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
	void walk(final ApplicationTerm proofTerm) {
		/* Check the cache, if the unfolding step was already done */
		if (mCacheConv.containsKey(proofTerm)) {
			stackPush(mCacheConv.get(proofTerm), proofTerm);
			return;
		}

		/* Get the function and parameters */
		if (ProofRules.isProofRule(ProofRules.RES, proofTerm))  {
			new ResolutionWalker(proofTerm).enqueue(this);
		} else {
			stackPush(computeClause(proofTerm), proofTerm);
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
		 * s allDisjuncts is the currently computed resolution result.
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

	void stackPush(final ProofLiteral[] pushClause, final ApplicationTerm keyTerm) {
		mCacheConv.put(keyTerm, pushClause);
		mStackResults.push(pushClause);
	}

	ProofLiteral[] stackPop() {
		return mStackResults.pop();
	}

	public ProofLiteral[] computeClause(final Term axiom) {
		final ApplicationTerm appTerm = (ApplicationTerm) axiom;
		final Term[] params = appTerm.getParameters();
		switch (appTerm.getFunction().getName()) {
		case ProofRules.PREFIX + ProofRules.ASSUME: {
			assert params.length == 1;
			if (!mAssertions.contains(params[0])) {
				reportWarning("Unknown assumption: " + params[0]);
			}
			// t
			return new ProofLiteral[] { new ProofLiteral(params[0], true) };
		}
		case ProofRules.PREFIX + ProofRules.TRUEI: {
			return new ProofLiteral[] { new ProofLiteral(axiom.getTheory().term(SMTLIBConstants.TRUE), true) };
		}
		case ProofRules.PREFIX + ProofRules.FALSEE: {
			return new ProofLiteral[] { new ProofLiteral(axiom.getTheory().term(SMTLIBConstants.FALSE), false) };
		}
		case ProofRules.PREFIX + ProofRules.NOTI: {
			assert params.length == 1;
			final ApplicationTerm subterm = (ApplicationTerm) params[0];
			assert subterm.getFunction().getName() == SMTLIBConstants.NOT;
			final Term[] subParams = subterm.getParameters();

			// (not t), t
			return new ProofLiteral[] { new ProofLiteral(subterm, true), new ProofLiteral(subParams[0], true) };
		}
		case ProofRules.PREFIX + ProofRules.NOTE: {
			assert params.length == 1;
			final ApplicationTerm subterm = (ApplicationTerm) params[0];
			assert subterm.getFunction().getName() == SMTLIBConstants.NOT;
			final Term[] subParams = subterm.getParameters();

			// ~(not t), ~t
			return new ProofLiteral[] { new ProofLiteral(subterm, false), new ProofLiteral(subParams[0], false) };
		}
		case ProofRules.PREFIX + ProofRules.ORI: {
			assert params.length == 1;
			final AnnotatedTerm annotTerm = (AnnotatedTerm) params[0];
			final Annotation[] annots = annotTerm.getAnnotations();
			assert annots.length == 1 && annots[0].getKey().equals(ProofRules.ANNOT_POS);
			final ApplicationTerm subterm = (ApplicationTerm) annotTerm.getSubterm();
			assert subterm.getFunction().getName() == SMTLIBConstants.OR;
			final int pos = (Integer) annots[0].getValue();
			final Term[] subParams = subterm.getParameters();
			assert pos >= 0 && pos < subParams.length;

			// (or t1 ... tn), ~tpos
			return new ProofLiteral[] { new ProofLiteral(subterm, true), new ProofLiteral(subParams[pos], false) };
		}
		case ProofRules.PREFIX + ProofRules.ORE: {
			assert params.length == 1;
			final ApplicationTerm subterm = (ApplicationTerm) params[0];
			assert subterm.getFunction().getName() == SMTLIBConstants.OR;
			final Term[] subParams = subterm.getParameters();

			// ~(or t1 ... tn), t1, ..., tn
			final ProofLiteral[] clause = new ProofLiteral[subParams.length + 1];
			clause[0] = new ProofLiteral(subterm, false);
			for (int i = 0; i < subParams.length; i++) {
				clause[i + 1] = new ProofLiteral(subParams[i], true);
			}
			return clause;
		}
		case ProofRules.PREFIX + ProofRules.ANDI: {
			assert params.length == 1;
			final ApplicationTerm subterm = (ApplicationTerm) params[0];
			assert subterm.getFunction().getName() == SMTLIBConstants.AND;
			final Term[] subParams = subterm.getParameters();

			// (and t1 ... tn), ~t1, ..., ~tn
			final ProofLiteral[] clause = new ProofLiteral[subParams.length + 1];
			clause[0] = new ProofLiteral(subterm, true);
			for (int i = 0; i < subParams.length; i++) {
				clause[i + 1] = new ProofLiteral(subParams[i], false);
			}
			return clause;
		}
		case ProofRules.PREFIX + ProofRules.ANDE: {
			assert params.length == 1;
			final AnnotatedTerm annotTerm = (AnnotatedTerm) params[0];
			final Annotation[] annots = annotTerm.getAnnotations();
			assert annots.length == 1 && annots[0].getKey().equals(ProofRules.ANNOT_POS);
			final ApplicationTerm subterm = (ApplicationTerm) annotTerm.getSubterm();
			assert subterm.getFunction().getName() == SMTLIBConstants.AND;
			final int pos = (Integer) annots[0].getValue();
			final Term[] subParams = subterm.getParameters();
			assert pos >= 0 && pos < subParams.length;

			// ~(and t1 ... tn), tpos
			return new ProofLiteral[] { new ProofLiteral(subterm, false), new ProofLiteral(subParams[pos], true) };
		}
		case ProofRules.PREFIX + ProofRules.IMPI: {
			assert params.length == 1;
			final AnnotatedTerm annotTerm = (AnnotatedTerm) params[0];
			final Annotation[] annots = annotTerm.getAnnotations();
			assert annots.length == 1 && annots[0].getKey().equals(ProofRules.ANNOT_POS);
			final ApplicationTerm subterm = (ApplicationTerm) annotTerm.getSubterm();
			assert subterm.getFunction().getName() == SMTLIBConstants.IMPLIES;
			final int pos = (Integer) annots[0].getValue();
			final Term[] subParams = subterm.getParameters();
			assert pos >= 0 && pos < subParams.length;

			// (=> t1 ... tn), tpos (~tpos if pos == n)
			return new ProofLiteral[] { new ProofLiteral(subterm, true),
					new ProofLiteral(subParams[pos], pos < subParams.length - 1) };
		}
		case ProofRules.PREFIX + ProofRules.IMPE: {
			assert params.length == 1;
			final ApplicationTerm subterm = (ApplicationTerm) params[0];
			assert subterm.getFunction().getName() == SMTLIBConstants.IMPLIES;
			final Term[] subParams = subterm.getParameters();

			// ~(=> t1 ... tn), ~t1, ..., ~tn-1, tn
			final ProofLiteral[] clause = new ProofLiteral[subParams.length + 1];
			clause[0] = new ProofLiteral(subterm, false);
			for (int i = 0; i < subParams.length; i++) {
				clause[i + 1] = new ProofLiteral(subParams[i], i == subParams.length - 1);
			}
			return clause;
		}
		case ProofRules.PREFIX + ProofRules.IFFI1: {
			assert params.length == 1;
			final ApplicationTerm subterm = (ApplicationTerm) params[0];
			assert subterm.getFunction().getName() == SMTLIBConstants.EQUALS;
			final Term[] subParams = subterm.getParameters();
			assert subParams.length == 2;

			// (= t1 t2), t1, t2
			return new ProofLiteral[] { new ProofLiteral(subterm, true), new ProofLiteral(subParams[0], true),
					new ProofLiteral(subParams[1], true) };
		}
		case ProofRules.PREFIX + ProofRules.IFFI2: {
			assert params.length == 1;
			final ApplicationTerm subterm = (ApplicationTerm) params[0];
			assert subterm.getFunction().getName() == SMTLIBConstants.EQUALS;
			final Term[] subParams = subterm.getParameters();
			assert subParams.length == 2;

			// (= t1 t2), ~t1, ~t2
			return new ProofLiteral[] { new ProofLiteral(subterm, true), new ProofLiteral(subParams[0], false),
					new ProofLiteral(subParams[1], false) };
		}
		case ProofRules.PREFIX + ProofRules.IFFE1: {
			assert params.length == 1;
			final ApplicationTerm subterm = (ApplicationTerm) params[0];
			assert subterm.getFunction().getName() == SMTLIBConstants.EQUALS;
			final Term[] subParams = subterm.getParameters();
			assert subParams.length == 2;

			// ~(= t1 t2), t1, ~t2
			return new ProofLiteral[] { new ProofLiteral(subterm, false), new ProofLiteral(subParams[0], true),
					new ProofLiteral(subParams[1], false) };
		}
		case ProofRules.PREFIX + ProofRules.IFFE2: {
			assert params.length == 1;
			final ApplicationTerm subterm = (ApplicationTerm) params[0];
			assert subterm.getFunction().getName() == SMTLIBConstants.EQUALS;
			final Term[] subParams = subterm.getParameters();
			assert subParams.length == 2;

			// ~(= t1 t2), ~t1, t2
			return new ProofLiteral[] { new ProofLiteral(subterm, false), new ProofLiteral(subParams[0], false),
					new ProofLiteral(subParams[1], true) };
		}
		case ProofRules.PREFIX + ProofRules.XORI: {
			assert params.length == 3;
			assert ProofRules.checkXorParams(params);
			// (xor set0), (xor set1), ~(xor set2)
			final ProofLiteral[] clause = new ProofLiteral[3];
			for (int i = 0; i < 3; i++) {
				Term atom = params[i];
				if (atom instanceof AnnotatedTerm) {
					assert ((AnnotatedTerm) atom).getAnnotations()[0].getKey() == ProofRules.ANNOT_UNIT;
					atom = ((AnnotatedTerm) atom).getSubterm();
				}
				clause[i] = new ProofLiteral(atom, i < 2);
			}
			return clause;
		}
		case ProofRules.PREFIX + ProofRules.XORE: {
			assert params.length == 3;
			assert ProofRules.checkXorParams(params);
			// ~(xor set0), ~(xor set1), ~(xor set2)
			final ProofLiteral[] clause = new ProofLiteral[3];
			for (int i = 0; i < 3; i++) {
				Term atom = params[i];
				if (atom instanceof AnnotatedTerm) {
					assert ((AnnotatedTerm) atom).getAnnotations()[0].getKey() == ProofRules.ANNOT_UNIT;
					atom = ((AnnotatedTerm) atom).getSubterm();
				}
				clause[i] = new ProofLiteral(atom, false);
			}
			return clause;
		}
		case ProofRules.PREFIX + ProofRules.EQI: {
			assert params.length == 1;
			final ApplicationTerm subterm = (ApplicationTerm) params[0];
			assert subterm.getFunction().getName() == SMTLIBConstants.EQUALS;
			final Term[] subParams = subterm.getParameters();
			final Theory t = axiom.getTheory();

			// (= t1 ... tn), ~(= t1 t2), ~(tn-1 tn)
			final ProofLiteral[] clause = new ProofLiteral[subParams.length];
			clause[0] = new ProofLiteral(subterm, true);
			for (int i = 0; i < subParams.length - 1; i++) {
				clause[i + 1] = new ProofLiteral(t.term(SMTLIBConstants.EQUALS, subParams[i], subParams[i + 1]), false);
			}
			return clause;
		}
		case ProofRules.PREFIX + ProofRules.EQE: {
			assert params.length == 1;
			final AnnotatedTerm annotTerm = (AnnotatedTerm) params[0];
			final Annotation[] annots = annotTerm.getAnnotations();
			assert annots.length == 1 && annots[0].getKey().equals(ProofRules.ANNOT_POS);
			final ApplicationTerm subterm = (ApplicationTerm) annotTerm.getSubterm();
			assert subterm.getFunction().getName() == SMTLIBConstants.EQUALS;
			final Term[] subParams = subterm.getParameters();
			final Object[] positions = (Object[]) annots[0].getValue();
			assert positions.length == 2;
			final int pos0 = (Integer) positions[0];
			final int pos1 = (Integer) positions[1];
			assert 0 <= pos0 && pos0 < subParams.length && 0 <= pos1 && pos1 < subParams.length;
			final Theory t = axiom.getTheory();

			// ~(= t1 ... tn), (= ti tj)
			return new ProofLiteral[] { new ProofLiteral(subterm, false),
					new ProofLiteral(t.term(SMTLIBConstants.EQUALS, subParams[pos0], subParams[pos1]), true) };
		}
		case ProofRules.PREFIX + ProofRules.DISTINCTI: {
			assert params.length == 1;
			final ApplicationTerm subterm = (ApplicationTerm) params[0];
			assert subterm.getFunction().getName() == SMTLIBConstants.DISTINCT;
			final Term[] subParams = subterm.getParameters();
			final Theory t = axiom.getTheory();
			final int len = subParams.length;

			// (distinct t1 ... tn), (= t1 t2),...
			final ProofLiteral[] clause = new ProofLiteral[1 + len * (len - 1) / 2];
			clause[0] = new ProofLiteral(subterm, true);
			int pos = 0;
			for (int i = 0; i < len - 1; i++) {
				for (int j = i + 1; j < len; j++) {
					clause[pos++] = new ProofLiteral(t.term(SMTLIBConstants.EQUALS, subParams[i], subParams[j]), true);
				}
			}
			assert pos == clause.length;
			return clause;
		}
		case ProofRules.PREFIX + ProofRules.DISTINCTE: {
			assert params.length == 1;
			final AnnotatedTerm annotTerm = (AnnotatedTerm) params[0];
			final Annotation[] annots = annotTerm.getAnnotations();
			assert annots.length == 1 && annots[0].getKey().equals(ProofRules.ANNOT_POS);
			final ApplicationTerm subterm = (ApplicationTerm) annotTerm.getSubterm();
			assert subterm.getFunction().getName() == SMTLIBConstants.DISTINCT;
			final Term[] subParams = subterm.getParameters();
			final Object[] positions = (Object[]) annots[0].getValue();
			assert positions.length == 2;
			final int pos0 = (Integer) positions[0];
			final int pos1 = (Integer) positions[1];
			assert 0 <= pos0 && pos0 < subParams.length && 0 <= pos1 && pos1 < subParams.length;
			final Theory t = axiom.getTheory();

			// ~(distinct t1 ... tn), ~(= ti tj)
			return new ProofLiteral[] { new ProofLiteral(subterm, false),
					new ProofLiteral(t.term(SMTLIBConstants.EQUALS, subParams[pos0], subParams[pos1]), false) };
		}
		case ProofRules.PREFIX + ProofRules.ITE1: {
			assert params.length == 1;
			final ApplicationTerm subterm = (ApplicationTerm) params[0];
			assert subterm.getFunction().getName() == SMTLIBConstants.ITE;
			final Term[] subParams = subterm.getParameters();
			assert subParams.length == 3;
			final Theory t = axiom.getTheory();

			// (= (ite c t e) t), ~c
			return new ProofLiteral[] { new ProofLiteral(t.term(SMTLIBConstants.EQUALS, params[0], subParams[1]), true),
					new ProofLiteral(subParams[0], false) };
		}
		case ProofRules.PREFIX + ProofRules.ITE2: {
			assert params.length == 1;
			final ApplicationTerm subterm = (ApplicationTerm) params[0];
			assert subterm.getFunction().getName() == SMTLIBConstants.ITE;
			final Term[] subParams = subterm.getParameters();
			assert subParams.length == 3;
			final Theory t = axiom.getTheory();

			// (= (ite c t e) e), c
			return new ProofLiteral[] { new ProofLiteral(t.term(SMTLIBConstants.EQUALS, params[0], subParams[2]), true),
					new ProofLiteral(subParams[0], true) };
		}
		case ProofRules.PREFIX + ProofRules.DELANNOT: {
			assert params.length == 1;
			final AnnotatedTerm annotTerm = (AnnotatedTerm) params[0];
			final Term subterm = annotTerm.getSubterm();
			final Theory t = axiom.getTheory();

			// (= (! t :...) t)
			return new ProofLiteral[] { new ProofLiteral(t.term(SMTLIBConstants.EQUALS, annotTerm, subterm), true) };
		}
		case ProofRules.PREFIX + ProofRules.REFL: {
			assert params.length == 1;
			final Theory t = axiom.getTheory();

			// (= a a)
			return new ProofLiteral[] { new ProofLiteral(t.term(SMTLIBConstants.EQUALS, params[0], params[0]), true) };
		}
		case ProofRules.PREFIX + ProofRules.SYMM: {
			assert params.length == 1;
			final ApplicationTerm subterm = (ApplicationTerm) params[0];
			assert subterm.getFunction().getName() == SMTLIBConstants.EQUALS;
			final Term subParams[] = subterm.getParameters();
			assert subParams.length == 2;
			final Theory t = axiom.getTheory();

			// (= a0 a1), ~(= a1 a0)
			return new ProofLiteral[] { new ProofLiteral(subterm, true),
					new ProofLiteral(t.term(SMTLIBConstants.EQUALS, subParams[1], subParams[0]), false) };
		}
		case ProofRules.PREFIX + ProofRules.TRANS: {
			assert params.length == 1;
			final ApplicationTerm subterm = (ApplicationTerm) params[0];
			assert subterm.getFunction().getName() == SMTLIBConstants.EQUALS;
			final Term subParams[] = subterm.getParameters();
			assert subParams.length > 2;
			final int len = subParams.length;
			final Theory t = axiom.getTheory();

			// (= a0 alen-1), ~(= a0 a1), ..., ~(= alen-2 alen-1)
			final ProofLiteral[] clause = new ProofLiteral[len];
			clause[0] = new ProofLiteral(t.term(SMTLIBConstants.EQUALS, subParams[0], subParams[len - 1]), true);
			for (int i = 0; i < len - 1; i++) {
				clause[i + 1] = new ProofLiteral(t.term(SMTLIBConstants.EQUALS, subParams[i], subParams[i + 1]), false);
			}
			return clause;
		}
		case ProofRules.PREFIX + ProofRules.CONG: {
			assert params.length == 1;
			final ApplicationTerm subterm = (ApplicationTerm) params[0];
			assert subterm.getFunction().getName() == SMTLIBConstants.EQUALS;
			final Term subParams[] = subterm.getParameters();
			assert subParams.length == 2;
			final ApplicationTerm appTerm0 = (ApplicationTerm) subParams[0];
			final ApplicationTerm appTerm1 = (ApplicationTerm) subParams[1];
			assert (appTerm0.getFunction() == appTerm1.getFunction());
			final Term[] params0 = appTerm0.getParameters();
			final Term[] params1 = appTerm1.getParameters();
			assert params0.length == params1.length;
			final Theory t = axiom.getTheory();

			// (= (f a0...an) (f b0... bn)), ~(= a0 b0), ..., ~(= an bn)
			final ProofLiteral[] clause = new ProofLiteral[params0.length + 1];
			clause[0] = new ProofLiteral(subterm, true);
			for (int i = 0; i < params0.length; i++) {
				clause[i + 1] = new ProofLiteral(t.term(SMTLIBConstants.EQUALS, params0[i], params1[i]), false);
			}
			return clause;
		}
		default:
			throw new AssertionError("Unknown axiom " + axiom);
		}
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
		final ApplicationTerm mTerm;

		public ProofWalker(Term term) {
			assert term.getSort().getName().equals(ProofRules.PREFIX + ProofRules.PROOF);
			while (term instanceof AnnotatedTerm) {
				term = ((AnnotatedTerm) term).getSubterm();
			}
			mTerm = (ApplicationTerm) term;
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
			assert ProofRules.isProofRule(ProofRules.RES, term);
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
