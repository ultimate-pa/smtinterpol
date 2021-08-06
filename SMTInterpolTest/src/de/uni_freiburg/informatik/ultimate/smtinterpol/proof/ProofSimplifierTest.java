/*
 * Copyright (C) 2012-2013 University of Freiburg
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
import java.util.HashSet;
import java.util.Random;

import org.junit.Assert;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.JUnit4;

import de.uni_freiburg.informatik.ultimate.logic.AnnotatedTerm;
import de.uni_freiburg.informatik.ultimate.logic.Annotation;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.Logics;
import de.uni_freiburg.informatik.ultimate.logic.SMTLIBConstants;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.Theory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.smtlib2.SMTInterpol;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.cclosure.CCEquality;

@RunWith(JUnit4.class)
public class ProofSimplifierTest {

	private final SMTInterpol mSmtInterpol;
	private final Theory mTheory;
	private final Random rng = new Random(123456);
	private final ProofSimplifier mSimplifier;
	private final MinimalProofChecker mProofChecker;

	public ProofSimplifierTest() {
		mSmtInterpol = new SMTInterpol();
		mSmtInterpol.setOption(SMTLIBConstants.PRODUCE_PROOFS, SMTLIBConstants.TRUE);
		mSmtInterpol.setOption(SMTLIBConstants.INTERACTIVE_MODE, SMTLIBConstants.TRUE);
		mSmtInterpol.setLogic(Logics.ALL);
		mTheory = mSmtInterpol.getTheory();
		mSimplifier = new ProofSimplifier(mSmtInterpol);
		mProofChecker = new MinimalProofChecker(mSmtInterpol, mSmtInterpol.getLogger());
		mSmtInterpol.declareSort("U", 0);
	}

	private Object[] shuffle(final Object[] o) {
		for (int i = 1; i < o.length; i++) {
			final int randomPos = rng.nextInt(i);
			final Object swap = o[i];
			o[i] = o[randomPos];
			o[randomPos] = swap;
		}
		return o;
	}

	public Term[] generateDummyTerms(final int len, final Sort sort) {
		final Term[] terms = new Term[len];
		for (int i = 0; i < len; i++) {
			mSmtInterpol.declareFun("x" + i, new Sort[0], sort);
			terms[i] = mSmtInterpol.term("x" + i);
		}
		return terms;
	}

	public Term generateTransitivity(final int len, final int swapFlags) {
		final Sort U = mSmtInterpol.sort("U");
		final Term[] terms = generateDummyTerms(len, U);
		final Term[] eqs   = new Term[len];
		for (int i = 0; i < len; i++) {
			if (i > 0) {
				eqs[i-1] = (swapFlags & (1<< (i-1))) != 0 ? mTheory.term("=", terms[i-1],terms[i]) : mTheory.term("=", terms[i],terms[i-1]);
			}
		}
		eqs[len - 1] = (swapFlags & (1<< (len-1))) != 0 ? mTheory.term("=", terms[0],terms[len-1]) : mTheory.term("=", terms[len-1],terms[0]);
		final Term[] quotedEqs   = new Term[len];
		for (int i = 0; i < len; i++) {
			quotedEqs[i] = mSmtInterpol.annotate(eqs[i], CCEquality.QUOTED_CC);
		}
		final Term[] orParams = new Term[len];
		for (int i = 0; i < len; i++) {
			orParams[i] = i == len - 1 ? quotedEqs[i] : mSmtInterpol.term("not", quotedEqs[i]);
		}
		final Term clause = mSmtInterpol.term("or", (Term[]) shuffle(orParams));
		final Object[] subannots = new Object[] {
			quotedEqs[len-1],
			":subpath",
			terms
		};
		final Annotation[] lemmaAnnots = new Annotation[] { new Annotation(":CC", subannots) };
		final Term lemma = mSmtInterpol.term(ProofConstants.FN_LEMMA,
				mSmtInterpol.annotate(clause, lemmaAnnots));
		return lemma;
	}

	void checkLemmaOrRewrite(final Term lemma, final Term[] lits) {
		final HashSet<ProofLiteral> expected = new HashSet<>();
		for (int i = 0; i < lits.length; i++) {
			if (lits[i] instanceof ApplicationTerm
					&& ((ApplicationTerm) lits[i]).getFunction().getName() == SMTLIBConstants.NOT) {
				expected.add(new ProofLiteral(((ApplicationTerm) lits[i]).getParameters()[0], false));
			} else {
				expected.add(new ProofLiteral(lits[i], true));
			}
		}
		final Term simpleLemma = mSimplifier.transform(lemma);
		final ProofLiteral[] provedLits = mProofChecker.getProvedClause(simpleLemma);
		final HashSet<ProofLiteral> actual = new HashSet<>(Arrays.asList(provedLits));
		Assert.assertEquals(expected, actual);
	}

	@Test
	public void testCCLemma() {
		for (int len = 3; len < 5; len++) {
			for (int flags = 0; flags < (1 << len); flags++) {
				mSmtInterpol.push(1);
				final Term transLemma = generateTransitivity(len, flags);
				final Term clause = ((AnnotatedTerm) ((ApplicationTerm) transLemma).getParameters()[0]).getSubterm();
				final Term[] orParams = ((ApplicationTerm) clause).getParameters();
				checkLemmaOrRewrite(transLemma, orParams);
				mSmtInterpol.pop(1);
			}
		}
	}

	@Test
	public void testEqSameRewrite() {
		mSmtInterpol.push(1);
		final Sort U = mSmtInterpol.sort("U");
		final Term[] terms = generateDummyTerms(5, U);

		for (int i = 0; i < 1000; i++) {
			final int len = rng.nextInt(10) + 2;
			final Term[] lhsTerms = new Term[len];
			for (int j = 0; j < len; j++) {
				lhsTerms[j] = terms[rng.nextInt(terms.length)];
			}
			final HashSet<Term> contents = new HashSet<>(Arrays.asList(lhsTerms));
			final Term[] rhsTerms = (Term[]) shuffle(contents.toArray(new Term[contents.size()]));
			final Term rhs = rhsTerms.length == 1 ? mSmtInterpol.term(SMTLIBConstants.TRUE)
					: mSmtInterpol.term("=", rhsTerms);

			final Term equality = mSmtInterpol.term("=", mSmtInterpol.term("=", lhsTerms), rhs);
			final Term rewriteEqSimp = mSmtInterpol.term(ProofConstants.FN_REWRITE, mSmtInterpol.annotate(equality,
					rhsTerms.length == 1 ? ProofConstants.RW_EQ_SAME : ProofConstants.RW_EQ_SIMP));
			checkLemmaOrRewrite(rewriteEqSimp, new Term[] { equality });
		}
		mSmtInterpol.pop(1);
	}

	@Test
	public void testEqDistinctRewrite() {

		{
			mSmtInterpol.push(1);
			final Term[] terms = generateDummyTerms(5, mSmtInterpol.sort("Bool"));
			final Term equality = mSmtInterpol.term("=", mSmtInterpol.term("distinct", terms),
					mSmtInterpol.term(SMTLIBConstants.FALSE));
			final Term rewriteEqSimp = mSmtInterpol.term(ProofConstants.FN_REWRITE,
					mSmtInterpol.annotate(equality, ProofConstants.RW_DISTINCT_BOOL));
			checkLemmaOrRewrite(rewriteEqSimp, new Term[] { equality });
			mSmtInterpol.pop(1);
		}

		{
			mSmtInterpol.push(1);
			final Term[] terms = generateDummyTerms(5, mSmtInterpol.sort("U"));
			terms[4] = terms[2];
			final Term equality = mSmtInterpol.term("=", mSmtInterpol.term("distinct", terms),
					mSmtInterpol.term(SMTLIBConstants.FALSE));
			final Term rewriteEqSimp = mSmtInterpol.term(ProofConstants.FN_REWRITE,
					mSmtInterpol.annotate(equality, ProofConstants.RW_DISTINCT_SAME));
			checkLemmaOrRewrite(rewriteEqSimp, new Term[] { equality });
			mSmtInterpol.pop(1);
		}

		for (int len = 2; len < 5; len++) {
			mSmtInterpol.push(1);
			final Term[] terms = generateDummyTerms(len, mSmtInterpol.sort("U"));
			final Term[] orParams = new Term[len * (len - 1) / 2];
			int offset = 0;
			for (int i = 0; i < terms.length; i++) {
				for (int j = i + 1; j < terms.length; j++) {
					orParams[offset++] = mSmtInterpol.term(SMTLIBConstants.EQUALS, terms[i], terms[j]);
				}
			}
			final Term orTerm = orParams.length == 1 ? orParams[0] : mSmtInterpol.term(SMTLIBConstants.OR, orParams);
			final Term equality = mSmtInterpol.term("=", mSmtInterpol.term("distinct", terms),
					mSmtInterpol.term(SMTLIBConstants.NOT, orTerm));
			final Term rewriteEqSimp = mSmtInterpol.term(ProofConstants.FN_REWRITE,
					mSmtInterpol.annotate(equality, ProofConstants.RW_DISTINCT_BINARY));
			checkLemmaOrRewrite(rewriteEqSimp, new Term[] { equality });
			mSmtInterpol.pop(1);
		}
	}

	@Test
	public void testEqToXorRewrite() {
		mSmtInterpol.push(1);
		final Sort U = mSmtInterpol.sort("Bool");
		final Term[] terms = generateDummyTerms(2, U);

		// convert equality to not xor, simplify the xor term and possibly remove double
		// negation.
		final Term eqTerm = mSmtInterpol.term("=", terms);
		final Term xorTerm = mSmtInterpol.term("xor", terms);
		final Term equality = mSmtInterpol.term("=", eqTerm, mSmtInterpol.term("not", xorTerm));
		final Term rewriteEqSimp = mSmtInterpol.term(ProofConstants.FN_REWRITE,
				mSmtInterpol.annotate(equality, ProofConstants.RW_EQ_TO_XOR));
		checkLemmaOrRewrite(rewriteEqSimp, new Term[] { equality });
		mSmtInterpol.pop(1);
	}

}
