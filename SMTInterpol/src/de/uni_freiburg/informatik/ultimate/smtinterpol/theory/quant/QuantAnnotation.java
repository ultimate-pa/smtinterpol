/*
 * Copyright (C) 2019 University of Freiburg
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

import java.util.Map;

import de.uni_freiburg.informatik.ultimate.logic.Annotation;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.logic.Theory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.Clause;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.IAnnotation;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.ILiteral;
import de.uni_freiburg.informatik.ultimate.smtinterpol.proof.ProofConstants;

/**
 * Annotation for quantifier theory lemmas.
 * 
 * A quantifier theory lemma is an instance of a quantified clause. It is annotated with the quantified clause and the
 * substitution used to produce the instance.
 * 
 * @author Tanja Schindler
 *
 */
public class QuantAnnotation implements IAnnotation {

	private final Term mQuantClauseTerm;
	private final TermVariable[] mVars;
	private final Term[] mSubs;

	public QuantAnnotation(final QuantClause qClause, final Term[] subs) {
		mQuantClauseTerm = qClause.toTerm(qClause.getQuantTheory().getTheory());
		mVars = qClause.getVars();
		mSubs = subs;
	}

	public QuantAnnotation(final ILiteral[] lits, final Map<TermVariable, Term> subs, final Theory theory) {
		final Term[] litTerms = new Term[lits.length];
		for (int i = 0; i < lits.length; i++) {
			litTerms[i] = lits[i].getSMTFormula(theory, false);
		}
		mQuantClauseTerm = theory.or(litTerms);
		mVars = subs.keySet().toArray(new TermVariable[subs.keySet().size()]);
		mSubs = new Term[mVars.length];
		for (int i = 0; i < mVars.length; i++) {
			mSubs[i] = subs.get(mVars[i]);
		}
	}

	@Override
	public Term toTerm(Clause cls, Theory theory) {
		final Term base = cls.toTerm(theory);
		final Object[] subannots = new Object[6];
		subannots[0] = ":quantClause";
		subannots[1] = mQuantClauseTerm;
		subannots[2] = ":vars";
		subannots[3] = mVars;
		subannots[4] = ":subs";
		subannots[5] = mSubs;
		final Annotation[] annots = new Annotation[] { new Annotation(":inst", subannots) };
		return theory.term(ProofConstants.FN_LEMMA, theory.annotatedTerm(annots, base));
	}

	@Override
	public String toString() {
		final StringBuilder sb = new StringBuilder();
		sb.append(":inst ").append(mQuantClauseTerm.toString());
		sb.append(" :vars ").append(mVars.toString());
		sb.append(" :subs ").append(mSubs.toString());
		return sb.toString();
	}
}
