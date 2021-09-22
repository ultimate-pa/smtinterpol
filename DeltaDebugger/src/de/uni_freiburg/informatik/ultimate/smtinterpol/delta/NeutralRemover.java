/*
 * Copyright (C) 2014 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.smtinterpol.delta;

import java.util.ArrayList;
import java.util.Iterator;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.SMTLIBConstants;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermTransformer;

public class NeutralRemover extends TermTransformer {
	private final Iterator<Neutral> mNeutrals;
	private Neutral mNext;

	public NeutralRemover(final List<Neutral> neutrals) {
		mNeutrals = neutrals.iterator();
		mNext = mNeutrals.hasNext() ? mNeutrals.next() : null;
	}

	boolean shouldRemove(final Term t, final int pos) {
		if (mNext != null && mNext.matches(t, pos)) {
			mNext = mNeutrals.hasNext() ? mNeutrals.next() : null;
			return true;
		}
		return false;
	}

	@Override
	public void convert(Term term) {
		if (term instanceof ApplicationTerm) {
			final ApplicationTerm appTerm = (ApplicationTerm) term;
			final Term[] params = appTerm.getParameters();
			final ArrayList<Term> newParams = new ArrayList<>();
			for (int i = 0; i < params.length; ++i) {
				if (!shouldRemove(term, i)) {
					newParams.add(params[i]);
				}
			}
			if (newParams.size() < params.length) {
				if (newParams.size() == 0) {
					// Try to remove the whole term
					if (term.getSort().getName() == SMTLIBConstants.BOOL) {
						term = term.getTheory().mTrue;
					} else {
						term = Rational.ZERO.toTerm(term.getSort());
					}
				} else if (newParams.size() == 1) {
					term = newParams.get(0);
				} else {
					term = term.getTheory().term(appTerm.getFunction(), newParams.toArray(new Term[newParams.size()]));
				}
			}
		}
		super.convert(term);
	}

	public Term removeNeutrals(final Term t) {
		return transform(t);
	}
}
