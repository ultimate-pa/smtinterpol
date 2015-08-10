/*
 * Copyright (C) 2015 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.smtinterpol.simp;

import java.util.IdentityHashMap;

import de.uni_freiburg.informatik.ultimate.logic.AnnotatedTerm;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.ConstantTerm;
import de.uni_freiburg.informatik.ultimate.logic.LetTerm;
import de.uni_freiburg.informatik.ultimate.logic.NonRecursive;
import de.uni_freiburg.informatik.ultimate.logic.QuantifiedFormula;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;

public class FindBooleanInDegree extends NonRecursive {

	private IdentityHashMap<Term, Integer> mBooleanInDegs;

	private class InDegWalker extends TermWalker {

		public InDegWalker(Term term) {
			super(term);
		}

		@Override
		public void walk(NonRecursive walker, ConstantTerm term) {
			// Nothing to do
		}

		@Override
		public void walk(NonRecursive walker, AnnotatedTerm term) {
			walker.enqueueWalker(new InDegWalker(term.getSubterm()));
		}

		@Override
		public void walk(NonRecursive walker, ApplicationTerm term) {
			boolean descend = true;
			if (term.getSort() == term.getTheory().getBooleanSort()) {
				FindBooleanInDegree fbid = (FindBooleanInDegree) walker;
				descend &= fbid.inc(term);
			}
			if (descend) {
				for (Term t : term.getParameters())
					walker.enqueueWalker(new InDegWalker(t));
			}
		}

		@Override
		public void walk(NonRecursive walker, LetTerm term) {
			throw new AssertionError("Lets should be removed by FormulaUnLet");
		}

		@Override
		public void walk(NonRecursive walker, QuantifiedFormula term) {
			throw new UnsupportedOperationException();
		}

		@Override
		public void walk(NonRecursive walker, TermVariable term) {
			throw new UnsupportedOperationException();
		}

	}

	boolean inc(Term t) {
		boolean res = false;
		Integer val = mBooleanInDegs.get(t);
		if (val == null) {
			val = 0;
			res = true;
		}
		mBooleanInDegs.put(t, val + 1);
		return res;
	}

	public IdentityHashMap<Term, Integer> getBooleanInDegs(Term t) {
		mBooleanInDegs = new IdentityHashMap<Term, Integer>();
		run(new InDegWalker(t));
		IdentityHashMap<Term, Integer> res = mBooleanInDegs;
		mBooleanInDegs = null;
		return res;
	}

}
