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
package de.uni_freiburg.informatik.ultimate.smtinterpol.delta;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Iterator;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.logic.AnnotatedTerm;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.ConstantTerm;
import de.uni_freiburg.informatik.ultimate.logic.LetTerm;
import de.uni_freiburg.informatik.ultimate.logic.NonRecursive;
import de.uni_freiburg.informatik.ultimate.logic.QuantifiedFormula;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.logic.Theory;

public class SubstitutionApplier extends NonRecursive {
	
	private final class AnnotationBuilder implements Walker {
		
		private final AnnotatedTerm mTerm;
		
		public AnnotationBuilder(AnnotatedTerm term) {
			mTerm = term;
		}

		@Override
		public void walk(NonRecursive engine) {
			Term converted = mConverted.pop();
			Term res = converted.getTheory().annotatedTerm(
					mTerm.getAnnotations(), converted);
			mConverted.push(res);
		}
		
	}
	
	private final class ApplicationTermBuilder implements Walker {
		
		private final ApplicationTerm mTerm;
		
		public ApplicationTermBuilder(ApplicationTerm term) {
			mTerm = term;
		}

		@Override
		public void walk(NonRecursive engine) {
			Term[] newArgs = new Term[mTerm.getParameters().length];
			for (int i = 0; i < newArgs.length; ++i)
				newArgs[i] = mConverted.pop();
			Term res = mTerm.getTheory().term(mTerm.getFunction(), newArgs);
			mConverted.push(res);
		}
		
	}
	
	private final class LetBuilder implements Walker {
		
		private final LetTerm mTerm;
		
		public LetBuilder(LetTerm term) {
			mTerm = term;
		}

		@Override
		public void walk(NonRecursive engine) {
			Term[] newVals = new Term[mTerm.getValues().length];
			for (int i = 0; i < newVals.length; ++i)
				newVals[i] = mConverted.pop();
			Term subform = mConverted.pop();
			Term res = mTerm.getTheory().let(
					mTerm.getVariables(), newVals, subform);
			mConverted.push(res);
		}
		
	}
	
	private final class QuantifierBuilder implements Walker {

		private final QuantifiedFormula mTerm;
		
		public QuantifierBuilder(QuantifiedFormula term) {
			mTerm = term;
		}
		
		@Override
		public void walk(NonRecursive engine) {
			Term subform = mConverted.pop();
			Theory t = mTerm.getTheory();
			Term res = mTerm.getQuantifier() == QuantifiedFormula.EXISTS
					? t.exists(mTerm.getVariables(), subform)
						: t.forall(mTerm.getVariables(), subform);
			mConverted.push(res);
		}
		
	}
	
	private final class DepthDescender extends TermWalker {

		private final int mDepth;
		
		public DepthDescender(Term term, int depth) {
			super(term);
			mDepth = depth;
		}

		@Override
		public void walk(NonRecursive walker) {
			if (mDepth == SubstitutionApplier.this.mDepth) {
				// Apply substitution
				boolean expectedTrue = mIt.hasNext();
				assert expectedTrue;
				if (mSubst != null && mSubst.matches(getTerm())) {
					if (mSubst.isActive()) {
						mConverted.push(mSubst.apply(getTerm()));
						Cmd add = mSubst.getAdditionalCmd(getTerm());
						if (add != null)
							mAdds.add(add);
					} else
						mConverted.push(getTerm());
					// We can step here since we found a (possibly deactivated)
					// match.  If the term does not match, we should not step!
					stepSubst();
				} else {
					// We don't need to descend since we will never change
					// anything at lower depths.
					mConverted.push(getTerm());
				}
			} else
				super.walk(walker);
		}

		@Override
		public void walk(NonRecursive walker, ConstantTerm term) {
			mConverted.push(term);
		}

		@Override
		public void walk(NonRecursive walker, AnnotatedTerm term) {
			walker.enqueueWalker(new AnnotationBuilder(term));
			walker.enqueueWalker(
					new DepthDescender(term.getSubterm(), mDepth + 1));
		}

		@Override
		public void walk(NonRecursive walker, ApplicationTerm term) {
			walker.enqueueWalker(new ApplicationTermBuilder(term));
			for (Term p : term.getParameters())
				walker.enqueueWalker(new DepthDescender(p, mDepth + 1));
		}

		@Override
		public void walk(NonRecursive walker, LetTerm term) {
			walker.enqueueWalker(new LetBuilder(term));
			for (Term v : term.getValues())
				walker.enqueueWalker(new DepthDescender(v, mDepth + 1));
			walker.enqueueWalker(
					new DepthDescender(term.getSubTerm(), mDepth + 1));
		}

		@Override
		public void walk(NonRecursive walker, QuantifiedFormula term) {
			walker.enqueueWalker(new QuantifierBuilder(term));
			walker.enqueueWalker(
					new DepthDescender(term.getSubformula(), mDepth + 1));
		}

		@Override
		public void walk(NonRecursive walker, TermVariable term) {
			mConverted.push(term);
		}
		
	}
	
	private int mDepth;
	private List<Substitution> mSubsts;// NOPMD
	private Iterator<Substitution> mIt;
	private Substitution mSubst;
	
	private final ArrayDeque<Term> mConverted = new ArrayDeque<Term>();
	private List<Cmd> mAdds = new ArrayList<Cmd>();

	void stepSubst() {
		while (mIt.hasNext()) {
			mSubst = mIt.next();
			if (!mSubst.isSuccess())
				return;
		}
		mSubst = null;
	}
	
	public void init(int depth, List<Substitution> substs) {
		mDepth = depth;
		mSubsts = substs;
		mIt = mSubsts.iterator();
		stepSubst();
	}
	
	public Term apply(Term term) {
		run(new DepthDescender(term, 0));
		return mConverted.pop();
	}
	
	public List<Cmd> getAdds() {
		List<Cmd> res = mAdds;
		mAdds = new ArrayList<Cmd>();
		return res;
	}
	
}
