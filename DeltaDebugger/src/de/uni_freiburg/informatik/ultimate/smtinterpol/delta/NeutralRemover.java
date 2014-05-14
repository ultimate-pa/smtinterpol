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

import java.util.ArrayDeque;
import java.util.Iterator;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.logic.AnnotatedTerm;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.ConstantTerm;
import de.uni_freiburg.informatik.ultimate.logic.LetTerm;
import de.uni_freiburg.informatik.ultimate.logic.NonRecursive;
import de.uni_freiburg.informatik.ultimate.logic.QuantifiedFormula;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.logic.Theory;

public class NeutralRemover extends NonRecursive {
	
	private static class BuildAnnotationTerm implements Walker {
		private final AnnotatedTerm mAnnot;
		public BuildAnnotationTerm(AnnotatedTerm annot) {
			mAnnot = annot;
		}
		@Override
		public void walk(NonRecursive engine) {
			NeutralRemover remover = (NeutralRemover) engine;
			Term sub = remover.getConverted();
			remover.setResult(sub == mAnnot.getSubterm()
					? mAnnot
						: mAnnot.getTheory().annotatedTerm(
								mAnnot.getAnnotations(), sub));
		}
	}
	
	private static class BuildApplicationTerm implements Walker {
		private final ApplicationTerm mApp;
		private int mNumParams;
		public BuildApplicationTerm(ApplicationTerm app) {
			mApp = app;
		}
		public void setParamCount(int count) {
			mNumParams = count;
		}
		@Override
		public void walk(NonRecursive engine) {
			NeutralRemover remover = (NeutralRemover) engine;
			System.err.println("Building ApplicationTerm: " + mApp + " @ "+ mNumParams);
			if (mApp.getParameters().length == mNumParams)
				remover.setResult(mApp);
			else if (mNumParams == 0) {
				// Try to remove the whole term
				if (mApp.getSort() == mApp.getTheory().getBooleanSort())
					remover.setResult(mApp.getTheory().mTrue);
				else
					remover.setResult(Rational.ZERO.toTerm(mApp.getSort()));
			} else if (mNumParams == 1)
				remover.setResult(remover.getConverted());
			else {
				Term[] params = remover.getConverted(mNumParams);
				remover.setResult(mApp.getTheory().term(
						mApp.getFunction(), params));
			}
		}
	}
	
	private static class BuildLetTerm implements Walker {
		private final LetTerm mLet;
		public BuildLetTerm(LetTerm let) {
			mLet = let;
		}
		@Override
		public void walk(NonRecursive engine) {
			NeutralRemover remover = (NeutralRemover) engine;
			Term[] values = remover.getConverted(mLet.getValues().length);
			Term sub = remover.getConverted();
			remover.setResult(sub.getTheory().let(
					mLet.getVariables(), values, sub));
		}
	}
	
	private static class BuildQuantifiedFormula implements Walker {
		private final QuantifiedFormula mQuant;
		public BuildQuantifiedFormula(QuantifiedFormula quant) {
			mQuant = quant;
		}
		@Override
		public void walk(NonRecursive engine) {
			NeutralRemover remover = (NeutralRemover) engine;
			Term sub = remover.getConverted();
			Theory t = sub.getTheory();
			if (sub == mQuant.getSubformula())
				remover.setResult(mQuant);
			else if (mQuant.getQuantifier() == QuantifiedFormula.EXISTS)
				remover.setResult(t.exists(mQuant.getVariables(), sub));
			else
				remover.setResult(t.forall(mQuant.getVariables(), sub));
		}
	}

	private static class NeutralWalker extends TermWalker {
		
		public NeutralWalker(Term t) {
			super(t);
		}

		@Override
		public void walk(NonRecursive walker, ConstantTerm term) {
			((NeutralRemover) walker).setResult(term);
		}

		@Override
		public void walk(NonRecursive walker, AnnotatedTerm term) {
			walker.enqueueWalker(new BuildAnnotationTerm(term));
			walker.enqueueWalker(new NeutralWalker(term.getSubterm()));
		}

		@Override
		public void walk(NonRecursive walker, ApplicationTerm term) {
			NeutralRemover remover = (NeutralRemover) walker;
			BuildApplicationTerm bat = new BuildApplicationTerm(term);
			walker.enqueueWalker(bat);
			int paramsPushed = 0;
			Term[] params = term.getParameters();
			for (int i = 0; i < params.length; ++i) {
				if (!remover.shouldRemove(term, i)) {
					walker.enqueueWalker(new NeutralWalker(params[i]));
					++paramsPushed;
				}
			}
			bat.setParamCount(paramsPushed);
		}

		@Override
		public void walk(NonRecursive walker, LetTerm term) {
			walker.enqueueWalker(new BuildLetTerm(term));
			for (Term v : term.getValues())
				walker.enqueueWalker(new NeutralWalker(v));
			walker.enqueueWalker(new NeutralWalker(term.getSubTerm()));
		}

		@Override
		public void walk(NonRecursive walker, QuantifiedFormula term) {
			walker.enqueueWalker(new BuildQuantifiedFormula(term));
			walker.enqueueWalker(new NeutralWalker(term.getSubformula()));
		}

		@Override
		public void walk(NonRecursive walker, TermVariable term) {
			((NeutralRemover) walker).setResult(term);
		}
	}
	
	private final ArrayDeque<Term> mConverted = new ArrayDeque<Term>();
	
	private final Iterator<Neutral> mNeutrals;
	private Neutral mNext;
	
	public NeutralRemover(List<Neutral> neutrals) {
		mNeutrals = neutrals.iterator();
		mNext = mNeutrals.hasNext() ? mNeutrals.next() : null;
	}
	
	boolean shouldRemove(Term t, int pos) {
		if (mNext != null && mNext.matches(t, pos)) {
			mNext = mNeutrals.hasNext() ? mNeutrals.next() : null;
			return true;
		}
		return false;
	}
	
	void setResult(Term t) {
		mConverted.push(t);
	}
	
	Term[] getConverted(int num) {
		Term[] res = new Term[num];
		for (int i = 0; i < res.length; ++i)
			res[i] = mConverted.pop();
		return res;
	}
	
	Term getConverted() {
		return mConverted.pop();
	}
	
	public Term removeNeutrals(Term t) {
		run(new NeutralWalker(t));
		return mConverted.pop();
	}
	
}
