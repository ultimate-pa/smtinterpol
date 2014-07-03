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

import java.math.BigDecimal;
import java.math.BigInteger;
import java.util.ArrayList;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.logic.AnnotatedTerm;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.ConstantTerm;
import de.uni_freiburg.informatik.ultimate.logic.FunctionSymbol;
import de.uni_freiburg.informatik.ultimate.logic.LetTerm;
import de.uni_freiburg.informatik.ultimate.logic.NonRecursive;
import de.uni_freiburg.informatik.ultimate.logic.QuantifiedFormula;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.logic.Theory;

public class NeutralDetector extends NonRecursive {

	private static class NeutralWalker extends TermWalker {

		public NeutralWalker(Term term) {
			super(term);
		}
		
		@Override
		public void walk(NonRecursive walker, ConstantTerm term) {
			// Nothing to do
		}

		@Override
		public void walk(NonRecursive walker, AnnotatedTerm term) {
			walker.enqueueWalker(new NeutralWalker(term.getSubterm()));
		}

		@Override
		public void walk(NonRecursive walker, ApplicationTerm term) {
			NeutralDetector detector = (NeutralDetector) walker;
			FunctionSymbol fsym = term.getFunction();
			Theory t = fsym.getTheory();
			if (fsym == t.mAnd || fsym == t.mOr) {
				Term neutral = fsym == t.mAnd ? t.mTrue : t.mFalse;
				Term[] params = term.getParameters();
				for (int i = 0; i < params.length; ++i) {
					if (params[i] == neutral)
						detector.mNeutrals.add(new Neutral(term, i));
					else
						detector.enqueueWalker(new NeutralWalker(params[i]));
				}
			}
			if (fsym.getName().equals("+") || fsym.getName().equals("-")) {
				int start = fsym.getName().equals("+") ? 0 : 1;
				Term[] params = term.getParameters();
				for (int i = start; i < params.length; ++i) {
					if (isZero(params[i]))
						detector.mNeutrals.add(new Neutral(term, i));
					else
						detector.enqueueWalker(new NeutralWalker(params[i]));
				}
			}
		}

		@Override
		public void walk(NonRecursive walker, LetTerm term) {
			for (Term t : term.getValues())
				walker.enqueueWalker(new NeutralWalker(t));
			walker.enqueueWalker(new NeutralWalker(term.getSubTerm()));
		}

		@Override
		public void walk(NonRecursive walker, QuantifiedFormula term) {
			walker.enqueueWalker(new NeutralWalker(term.getSubformula()));
		}

		@Override
		public void walk(NonRecursive walker, TermVariable term) {
			// Nothing to do
		}
		
	}
	
	private final ArrayList<Neutral> mNeutrals = new ArrayList<Neutral>();
	
	private static boolean isZero(Term t) {
		if (t instanceof ConstantTerm) {
			ConstantTerm ct = (ConstantTerm) t;
			Object val = ct.getValue();
			if (val instanceof BigInteger)
				return BigInteger.ZERO.equals(val);
			if (val instanceof BigDecimal)
				return BigDecimal.ZERO.equals(val);
			if (val instanceof Rational)
				return Rational.ZERO.equals(val);
		}
		return false;
	}
	
	public List<Neutral> detect(Term t) {
		run(new NeutralWalker(t));
		return mNeutrals;
	}
}
