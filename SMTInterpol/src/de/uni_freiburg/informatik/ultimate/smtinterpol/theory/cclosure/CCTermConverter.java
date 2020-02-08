/*
 * Copyright (C) 2009-2018 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.smtinterpol.theory.cclosure;

import java.util.ArrayList;

import de.uni_freiburg.informatik.ultimate.logic.FunctionSymbol;
import de.uni_freiburg.informatik.ultimate.logic.NonRecursive;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.Theory;

/**
 * This class converts CCTerm to Term (SMTLIB) non-recursively.
 *
 * @author Jochen Hoenicke
 *
 */
public class CCTermConverter extends NonRecursive {
	private final Theory mTheory;
	private ArrayList<Term> mConverted;

	private static class ConvertCC implements NonRecursive.Walker {
		private final CCTerm mTerm;
		private final int mNumArgs;
		private final CCTerm mFullTerm;

		public ConvertCC(final CCTerm input, final int numArgs, final CCTerm fullInput) {
			mTerm = input;
			mNumArgs = numArgs;
			mFullTerm = fullInput;
		}

		@Override
		public void walk(final NonRecursive engine) {
			((CCTermConverter) engine).walkCCTerm(mTerm, mNumArgs, mFullTerm);
		}

	}

	/**
	 * Create the class to convert CCTerm to SMT Term. Note that CCTerm.toSMTTerm() will do this work for you.
	 *
	 * @param theory
	 *            The SMTLIB theory where the terms live. This must match the theory used to create these terms.
	 */
	public CCTermConverter(final Theory theory) {
		mTheory = theory;
	}

	/**
	 * Convert a CCTerm to an SMT term. This is the only function you should call on this class.
	 *
	 * @param input
	 *            the term to convert.
	 * @return the converted term.
	 */
	public Term convert(final CCTerm input) {
		assert mConverted == null;
		mConverted = new ArrayList<>();
		run(new ConvertCC(input, 0, input));
		assert mConverted.size() == 1;
		final Term result = mConverted.remove(0);
		mConverted = null;
		return result;
	}

	private void walkCCTerm(final CCTerm input, final int numArgs, final CCTerm fullTerm) {
		if (input instanceof CCBaseTerm) {
			walkBaseTerm((CCBaseTerm) input, numArgs, fullTerm);
		} else {
			walkAppTerm((CCAppTerm) input, numArgs, fullTerm);
		}
	}

	private void walkAppTerm(final CCAppTerm input, final int numArgs, final CCTerm fullTerm) {
		if (input.mSmtTerm != null) {
			assert numArgs == 0 && fullTerm == input;
			mConverted.add(input.mSmtTerm);
			return;
		}
		enqueueWalker(new ConvertCC(input.getFunc(), numArgs + 1, fullTerm));
		enqueueWalker(new ConvertCC(input.getArg(), 0, input.getArg()));
	}

	private void walkBaseTerm(final CCBaseTerm input, final int numArgs, final CCTerm fullTerm) {
		assert input.mIsFunc == (numArgs > 0);
		final Term[] args = new Term[numArgs];
		for (int i = 0; i < args.length; i++) {
			args[i] = mConverted.remove(mConverted.size() - 1);
		}
		final Object symbol = input.mSymbol;
		final Term converted;
		if (symbol instanceof Term) {
			assert numArgs == 0;
			converted = (Term) symbol;
		} else {
			if (symbol instanceof FunctionSymbol) {
				final FunctionSymbol func = (FunctionSymbol) symbol;
				assert func.getTheory() == mTheory;
				assert func.getParameterSorts().length == numArgs;
				converted = mTheory.term(func, args);
			} else if (symbol instanceof String) {
				converted = mTheory.term((String) symbol, args);
			} else {
				throw new InternalError("Unknown symbol in CCBaseTerm: " + symbol);
			}
		}
		if (numArgs > 0) {
			assert ((CCAppTerm) fullTerm).mSmtTerm == null;
			((CCAppTerm) fullTerm).mSmtTerm = converted;
		}
		mConverted.add(converted);
	}
}
