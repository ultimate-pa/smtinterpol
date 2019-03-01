/*
 * Copyright (C) 2018 University of Freiburg
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

import de.uni_freiburg.informatik.ultimate.logic.FunctionSymbol;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.smtinterpol.convert.Clausifier;

/**
 * Represents a quantified function term, i.e. at least one argument is a quantified EUTerm or a TermVariable.
 * 
 * @author Tanja Schindler
 *
 */
public class QuantAppTerm extends EUTerm {

	private final FunctionSymbol mFunc;
	private final QuantAppArg[] mArgs;

	/**
	 * Create a new QuantAppTerm. This must only be called after checking that the term is essentially uninterpreted,
	 * i.e. that variables appear as arguments of uninterpreted function or predicate symbols only. Additionally, it
	 * must contain at least one variable.
	 */
	QuantAppTerm(final Clausifier clausifier, final Term term, final FunctionSymbol func, final QuantAppArg[] args) {
		super(clausifier, term);
		mFunc = func;
		mArgs = args;
	}

	public FunctionSymbol getFunc() {
		return mFunc;
	}

	public QuantAppArg[] getArgs() {
		return mArgs;
	}
}
