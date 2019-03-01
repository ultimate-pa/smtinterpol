/*
 * Copyright (C) 2009-2012 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.smtinterpol.interpolate;

import java.util.HashSet;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.FormulaUnLet;
import de.uni_freiburg.informatik.ultimate.logic.FormulaUnLet.UnletType;
import de.uni_freiburg.informatik.ultimate.logic.FunctionSymbol;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermTransformer;

public class SymbolCollector extends TermTransformer {

	private HashSet<FunctionSymbol> mSymbols = new HashSet<FunctionSymbol>();

	/**
	 * Collect all symbols occurring in a given formula.  Do not use the
	 * {@link TermTransformer#transform(Term)} method on this class. 
	 * @param input The given formula.
	 */
	public final void collect(Term input) {
		final FormulaUnLet unletter = new FormulaUnLet(UnletType.EXPAND_DEFINITIONS);
		final Term t = unletter.unlet(input);
		transform(t);
	}

	public Set<FunctionSymbol> getSymbols() {
		final Set<FunctionSymbol> result = mSymbols;
		mSymbols = new HashSet<>();
		return result;
	}

	@Override
	public void convertApplicationTerm(ApplicationTerm appTerm, Term[] newArgs) {
		final FunctionSymbol fs = appTerm.getFunction();
		if (!fs.isIntern()) {
			mSymbols.add(fs);
		}
		super.convertApplicationTerm(appTerm, newArgs);
	}
}
