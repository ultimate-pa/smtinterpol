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
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.logic.AnnotatedTerm;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.FunctionSymbol;
import de.uni_freiburg.informatik.ultimate.logic.SMTLIBException;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermTransformer;

public class SymbolChecker extends TermTransformer {

	private Map<FunctionSymbol, Integer> mSubtreeOccurrences;
	private Map<FunctionSymbol, Integer> mAllOccurences;
	private HashSet<FunctionSymbol> mALocal;
	private HashSet<FunctionSymbol> mBLocal;
	private final Set<FunctionSymbol> mGlobals;

	/**
	 * Create a new checker for symbol occurrences in interpolants.
	 *
	 * @param globals
	 *            The symbols that occur in the background theory.
	 * @param occurrences
	 *            A map from each symbol to the number of partitions where the symbol occurs.
	 */
	public SymbolChecker(Set<FunctionSymbol> globals, Map<FunctionSymbol, Integer> allOccurrences) {
		mGlobals = globals;
		mAllOccurences = allOccurrences;
	}

	/**
	 * Check whether an interpolant contains only allowed symbols.
	 *
	 * @param interpolant
	 *            The interpolant.
	 * @param subtreeOccurrences
	 *            The number of partitions in the subtree (A part) where the symbol occurs.
	 * @return {@code true} if an A local or B local symbol was found in the interpolant.
	 */
	public final boolean check(Term interpolant, Map<FunctionSymbol, Integer> subtreeOccurrences) {
		mSubtreeOccurrences = subtreeOccurrences;
		mALocal = new HashSet<FunctionSymbol>();
		mBLocal = new HashSet<FunctionSymbol>();
		transform(interpolant);
		mSubtreeOccurrences = null;
		return !(mALocal.isEmpty() && mBLocal.isEmpty());
	}

	@Override
	public void convert(Term term) {
		if (term instanceof AnnotatedTerm) {
			throw new SMTLIBException("Interpolant contains annotated term: " + term);
		}
		super.convert(term);
	}

	@Override
	public void convertApplicationTerm(ApplicationTerm appTerm, Term[] newArgs) {
		final FunctionSymbol fs = appTerm.getFunction();
		if (!fs.isIntern() && !mGlobals.contains(fs)) {
			final Integer inA = mSubtreeOccurrences.get(fs);
			final Integer inAll = mAllOccurences.get(fs);
			if (inAll == null) {
				throw new InternalError("Detected new symbol in interpolant: " + fs);
			} else if (inA == null) {
				// symbol doesn't occur in the A part
				mBLocal.add(fs);
			} else if (inAll - inA <= 0) {
				// symbol doesn't occur in the B part
				mALocal.add(fs);
			}
		}
		super.convertApplicationTerm(appTerm, newArgs);
	}

	public Set<FunctionSymbol> getALocals() {
		return mALocal;
	}

	public Set<FunctionSymbol> getBLocals() {
		return mBLocal;
	}
}
