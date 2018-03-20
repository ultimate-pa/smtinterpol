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

import java.util.Set;

import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.smtinterpol.convert.Clausifier;

/**
 * Represents an essentially uninterpreted term. Quantified variables are allowed, but only as arguments of
 * uninterpreted predicate and function symbols.
 * 
 * @author Tanja Schindler
 *
 */
public abstract class EUTerm {

	private final Term mTerm;
	private final Clausifier mClausifier;

	protected Set<TermVariable> mFreeVars; // TODO Should a EUTerm store the variables, and how?

	/**
	 * Create a new EUTerm. This must only be called after checking that the term is essentially uninterpreted. We have
	 * three types of EUTerm: GroundTerm, QuantAffineTerm, QuantAppTerm.
	 * 
	 * @param clausifier
	 *            the clausifier.
	 * @param term
	 *            the underlying term.
	 */
	EUTerm(final Clausifier clausifier, final Term term) {
		mTerm = term;
		mClausifier = clausifier;
		mFreeVars = null;
	}

	public Sort getSort() {
		return mTerm.getSort();
	}

	public Term getTerm() {
		return mTerm;
	}

	public Clausifier getClausifier() {
		return mClausifier;
	}

	public Set<TermVariable> getFreeVars() {
		return mFreeVars;
	}
}
