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

import de.uni_freiburg.informatik.ultimate.logic.TermVariable;

/**
 * Represents a possibly quantified term that is allowed as argument of a QuantAppTerm. This can be a TermVariable, or a
 * ground or quantified EUTerm.
 * 
 * @author Tanja Schindler
 *
 */
public class QuantAppArg {

	final EUTerm mEUTerm;
	final TermVariable mVarTerm;

	/**
	 * Transform an EUTerm into an QuantAppArg.
	 * 
	 * @param eUTerm
	 *            the underlying EUTerm.
	 */
	public QuantAppArg(final EUTerm eUTerm) {
		mEUTerm = eUTerm;
		mVarTerm = null;
	}

	/**
	 * Transform a TermVariable into an QuantAppArg.
	 * 
	 * @param varTerm
	 *            the underlying TermVariable.
	 */
	QuantAppArg(final TermVariable varTerm) {
		mEUTerm = null;
		mVarTerm = varTerm;
	}

	public boolean isVar() {
		return mVarTerm != null;
	}

	public EUTerm getEUTerm() {
		return mEUTerm;
	}

	public TermVariable getVar() {
		return mVarTerm;
	}
}
