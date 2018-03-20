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

import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.smtinterpol.convert.Clausifier;
import de.uni_freiburg.informatik.ultimate.smtinterpol.convert.SharedTerm;

/**
 * Represents a ground term. It is basically a SharedTerm.
 * 
 * @author Tanja Schindler
 *
 */
public class GroundTerm extends EUTerm {

	private final SharedTerm mSharedTerm;

	/**
	 * Create a new GroundTerm. This must only be called after checking that the term is ground.
	 * 
	 * @param clausifier
	 *            the clausifier.
	 * @param term
	 *            the underlying ground term.
	 * @param shared
	 *            the SharedTerm corresponding to the given ground term.
	 */
	GroundTerm(final Clausifier clausifier, final Term term, final SharedTerm shared) {
		super(clausifier, term);
		assert term.getFreeVars().length == 0;
		mSharedTerm = shared;
	}

	public SharedTerm getSharedTerm() {
		return mSharedTerm;
	}
}
