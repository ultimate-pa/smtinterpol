/*
 * Copyright (C) 2016-2017 Alexander Nutz (nutz@informatik.uni-freiburg.de)
 * Copyright (C) 2016-2017 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.atoms;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.Theory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.EprEqualityPredicate;

/**
 * Atom representing a ground equality.
 * Maybe this is just a dummy until it gets replaced by CCEquality in all places,
 * maybe we want not-shared ground equalities in the Epr theory --> not sure yet..
 * 
 * Note that this does not extend EprEqualityAtom because that is assumed to represent
 * a quantified equality.
 * 
 * @author Alexander Nutz
 *
 */
public class EprGroundEqualityAtom extends EprGroundPredicateAtom {

	public EprGroundEqualityAtom(ApplicationTerm term, int hash, int assertionstacklevel, EprEqualityPredicate eqPred) {
		super(term, hash, assertionstacklevel, eqPred);
	}

	@Override
	public Term getSMTFormula(Theory smtTheory, boolean quoted) {
		return mTerm;
	}
}
