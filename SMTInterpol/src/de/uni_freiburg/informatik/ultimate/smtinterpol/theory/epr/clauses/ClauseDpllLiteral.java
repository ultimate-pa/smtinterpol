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
package de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.clauses;

import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.DPLLAtom;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.EprTheory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.atoms.EprPredicateAtom;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.atoms.EprQuantifiedEqualityAtom;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.partialmodel.DecideStackLiteral;

public class ClauseDpllLiteral extends ClauseLiteral {

	public ClauseDpllLiteral(boolean polarity, DPLLAtom atom, EprClause clause, EprTheory eprTheory) {
		super(polarity, atom, clause, eprTheory);
		assert !(atom instanceof EprPredicateAtom) : "use different ClauseLiteral";
		assert !(atom instanceof EprQuantifiedEqualityAtom) : "use different ClauseLiteral";
	}

	/**
	 * 
	 * @param decideStackBorder this parameter is irrelevant for dpll literals because they lie
	 *   "below" the epr decide stack anyway.
	 */
	@Override
	protected ClauseLiteralState determineState(DecideStackLiteral decideStackBorder) {
		if (mAtom.getDecideStatus() == null) {
			// undecided 
			return ClauseLiteralState.Fulfillable;
		} else if ((mAtom.getDecideStatus() == mAtom) == mPolarity){
			// decided with same polarity
			return ClauseLiteralState.Fulfilled;
		} else {
			// decided with different polarity
			return ClauseLiteralState.Refuted;
		}
	}

}
