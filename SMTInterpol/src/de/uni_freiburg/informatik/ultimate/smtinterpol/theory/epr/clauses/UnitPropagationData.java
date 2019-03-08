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

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.dawgs.DawgFactory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.dawgs.dawgstates.DawgState;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.partialmodel.DecideStackEntry;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.partialmodel.DecideStackPropagatedLiteral;

/**
 *
 * @author Alexander Nutz (nutz@informatik.uni-freiburg.de)
 *
 */
public class UnitPropagationData {

	private final List<DecideStackEntry> mQuantifiedPropagations;

	public UnitPropagationData(
			final EprClause clause, final DawgState<ApplicationTerm, Integer> clauseDawg,
			final DawgFactory<ApplicationTerm, TermVariable> dawgFactory) {

		final List<DecideStackEntry> quantifiedPropagations = new ArrayList<>();

		for (int i = 0; i < clause.getLiterals().size(); i++) {
			final ClauseLiteral cl = clause.getLiterals().get(i);
			final int litNr = i;
			final DawgState<ApplicationTerm, Boolean> unitPoints =
					dawgFactory.createMapped(clauseDawg, status -> status == litNr);
			if (DawgFactory.isEmpty(unitPoints)) {
				continue;
			}
			final ClauseEprLiteral cel = (ClauseEprLiteral) cl;
			final DecideStackPropagatedLiteral dspl = new DecideStackPropagatedLiteral(cel, unitPoints);
			quantifiedPropagations.add(dspl);
		}

		mQuantifiedPropagations = Collections.unmodifiableList(quantifiedPropagations);
	}

	public List<DecideStackEntry> getQuantifiedPropagations() {
		return mQuantifiedPropagations;
	}
}
