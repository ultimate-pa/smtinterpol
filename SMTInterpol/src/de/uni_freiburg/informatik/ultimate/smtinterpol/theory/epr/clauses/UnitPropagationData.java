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
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.Clause;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.Literal;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.atoms.EprGroundEqualityAtom;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.dawgs.DawgFactory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.dawgs.dawgstates.DawgState;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.partialmodel.DslBuilder;

/**
 *
 * @author Alexander Nutz (nutz@informatik.uni-freiburg.de)
 *
 */
public class UnitPropagationData {

	private final List<DslBuilder> mQuantifiedPropagations;
	// public final List<Pair<Literal, Clause>> mGroundPropagations;
	private final Map<Literal, Clause> mGroundPropagations;

	public UnitPropagationData(
			final Map<ClauseLiteral, DawgState<ApplicationTerm, Boolean>> finalClauseLitToUnitPoints,
			final DawgFactory<ApplicationTerm, TermVariable> dawgFactory) {

		final List<DslBuilder> quantifiedPropagations = new ArrayList<DslBuilder>();
		final Map<Literal, Clause> groundPropagations = new HashMap<Literal, Clause>();

		for (final Entry<ClauseLiteral, DawgState<ApplicationTerm, Boolean>> en : finalClauseLitToUnitPoints
				.entrySet()) {
			final ClauseLiteral cl = en.getKey();
			if (cl instanceof ClauseEprQuantifiedLiteral) {
				final ClauseEprQuantifiedLiteral ceql = (ClauseEprQuantifiedLiteral) cl;
				final DslBuilder propB = new DslBuilder(ceql.getPolarity(), ceql.getEprPredicate(),
						dawgFactory.translateClauseSigToPredSig(en.getValue(),
								ceql.mEprClause.getVariables(),
								ceql.getTranslationFromClauseToEprPredicate(), ceql.getArgumentsAsAppTerm(),
								ceql.getEprPredicate().getTermVariablesForArguments()),
						ceql, en.getValue(), false);
				quantifiedPropagations.add(propB);
			} else {
				if (cl.getLiteral().getAtom() instanceof EprGroundEqualityAtom) {
					/*
					 * EprGroundEqualityAtoms are not passed to the DPLLEngine --> treat them like a quantified
					 * propagations
					 */
					final EprGroundEqualityAtom egea = (EprGroundEqualityAtom) cl.getLiteral().getAtom();

					final DawgState<ApplicationTerm, Boolean> onePointDawg = dawgFactory
							.createSingletonSet(egea.getEprPredicate().getTermVariablesForArguments(), egea.getPoint());

					// we don't need a signature translation here, because equality is symmetric anyway, right?..
					// TODO: perhaps reorder it manually..
					final DawgState<ApplicationTerm, Boolean> onePointDawgInClauseSig =
							dawgFactory.createSingletonSet(cl.getClause().getVariables(), egea.getPoint());

					final DslBuilder propB = new DslBuilder(cl.getPolarity(), egea.getEprPredicate(), onePointDawg,
							(ClauseEprLiteral) cl, onePointDawgInClauseSig,
							false);
					quantifiedPropagations.add(propB);
				} else {

					final DawgState<ApplicationTerm, Boolean> groundingDawg = finalClauseLitToUnitPoints.get(cl);
					final Set<Clause> groundings = cl.getClause().getGroundings(groundingDawg);
					final Clause unitGrounding = groundings.iterator().next();
					// note that the following assert would be wrong (rightfully), because some atoms of the given
					// clause
					// may not be known to the DPLLEngine yet
					// assert EprHelpers.verifyUnitClause(unitGrounding, cl.getLiteral(), dawgFactory.getLogger());
					groundPropagations.put(cl.getLiteral(), unitGrounding);
				}
			}
		}

		mQuantifiedPropagations = Collections.unmodifiableList(quantifiedPropagations);
		mGroundPropagations = Collections.unmodifiableMap(groundPropagations);
	}
	public List<DslBuilder> getQuantifiedPropagations() {
		return mQuantifiedPropagations;
	}


	/**
	 *
	 * @return a mapping from a ground unit literal to its propagation reason (which is a ground clause)
	 */
	public Map<Literal, Clause> getGroundPropagations() {
		return mGroundPropagations;
	}
}
