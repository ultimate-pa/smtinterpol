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
package de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.partialmodel;

import java.util.HashSet;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.Literal;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.EprHelpers;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.EprPredicate;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.atoms.EprGroundPredicateAtom;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.clauses.ClauseEprLiteral;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.dawgs.DawgFactory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.dawgs.dawgstates.DawgState;

/**
 * An EprGroundPredicateLiteral is a representation of a literal that is set by the DPLLEngine which uses an
 * epr predicate, and thus has special relevance to the epr theory, compared to other Literals
 *
 * Properties:
 *  - is known to the DPLLEngine (in the form of a "Literal" object)
 *  - is similar to a decide stack literal insofar it contributes to the union dawg of an epr predicate
 *    (which describes the current partial model for that predicate)
 *    --> this property is described by the interface IEprLiteral
 *
 * @author Alexander Nutz
 */
public class EprGroundPredicateLiteral implements IEprLiteral {

	private final EprGroundPredicateAtom mAtom;
	private final EprPredicate mEprPredicate;
	private final boolean mPolarity;
	private final DawgState<ApplicationTerm, Boolean> mDawg;

	Set<ClauseEprLiteral> mConcernedClauseLiterals = new HashSet<ClauseEprLiteral>();

	public EprGroundPredicateLiteral(final Literal l, final DawgFactory<ApplicationTerm, TermVariable> dawgFactory,
			final EprStateManager stateManager) {
		mAtom = (EprGroundPredicateAtom) l.getAtom();
		mEprPredicate = mAtom.mEprPredicate;
		mPolarity = l.getSign() == 1;
		mDawg = dawgFactory.createSingletonSet(
						mEprPredicate.getTermVariablesForArguments(),
						EprHelpers.convertTermArrayToConstantList(mAtom.getArguments()));
		mEprPredicate.registerEprLiteral(this);
		stateManager.registerEprGroundPredicateLiteral(this, l);
	}

	@Override
	public EprPredicate getEprPredicate() {
		return mEprPredicate;
	}

	@Override
	public boolean getPolarity() {
		return mPolarity;
	}

	@Override
	public DawgState<ApplicationTerm, Boolean> getDawg() {
		return mDawg;
	}

	@Override
	public String toString() {
		return "(EGPL: " + (mPolarity ? mAtom : mAtom.negate()).toString() + ")";
	}

	@Override
	public void unregister() {
		mEprPredicate.unregisterEprLiteral(this);
		for (final ClauseEprLiteral cel : mConcernedClauseLiterals) {
			cel.unregisterIEprLiteral(this);
		}
	}

	@Override
	public void registerConcernedClauseLiteral(final ClauseEprLiteral cel) {
		mConcernedClauseLiterals.add(cel);
	}
}
