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

import java.util.ArrayList;
import java.util.List;
import java.util.function.BiFunction;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.Literal;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.EprTheory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.atoms.EprGroundPredicateAtom;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.dawgs.DawgFactory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.dawgs.dawgstates.DawgState;

/**
 * Represents an entry in the epr decide stack which marks the setting of a literal through the dpll engine
 * at that point.
 *
 * @author Alexander Nutz
 */
public class DecideStackSetLiteralMarker extends DecideStackEntry {

	private final Literal mLiteral;

	public DecideStackSetLiteralMarker(final Literal l, final int index) {
		super(index);
		mLiteral = l;
	}

	@Override
	public String toString() {
		return "(literalMarker: " + mLiteral + " " + nr + ")";
	}

	private boolean isEffective;
	@Override
	public void push() {
		if (mLiteral.getAtom() instanceof EprGroundPredicateAtom) {
			final EprGroundPredicateAtom eprAtom = (EprGroundPredicateAtom) mLiteral.getAtom();
			final DawgState<ApplicationTerm, EprTheory.TriBool> dawg = eprAtom.mEprPredicate.getDawg();
			final List<ApplicationTerm> word = new ArrayList<>();
			for (final Term param : eprAtom.getArguments()) {
				word.add((ApplicationTerm) param);
			}
			if (dawg.getValue(word) == EprTheory.TriBool.UNKNOWN) {
				final BiFunction<EprTheory.TriBool, Boolean, EprTheory.TriBool> combinator = (old, setLit) -> {
					assert !setLit || old == EprTheory.TriBool.UNKNOWN;
					return (setLit ? (mLiteral == eprAtom ? EprTheory.TriBool.TRUE : EprTheory.TriBool.FALSE) : old);
				};
				isEffective = true;
				final DawgFactory<ApplicationTerm, TermVariable> factory =
						eprAtom.mEprPredicate.getEprTheory().getDawgFactory();
				eprAtom.mEprPredicate.setDawg(factory.createProduct(dawg,
						factory.createSingletonSet(eprAtom.mEprPredicate.getSignature(), word), combinator));
			}
		}
	}

	@Override
	public void pop() {
		if (isEffective) {
			final EprGroundPredicateAtom eprAtom = (EprGroundPredicateAtom) mLiteral.getAtom();
			final DawgState<ApplicationTerm, EprTheory.TriBool> dawg = eprAtom.mEprPredicate.getDawg();
			final List<ApplicationTerm> word = new ArrayList<>();
			for (final Term param : eprAtom.getArguments()) {
				word.add((ApplicationTerm) param);
			}
			final BiFunction<EprTheory.TriBool, Boolean, EprTheory.TriBool> combinator = (old, setLit) -> {
				return (setLit ? EprTheory.TriBool.UNKNOWN : old);
			};
			isEffective = false;
			final DawgFactory<ApplicationTerm, TermVariable> factory =
					eprAtom.mEprPredicate.getEprTheory().getDawgFactory();
			eprAtom.mEprPredicate.setDawg(factory.createProduct(dawg,
					factory.createSingletonSet(eprAtom.mEprPredicate.getSignature(), word), combinator));
		}
	}
}
