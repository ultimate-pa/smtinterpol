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

import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.smtinterpol.convert.Clausifier;

/**
 * Represents a quantified affine term, i.e. all summands (except for the constant) are EUTerms and at least one is a
 * quantified EUTerm.
 * 
 * @author Tanja Schindler
 *
 */
public class QuantAffineTerm extends EUTerm {

	private final Map<EUTerm, Rational> mSummands;
	private final Rational mConstant;

	/**
	 * Create a new QuantAffineTerm for a given term of the form "sum of coeff*EUTerms + const". This must only be
	 * called if at least one of the EUTerms is not ground.
	 * 
	 * @param clausifier
	 *            the Clausifier.
	 * @param term
	 *            the underlying term.
	 * @param summands
	 *            the non-constant summands of form "coeff*EUTerm". At least one must not be ground.
	 * @param constant
	 *            the constant.
	 */
	QuantAffineTerm(final Clausifier clausifier, final Term term, final Map<EUTerm, Rational> summands,
			final Rational constant) {
		super(clausifier, term);
		mSummands = summands;
		mConstant = constant;
		mFreeVars = new HashSet<TermVariable>();
		for (EUTerm summand : summands.keySet()) {
			if (summand.getFreeVars() != null) {
				mFreeVars.addAll(summand.getFreeVars());
			}
		}
		assert !mFreeVars.isEmpty();
	}

	/**
	 * Build a new QuantAffineTerm for a given EUTerm. This must only be called if the EUTerm is not ground.
	 * 
	 * @param euTerm
	 *            the non-ground EUTerm that is transformed into a QuantAffineTerm.
	 */
	QuantAffineTerm(final EUTerm euTerm) {
		super(euTerm.getClausifier(), euTerm.getTerm());
		assert !(euTerm instanceof GroundTerm);
		if (euTerm instanceof QuantAppTerm) {
			mSummands = Collections.singletonMap(euTerm, Rational.ONE);
			mConstant = Rational.ZERO;
		} else if (euTerm instanceof QuantAffineTerm) {
			mSummands = ((QuantAffineTerm) euTerm).getSummands();
			mConstant = ((QuantAffineTerm) euTerm).getConstant();
		} else {
			throw new InternalError("Unknown EUTerm: " + euTerm);
		}
		mFreeVars = euTerm.getFreeVars();
	}

	public Map<EUTerm, Rational> getSummands() {
		return mSummands;
	}

	public Rational getConstant() {
		return mConstant;
	}

	/**
	 * Return a new QuantAffineTerm for the result of adding to this QuantAffineTerm another EUTerm multiplied by some
	 * factor.
	 */
	protected QuantAffineTerm add(final Rational factor, final EUTerm other) {
		final QuantAffineTerm otherAffine = new QuantAffineTerm(other);
		final Term newTerm = null; // TODO
		final Map<EUTerm, Rational> newSummands = new HashMap<EUTerm, Rational>(mSummands);
		for (final Map.Entry<EUTerm, Rational> entry : otherAffine.getSummands().entrySet()) {
			final EUTerm var = entry.getKey();
			if (newSummands.containsKey(var)) {
				final Rational newFactor = newSummands.get(var).add(entry.getValue());
				if (newFactor.equals(Rational.ZERO)) {
					newSummands.remove(var);
				} else {
					newSummands.put(var, newFactor);
				}
			} else {
				newSummands.put(var, entry.getValue());
			}
		}
		final Rational newConstant = mConstant.add(otherAffine.getConstant());
		return new QuantAffineTerm(getClausifier(), newTerm, newSummands, newConstant);
	}
}
