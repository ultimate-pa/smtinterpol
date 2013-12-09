/*
 * Copyright (C) 2012-2013 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.smtinterpol.proofcheck;

import de.uni_freiburg.informatik.ultimate.logic.*;

/**
 * This class is used to convert a trichotomy lemma.
 * That is, a number 'x' must be one of the following:
 * '(= x 0), (< x 0), or (> x 0)'
 * 
 * @author Christian Schilling
 */
public class LemmaTrichotomyConverter extends AConverter {
	/**
	 * @param appendable appendable to write the proof to
	 * @param theory the theory
	 * @param converter term converter
	 * @param simplifier computation simplifier
	 */
	public LemmaTrichotomyConverter(final Appendable appendable,
			final Theory theory, final TermConverter converter,
			final ComputationSimplifier simplifier) {
		super(appendable, theory, converter, simplifier);
	}
	
	/**
	 * This method converts a trichotomy lemma.
	 * The lemma is always a ternary disjunction, where one disjunct has the
	 * form '(= x 0)' (equality, 'e'), one disjunct has the form
	 * '(not (<= x 0))' (greater, 'g'), and one disjunct is the less ('l')
	 * disjunct. The order can vary.
	 * 
	 * The 'l' disjunct depends on the sort of 'x'. For integer 'x', the form
	 * is '(<= y 0)', where 'y' is equivalent to 'x + 1'. For real 'x' the form
	 * is '(< x 0)'.
	 * 
	 * The conversion first brings the disjunction to the normal form
	 * '(e | l | g)' (only internally). Since afterwards there can only occur
	 * resolution nodes, we can set our own order here.
	 * For real 'x' the lemma is then proven with a single rule.
	 * For integer 'x' the rule has an open obligation 'y = x + 1', which is
	 * finally proven by the simplifier.
	 * 
	 * @param lemma the ternary disjunction
	 * @return the disjunction (possibly reordered)
	 */
	public ApplicationTerm convert(ApplicationTerm lemma) {
		assert (lemma.getFunction() == mTheory.mOr);
		final Term[] oldDisjunction = lemma.getParameters();
		assert ((oldDisjunction.length == 3)
				&& (unquote(oldDisjunction[0]) != null)
				&& (unquote(oldDisjunction[1]) != null)
				&& (unquote(oldDisjunction[2]) != null));
		final FunctionSymbol first = unquote(oldDisjunction[0]).getFunction();
		final FunctionSymbol second = unquote(oldDisjunction[1]).getFunction();
		final Sort sort;
		
		/* bring the disjuncts to the order 'e | l | g' */
		
		if (first == mTheory.mNot) {
			assert (second.getParameterSorts().length == 2);
			sort = second.getParameterSorts()[0];
			final Term[] newDisjunction = new Term[3];
			newDisjunction[2] = oldDisjunction[0];
			
			// 'gel'
			if (second.getName() == "=") {
				assert ((unquote(oldDisjunction[2]).getFunction().getName()
								== "<=")
						|| (unquote(oldDisjunction[2]).getFunction().getName()
								== "<"));
				newDisjunction[0] = oldDisjunction[1];
				newDisjunction[1] = oldDisjunction[2];
			} else {
				// 'gle'
				assert (((second.getName() == "<=")
						|| (second.getName() == "<"))
						&& (unquote(oldDisjunction[2]).getFunction().getName()
								== "="));
				newDisjunction[0] = oldDisjunction[2];
				newDisjunction[1] = oldDisjunction[1];
			}
			
			lemma = mTheory.term(mTheory.mOr, newDisjunction);
		} else {
			assert (first.getParameterSorts().length == 2);
			sort = first.getParameterSorts()[0];
			
			if (first.getName() == "=") {
				// 'egl'
				if (second == mTheory.mNot) {
					assert ((unquote(oldDisjunction[2]).getFunction().
									getName() == "<=")
							|| (unquote(oldDisjunction[2]).getFunction().
									getName() == "<"));
					final Term[] newDisjunction = new Term[3];
					newDisjunction[0] = oldDisjunction[0];
					newDisjunction[1] = oldDisjunction[2];
					newDisjunction[2] = oldDisjunction[1];
					lemma = mTheory.term(mTheory.mOr, newDisjunction);
				} else {
					// 'elg'
					assert (((second.getName() == "<=")
							|| (second.getName() == "<"))
							&& (unquote(oldDisjunction[2]).getFunction()
									== mTheory.mNot));
					// nothing to do here
				}
			} else {
				assert ((first.getName() == "<=")
						|| (first.getName() == "<"));
				final Term[] newDisjunction = new Term[3];
				newDisjunction[1] = oldDisjunction[0];
				
				// 'lge'
				if (second == mTheory.mNot) {
					assert (unquote(oldDisjunction[2]).getFunction().
									getName() == "=");
					newDisjunction[0] = oldDisjunction[2];
					newDisjunction[2] = oldDisjunction[1];
				} else {
					// 'leg'
					assert ((second.getName() == "=")
							&& (unquote(oldDisjunction[2]).getFunction()
									== mTheory.mNot));
					newDisjunction[0] = oldDisjunction[1];
					newDisjunction[2] = oldDisjunction[2];
				}
				
				lemma = mTheory.term(mTheory.mOr, newDisjunction);
			}
		}
		
		// write rule
		mConverter.convert(lemma);
		
		// integer case
		if (sort == mTheory.getNumericSort()) {
			writeString("\" by (rule trichotomy_int, ");
			writeString(mSimplifier.getRule());
			writeString(")\n");
		} else {
			// real case
			assert (sort == mTheory.getRealSort());
			writeString("\" by (rule trichotomy_real)\n");
		}

		// result may have been modified, so return it
		return lemma;
	}
	
	/**
	 * This method returns the ApplicationTerm from a disjunct.
	 * If the disjunct is negated, it will be returned unchanged and
	 * is unpacked from the :quoted literals otherwise.
	 * 
	 * @param term the quoted term (must be an AnnotatedTerm)
	 * @return the inner term
	 */
	private ApplicationTerm unquote(Term term) {
		if (term instanceof ApplicationTerm) {
			assert (((ApplicationTerm)term).getFunction() == mTheory.mNot);
			return (ApplicationTerm)term;
		}
		assert ((term instanceof AnnotatedTerm)
				&& (((AnnotatedTerm)term).getAnnotations().length == 1)
				&& (((AnnotatedTerm)term).getAnnotations()[0].getKey()
						== ":quoted")
				&& (((AnnotatedTerm)term).getSubterm() instanceof ApplicationTerm));
		return (ApplicationTerm)((AnnotatedTerm)term).getSubterm();
	}
}
