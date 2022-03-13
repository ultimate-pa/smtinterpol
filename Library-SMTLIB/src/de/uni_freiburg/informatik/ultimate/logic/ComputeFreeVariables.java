/*
 * Copyright (C) 2009-2022 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.logic;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashSet;
import java.util.LinkedHashSet;
import java.util.List;

/**
 * Helper to compute the free variables contained in a term. This is a very
 * simple term transformer that returns the input term but computes the free
 * variables and sets the corresponding field.
 *
 * @author Jochen Hoenicke
 */
public class ComputeFreeVariables extends TermTransformer {
	static final TermVariable[] NOFREEVARS = new TermVariable[0];

	public ComputeFreeVariables() {
	}

	@Override
	public void convert(final Term term) {
		if (term.mFreeVars != null) {
			setResult(term);
			return;
		}
		if (term instanceof ConstantTerm) {
			term.mFreeVars = NOFREEVARS;
		} else if (term instanceof TermVariable) {
			term.mFreeVars = new TermVariable[] { (TermVariable) term };
		}
		super.convert(term);
	}

	@Override
	public void convertApplicationTerm(final ApplicationTerm oldApp, final Term[] params) {
		if (params.length <= 1) {
			if (params.length == 1) {
				oldApp.mFreeVars = params[0].mFreeVars;
			} else {
				oldApp.mFreeVars = ComputeFreeVariables.NOFREEVARS;
			}
		} else {
			int biggestlen = 0;
			int biggestidx = -1;
			for (int i = 0; i < params.length; i++) {
				final TermVariable[] free = params[i].mFreeVars;
				if (free.length > biggestlen) {
					biggestlen = free.length;
					biggestidx = i;
				}
			}
			/* return if term is closed */
			if (biggestidx < 0) {
				oldApp.mFreeVars = ComputeFreeVariables.NOFREEVARS;
			} else {
				List<TermVariable> result = null;
				final List<TermVariable> biggestAsList = Arrays.asList(params[biggestidx].mFreeVars);
				for (int i = 0; i < params.length; i++) {
					if (i == biggestidx) {
						continue;
					}
					final TermVariable[] free = params[i].getFreeVars();
					for (final TermVariable tv : free) {
						if (!biggestAsList.contains(tv)) {
							if (result == null) {
								result = new ArrayList<>();
								result.addAll(biggestAsList);
							}
							if (!result.contains(tv)) {
								result.add(tv);
							}
						}
					}
				}
				if (result == null) {
					oldApp.mFreeVars = params[biggestidx].mFreeVars;
				} else {
					oldApp.mFreeVars = result.toArray(new TermVariable[result.size()]);
				}
			}
		}
		setResult(oldApp);
	}

	@Override
	public void postConvertLet(final LetTerm letTerm, final Term[] vals, final Term newBody) {
		final TermVariable[] vars = letTerm.getVariables();
		final HashSet<TermVariable> free = new LinkedHashSet<>();
		free.addAll(Arrays.asList(newBody.mFreeVars));
		free.removeAll(Arrays.asList(vars));
		for (final Term v : vals) {
			free.addAll(Arrays.asList(v.mFreeVars));
		}
		if (free.isEmpty()) {
			letTerm.mFreeVars = NOFREEVARS;
		} else {
			letTerm.mFreeVars = free.toArray(new TermVariable[free.size()]);
		}
		setResult(letTerm);
	}

	@Override
	public void postConvertLambda(final LambdaTerm lambda, final Term newBody) {
		final HashSet<TermVariable> free = new LinkedHashSet<>();
		free.addAll(Arrays.asList(newBody.mFreeVars));
		free.removeAll(Arrays.asList(lambda.getVariables()));
		if (free.isEmpty()) {
			lambda.mFreeVars = NOFREEVARS;
		} else {
			lambda.mFreeVars = free.toArray(new TermVariable[free.size()]);
		}
		setResult(lambda);
	}

	@Override
	public void postConvertQuantifier(final QuantifiedFormula quant, final Term newBody) {
		final HashSet<TermVariable> free = new LinkedHashSet<>();
		free.addAll(Arrays.asList(newBody.mFreeVars));
		free.removeAll(Arrays.asList(quant.getVariables()));
		if (free.isEmpty()) {
			quant.mFreeVars = NOFREEVARS;
		} else {
			quant.mFreeVars = free.toArray(new TermVariable[free.size()]);
		}
		setResult(quant);
	}

	@Override
	public void postConvertAnnotation(final AnnotatedTerm annotTerm, final Annotation[] newAnnots, final Term newBody) {
		final HashSet<TermVariable> free = new LinkedHashSet<>();
		free.addAll(Arrays.asList(newBody.mFreeVars));
		final ArrayDeque<Object> todo = new ArrayDeque<>();
		for (final Annotation annot : newAnnots) {
			if (annot.getValue() != null) {
				todo.add(annot.getValue());
			}
		}
		while (!todo.isEmpty()) {
			final Object value = todo.removeLast();
			if (value instanceof Term) {
				free.addAll(Arrays.asList(((Term) value).mFreeVars));
			} else if (value instanceof Object[]) {
				for (final Object elem : (Object[]) value) {
					todo.add(elem);
				}
			}
		}
		if (free.isEmpty()) {
			annotTerm.mFreeVars = NOFREEVARS;
		} else if (free.size() == newBody.mFreeVars.length) {
			annotTerm.mFreeVars = newBody.mFreeVars;
		} else {
			annotTerm.mFreeVars = free.toArray(new TermVariable[free.size()]);
		}
		setResult(annotTerm);
	}

	@Override
	public void postConvertMatch(final MatchTerm match, final Term newDataTerm, final Term[] newCases) {
		final HashSet<TermVariable> free = new LinkedHashSet<>();
		for (int i = 0; i < newCases.length; i++) {
			final HashSet<TermVariable> freeCase = new LinkedHashSet<>();
			freeCase.addAll(Arrays.asList(newCases[i].mFreeVars));
			freeCase.removeAll(Arrays.asList(match.getVariables()[i]));
			free.addAll(freeCase);
		}
		free.addAll(Arrays.asList(newDataTerm.mFreeVars));
		if (free.isEmpty()) {
			match.mFreeVars = NOFREEVARS;
		} else if (free.size() == newDataTerm.mFreeVars.length) {
			match.mFreeVars = newDataTerm.mFreeVars;
		} else {
			match.mFreeVars = free.toArray(new TermVariable[free.size()]);
		}
		setResult(match);
	}
}
