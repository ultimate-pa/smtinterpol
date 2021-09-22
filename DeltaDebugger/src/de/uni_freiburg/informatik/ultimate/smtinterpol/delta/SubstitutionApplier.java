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
package de.uni_freiburg.informatik.ultimate.smtinterpol.delta;

import java.util.ArrayList;
import java.util.Iterator;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.logic.AnnotatedTerm;
import de.uni_freiburg.informatik.ultimate.logic.Annotation;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.CheckClosedTerm;
import de.uni_freiburg.informatik.ultimate.logic.LambdaTerm;
import de.uni_freiburg.informatik.ultimate.logic.LetTerm;
import de.uni_freiburg.informatik.ultimate.logic.MatchTerm;
import de.uni_freiburg.informatik.ultimate.logic.QuantifiedFormula;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermTransformer;

public class SubstitutionApplier extends TermTransformer {
	private int mDepth;
	private Iterator<Substitution> mIt;
	private Substitution mSubst;

	private List<Cmd> mAdds = new ArrayList<>();
	private int mTermDepth;

	void stepSubst() {
		while (mIt.hasNext()) {
			mSubst = mIt.next();
			if (!mSubst.isSuccess()) {
				return;
			}
		}
		mSubst = null;
	}

	public void init(final int depth, final List<Substitution> substs) {
		mDepth = depth;
		mIt = substs.iterator();
		stepSubst();
	}

	public Term apply(final Term term) {
		mTermDepth = 0;
		return transform(term);
	}

	public List<Cmd> getAdds() {
		final List<Cmd> res = mAdds;
		mAdds = new ArrayList<>();
		return res;
	}

	@Override
	protected void convert(final Term term) {
		if (mTermDepth == mDepth) {
			// Apply substitution
			final boolean expectedTrue = mIt.hasNext();
			assert expectedTrue;
			if (mSubst != null && mSubst.matches(term)) {
				if (mSubst.isActive()) {
					setResult(mSubst.apply(term));
					final Cmd add = mSubst.getAdditionalCmd(term);
					if (add != null) {
						mAdds.add(add);
					}
				} else {
					setResult(term);
				}
				// We can step here since we found a (possibly deactivated)
				// match. If the term does not match, we should not step!
				stepSubst();
			} else {
				// We don't need to descend since we will never change
				// anything at lower depths.
				setResult(term);
			}
		} else {
			if (term instanceof ApplicationTerm || term instanceof LetTerm || term instanceof LambdaTerm
					|| term instanceof QuantifiedFormula || term instanceof MatchTerm
					|| term instanceof AnnotatedTerm) {
				mTermDepth++;
			}
			super.convert(term);
		}
	}

	@Override
	public void convertApplicationTerm(final ApplicationTerm old, final Term[] newParams) {
		mTermDepth--;
		super.convertApplicationTerm(old, newParams);
	}

	@Override
	public void postConvertLet(final LetTerm oldLet, final Term[] newValues, final Term newBody) {
		mTermDepth--;
		if (new CheckClosedTerm().isClosed(newBody)) {
			setResult(newBody);
		} else {
			super.postConvertLet(oldLet, newValues, newBody);
		}
	}

	@Override
	public void postConvertLambda(final LambdaTerm old, final Term newBody) {
		mTermDepth--;
		super.postConvertLambda(old, newBody);
	}

	@Override
	public void postConvertQuantifier(final QuantifiedFormula old, final Term newBody) {
		mTermDepth--;
		if (new CheckClosedTerm().isClosed(newBody)) {
			setResult(newBody);
		} else {
			super.postConvertQuantifier(old, newBody);
		}
	}

	@Override
	public void postConvertMatch(final MatchTerm old, final Term newDataTerm, final Term[] newCases) {
		mTermDepth--;
		super.postConvertMatch(old, newDataTerm, newCases);
	}

	@Override
	public void postConvertAnnotation(final AnnotatedTerm old, final Annotation[] newAnnots, final Term newBody) {
		mTermDepth--;
		super.postConvertAnnotation(old, newAnnots, newBody);
	}
}
