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

import java.math.BigDecimal;
import java.math.BigInteger;
import java.util.ArrayList;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.logic.AnnotatedTerm;
import de.uni_freiburg.informatik.ultimate.logic.Annotation;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.Theory;

public class SubstitutionManager {
	
	private int mDepth = -1;
	private List<Substitution> mSubsts;
	
	private final AbstractOneTermCmd mCmd;
	private final boolean mUnletRelet;

	public SubstitutionManager(AbstractOneTermCmd cmd, boolean unletRelet) {
		mCmd = cmd;
		mUnletRelet = unletRelet;
	}
	
	public boolean deepen() {
		++mDepth;
		return computeSubsts();
	}
	
	/**
	 * Notification of a test failure.  Steps all substitutions one step further
	 * and, hence, misses some of the potentially exponentially many
	 * substitutions.
	 * @return Does this depth still has some substitutions?
	 */
	public boolean failed() {
		stepSubsts();
		return !mSubsts.isEmpty();
	}
	
	private Substitution getSubstition(Term t) {
		if (t instanceof AnnotatedTerm) {
			AnnotatedTerm at = (AnnotatedTerm) t;
			for (Annotation a : at.getAnnotations())
				if (a.getKey().equals(":named"))
					// Cannot substitute at this level
					return null;
			// No names => Ignore annotations
			return new ReplaceByTerm(t, at.getSubterm(), true);
		} else if (t.getSort() == t.getTheory().getBooleanSort()) {
			// Try to replace by true
			return new ReplaceByTerm(t, t.getTheory().mTrue, true);
		} else if (t.getSort().isNumericSort()) {
			return new ReplaceByTerm(t, t.getSort().getName().equals("Int")
					? t.getTheory().numeral(BigInteger.ZERO)
						: t.getTheory().decimal(BigDecimal.ZERO), true);
		} else if (t instanceof ApplicationTerm) {
			// I guess this is always the case...
			ApplicationTerm at = (ApplicationTerm) t;
			if (at.getParameters().length > 0) {
				if (at.getFunction().getName().equals("store"))
					return new ReplaceByTerm(t, at.getParameters()[0], true);
				return ReplaceByFreshTerm.isFreshTerm(at)
						? null : new ReplaceByFreshTerm(t);
			}
		}
		// Cannot replace TermVariables or ConstantTerms
		return null;
	}
	
	private Substitution getNextSubstitution(Substitution subst) {
		Term t = subst.getMatch();
		if (subst instanceof ReplaceByFreshTerm) {
			ApplicationTerm at = (ApplicationTerm) t;
			if (at.getFunction().getName().equals("ite"))
				return new ReplaceByTerm(t, at.getParameters()[1], true, false);
			return null;
		}
		ReplaceByTerm r = (ReplaceByTerm) subst;
		if (t instanceof AnnotatedTerm) {
			assert r.getReplacement() == ((AnnotatedTerm) t).getSubterm();
			return null;
		}
		Theory theory = t.getTheory();
		if (r.getReplacement() == theory.mTrue && r.isNeutralReplacement())
			return new ReplaceByTerm(t, theory.mFalse, true);
		if (r.getReplacement() == theory.mFalse && r.isNeutralReplacement()) {
			if (t instanceof ApplicationTerm) {
				ApplicationTerm at = (ApplicationTerm) t;
				// replace f-app
				if (at.getParameters().length > 0)
					return new ReplaceByFreshTerm(t);
			} // application term
			// give up
			return null;
		} else if (t instanceof ApplicationTerm) {
			// Can be either neutrals or ite or store
			ApplicationTerm at = (ApplicationTerm) t;
			if (at.getFunction().getName().equals("ite")) {
				if (r.getReplacement() == at.getParameters()[1])
					return new ReplaceByTerm(t, at.getParameters()[2], true, false);
				else if (!r.isNeutralReplacement()
						|| r.getReplacement() == at.getParameters()[2])
					return null;
			} else if (at.getFunction().getName().equals("store")
					&& r.getReplacement() == at.getParameters()[0])
				return new ReplaceByFreshTerm(t);
			if (at.getParameters().length > 0)
				return new ReplaceByFreshTerm(t);
		}
		return null;
	}
	
	private boolean computeSubsts() {
		TermCollector tc = new TermCollector(mDepth);
		tc.add(mCmd.getTerm(mUnletRelet));
		List<Term> found = tc.getTerms();
		mSubsts = new ArrayList<Substitution>(found.size());
		for (Term t : found) {
			Substitution subst = getSubstition(t);
			if (subst != null)
				mSubsts.add(subst);
		}
		return !found.isEmpty();
	}
	
	private void stepSubsts() {
		List<Substitution> old = mSubsts;
		mSubsts = new ArrayList<Substitution>(old.size());
		for (Substitution cur : old) {
			if (cur.isActive()) {
				if (cur.isRecurse()) {
					Substitution rec = getSubstition(
							((ReplaceByTerm) cur).getReplacement());
					if (rec != null)
						mSubsts.add(rec);
				}
				continue;
			}
			Substitution next = getNextSubstitution(cur);
			if (next != null)
				mSubsts.add(next);
		}
	}
	
	public List<Substitution> getSubstitutions() {
		return mSubsts;
	}

	public int getDepth() {
		return mDepth;
	}
	
}
