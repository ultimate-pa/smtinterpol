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
import java.util.Arrays;
import java.util.Collections;
import java.util.List;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.Clause;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.Literal;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.EprPredicate;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.EprTheory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.atoms.EprPredicateAtom;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.dawgs.IDawg;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.partialmodel.IEprLiteral;
import de.uni_freiburg.informatik.ultimate.util.datastructures.ScopedHashSet;

/**
 *
 * @author Alexander Nutz (nutz@informatik.uni-freiburg.de)
 *
 */
public abstract class ClauseEprLiteral extends ClauseLiteral {

	/**
	 * Flag is set if the fields that are used to determine the state (fulfilled/fulfillable/refuted points)
	 * of this ClauseLiteral have been changed since the last computation of that state.
	 */
	protected boolean mIsStateDirty = true;

	protected final EprPredicateAtom mEprPredicateAtom;

	/**
	 * The literals on the current epr decide stack that contradict this literal at
	 * least on one point, potentially on many or all points that this literal talks about.
	 * (e.g. when P(a,x) is on the decide stack it contradicts ~P(y,b) on the point (a,b).)
	 */
	protected final ScopedHashSet<IEprLiteral> mPartiallyConflictingDecideStackLiterals =
			new ScopedHashSet<IEprLiteral>();

	protected final ScopedHashSet<IEprLiteral> mPartiallyFulfillingDecideStackLiterals =
			new ScopedHashSet<IEprLiteral>();

	/**
	 * The TermVariables (EDIT and constants) that this clauseLiterals's atom's arguments have in the clause
	 * this literal belongs to.
	 * (typically the same as mAtom.getArguments(), except that constants there have been
	 *  replaced by fresh TermVariables
	 *  EDIT: now we are just keeping the constants here, so this list is practically identical
	 *   to mAtom.getArguments()
	 *   We deal with repetitions and constants through mTranslationForClause)
	 */
	protected final List<Term> mArgumentTerms;

	protected final List<Object> mArgumentTermsAsObjects;

	public ClauseEprLiteral(boolean polarity, EprPredicateAtom atom, EprClause clause, EprTheory eprTheory) {
		super(polarity, atom, clause, eprTheory);
		mEprPredicateAtom = atom;
		mArgumentTerms = Collections.unmodifiableList(Arrays.asList(atom.getArguments()));

		List<Object> l =  new ArrayList<Object>();
		for (Term at : mArgumentTerms) {
			l.add(at);
		}
		mArgumentTermsAsObjects = Collections.unmodifiableList(l);
	}

	public EprPredicate getEprPredicate()  {
		return  mEprPredicateAtom.getEprPredicate();
	}

	public void addPartiallyConflictingEprLiteral(IEprLiteral el) {
		el.registerConcernedClauseLiteral(this);
		mPartiallyConflictingDecideStackLiterals.add(el);
		mIsStateDirty = true;
		mEprClause.mClauseStateIsDirty = true;
	}

	public void addPartiallyFulfillingEprLiteral(IEprLiteral el) {
		el.registerConcernedClauseLiteral(this);
		mPartiallyFulfillingDecideStackLiterals.add(el);
		mIsStateDirty = true;
		mEprClause.mClauseStateIsDirty = true;
	}

	public Set<IEprLiteral> getPartiallyConflictingDecideStackLiterals() {
		return Collections.unmodifiableSet(mPartiallyConflictingDecideStackLiterals);
	}

	/**
	 * notifies the clause about the beginning of a push/pop scope
	 */
	public void beginScope() {
		mPartiallyConflictingDecideStackLiterals.beginScope();
		mPartiallyFulfillingDecideStackLiterals.beginScope();
	}

	/**
	 * notifies the clause about the ending of a push/pop scope
	 */
	public void endScope() {
		mPartiallyConflictingDecideStackLiterals.endScope();
		mPartiallyFulfillingDecideStackLiterals.endScope();
		mIsStateDirty = true;
		mEprClause.mClauseStateIsDirty = true;
	}

	public List<Term> getArguments() {
		return mArgumentTerms;
	}

	/**
	 * Returns the same as getArguments, only in a list of objects
	 * @return
	 */
	public List<Object> getArgumentsAsObjects() {
		return mArgumentTermsAsObjects;
	}


	/**
	 * Determines if the point(s) this epr literal talks about have an empty intersection
	 * with the points in the given dawg, i.e., if setting a decide stack literal with the
	 * given dawg influences the fulfillment state of this clauseLiteral or not.
	 * @param dawg
	 * @return true iff the dawg and this literal don't talk about at least one common point.
	 */
	public abstract boolean isDisjointFrom(IDawg<ApplicationTerm, TermVariable> dawg) ;

	public void unregisterIEprLiteral(IEprLiteral el) {
		boolean success = false;
		success |= mPartiallyConflictingDecideStackLiterals.remove(el);
		success |= mPartiallyFulfillingDecideStackLiterals.remove(el);
		assert success : "something wrong with the registration??";
		mIsStateDirty = true;
		mEprClause.mClauseStateIsDirty = true;
	}


	public abstract Clause getGroundingForGroundLiteral(IDawg<ApplicationTerm, TermVariable> dawg, Literal groundLiteral);
}
