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
import java.util.function.BiFunction;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.EprPredicate;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.EprTheory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.clauses.ClauseEprLiteral;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.dawgs.dawgstates.DawgState;

/**
 * Represents a literal on the DPLL decide stack of the EprTheory.
 * This special literal consists of a quantified literal together with a
 * data structure restricting the possible groundings of that literal.
 *
 * @author Alexander Nutz
 */
public abstract class DecideStackLiteral extends DecideStackEntry implements IEprLiteral, Comparable<DecideStackLiteral> {

//	/**
//	 * The index on the decide stack of its push state that this DecideStackLiteral has.
//	 */
//	protected final int mIndexOnPushStateStack;
//
//	/**
//	 * The index of the push state on the stateManager's push state stack
//	 */
//	protected final int mPushStateStackIndex;

	protected final boolean mPolarity;
	protected final EprPredicate mPred;
	protected DawgState<ApplicationTerm, EprTheory.TriBool> mOldDawg;

	/**
	 * Stores all the groundings for which this.atom is decided with this.polarity
	 * by this DecideStackLiteral
	 */
	protected DawgState<ApplicationTerm, Boolean> mDawg;

	protected Set<ClauseEprLiteral> mConcernedClauseLiterals = new HashSet<>();



	public DecideStackLiteral(final boolean polarity,
			final EprPredicate pred, final DawgState<ApplicationTerm, Boolean> dawg, final int index) {
		super(index);
		mPolarity = polarity;
		mPred = pred;
		mDawg = dawg;
//		mPushStateStackIndex = index.first;
//		mIndexOnPushStateStack = index.second;
//		mIndex = new DslIndex(index.first, index.second);

		register();
	}

	@Override
	public boolean getPolarity() {
		return mPolarity;
	}

	@Override
	public EprPredicate getEprPredicate() {
		return mPred;
	}

	/**
	 * Checks if this literal's dawg talks about the point described by arguments.
	 * arguments may only contain constants.
	 * @param arguments
	 * @return
	 */
	public boolean talksAboutPoint(final Term[] arguments) {
		assert false : "TODO: implement";
		return false;
	}

	@Override
	public DawgState<ApplicationTerm, Boolean> getDawg() {
		return mDawg;
	}

//	/**
//	 *
//	 * @return true iff mDawg's language is a singleton set.
//	 */
//	public boolean isOnePoint() {
//		return mDawg.isSingleton();
//	}
//
//	public List<ApplicationTerm> getPoint() {
//		assert isOnePoint();
//		return mDawg.iterator().next();
//	}

	private void register() {
		mPred.registerEprLiteral(this);
	}

	/**
	 * This is called when this dsl is removed from the decide stack.
	 * It should purge this dsl from every data structure where it was registered.
	 */
	@Override
	public void unregister() {
		mPred.unregisterEprLiteral(this);
		for (final ClauseEprLiteral cl : mConcernedClauseLiterals) {
			cl.unregisterIEprLiteral(this);
		}
	}

	@Override
	public void registerConcernedClauseLiteral(final ClauseEprLiteral cel) {
		mConcernedClauseLiterals.add(cel);
	}

//	/**
//	 * @return
//	 */
//	public int getPushStateDecideStackIndex() {
//		return mIndexOnPushStateStack;
//	}
//
//	public int getPushStateIndex() {
//		return mPushStateStackIndex;
//	}

//	public int getDecideStackIndex() {
//		return mIndex;
//	}

	@Override
	public int compareTo(final DecideStackLiteral other) {
//		return this.mIndex.compareTo(other.mIndex);
		return nr - other.nr;
	}

//	static class DslIndex implements Comparable<DslIndex> {
//
//		final int indexOfPushState;
//		final int indexOnPushStatesDecideStack;
//
//		public DslIndex(int indexOfPushState, int indexOfPushStatesDecideStack) {
//			this.indexOfPushState = indexOfPushState;
//			this.indexOnPushStatesDecideStack = indexOfPushStatesDecideStack;
//		}
//
//		/**
//		 * DslIndices are compared lexicographically. First, the index of the push state a dsl is on
//		 * is compared. Only if that is equal the positions of the two literals on that push state's
//		 * decide stack is compared.
//		 */
//		@Override
//		public int compareTo(DslIndex o) {
//			int comp1 = Integer.compare(this.indexOfPushState, o.indexOfPushState);
//			if (comp1 == 0) {
//				return Integer.compare(this.indexOnPushStatesDecideStack, o.indexOnPushStatesDecideStack);
//			}
//			return comp1;
//		}
//	}

	@Override
	public void push() {
		final BiFunction<EprTheory.TriBool, Boolean, EprTheory.TriBool> combinator = (old, setLit) -> {
			return (setLit ? (mPolarity ? EprTheory.TriBool.TRUE : EprTheory.TriBool.FALSE) : old);
		};
		mOldDawg = mPred.getDawg();
		mPred.setDawg(mPred.getEprTheory().getDawgFactory().createProduct(mOldDawg, mDawg, combinator));
	}

	@Override
	public void pop() {
		mPred.setDawg(mOldDawg);
	}
}
