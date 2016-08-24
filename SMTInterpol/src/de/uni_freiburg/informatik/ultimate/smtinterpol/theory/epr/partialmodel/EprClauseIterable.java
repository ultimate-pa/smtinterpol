package de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.partialmodel;

import java.util.Iterator;
import java.util.Stack;

import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.clauses.EprClause;

public class EprClauseIterable implements Iterable<EprClause> {

	Iterator<EprPushState> mPushStateStack;

	public EprClauseIterable(Stack<EprPushState> pushStateStack) {
		mPushStateStack = pushStateStack.iterator();
	}

	@Override
	public Iterator<EprClause> iterator() {
		return new EprClauseIterator();
	}

	class EprClauseIterator implements Iterator<EprClause> {
		
		EprClause mNext;

		Iterator<EprClause> mCurrentPushStateClauseIterator;

		EprClauseIterator() {
			mNext = findNextEprClause();
		}

		public EprClause findNextEprClause() {
			if (! mPushStateStack.hasNext()) {
				return null;
			}
			mCurrentPushStateClauseIterator = mPushStateStack.next().getClausesIterator();
			
			// look for the first push state that has a clause
			while (! mCurrentPushStateClauseIterator.hasNext()) {
				if (!mPushStateStack.hasNext()) {
					return null;
				}
				mCurrentPushStateClauseIterator = mPushStateStack.next().getClausesIterator();
			}
			return mCurrentPushStateClauseIterator.next();
		}

		@Override
		public boolean hasNext() {
			return mNext != null;
		}

		@Override
		public EprClause next() {
			mNext = findNextEprClause();
			return mNext;
		}
		
	}
}
