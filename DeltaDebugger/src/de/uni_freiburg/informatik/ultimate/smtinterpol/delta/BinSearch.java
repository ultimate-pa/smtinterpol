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

import java.io.IOException;
import java.util.ArrayDeque;
import java.util.List;

public class BinSearch<E> {

	public static interface Driver<E> {
		public Boolean prepare(List<E> sublist);
		public void failure(List<E> sublist);
		public void success(List<E> sublist);
	}

	private static class IntPair {
		final int mFirst;
		final int mSecond;
		final boolean mBuddy;
		public IntPair(int f, int s) {
			this(f, s, false);
		}
		public IntPair(int f, int s, boolean buddy) {
			mFirst = f;
			mSecond = s;
			mBuddy = buddy;
		}
	}

	private final List<E> mList;
	private final Driver<E> mDriver;
	private final ArrayDeque<IntPair> mTodo;

	public BinSearch(List<E> list, Driver<E> driver) {
		mList = list;
		mDriver = driver;
		mTodo = new ArrayDeque<IntPair>();
	}

	/**
	 * Split a region into two regions.  The split pushes first the right part
	 * of the split onto the todo stack and then creates the left part and
	 * pushes it.  The left part has the buddy flag set since we assume we
	 * already know that the interval we are splitting yields a test failure.
	 * Thus, if the left part is a success, applying the right part will
	 * recreate the whole interval we are currently splitting.  Assuming
	 * deterministic behaviour of our system under test, we will get a failure
	 * for the right part.
	 * @param first  The start of the interval.
	 * @param second The end of the interval.
	 */
	private void split(int first, int second) {
		// Split into two new sublists
		final int mid = first / 2 + second / 2
				+ (first & second & 1);
		if (mid != first) {
			mTodo.push(new IntPair(mid, second));
			mTodo.push(new IntPair(first, mid, true));
		}
	}

	public boolean run(Minimizer tester)
		throws IOException, InterruptedException {
		if (mList.isEmpty()) {
			return false;
		}
		boolean result = false;
		mTodo.add(new IntPair(0, mList.size()));
		while (!mTodo.isEmpty()) {
			final IntPair p = mTodo.poll();
			final List<E> sublist = mList.subList(p.mFirst, p.mSecond);
			if (sublist.isEmpty()) {
				continue;
			}
			final Boolean seen = mDriver.prepare(sublist);
			final boolean success = (seen == null ? tester.test() : seen);
			if (success) {
				if (seen == null) {
					mDriver.success(sublist);
				}
				result = true;
				if (p.mBuddy) {
					// We already know that the buddy cannot succeed.
					// Split the buddy to prevent a meaningless test
					final IntPair buddy = mTodo.poll();
					split(buddy.mFirst, buddy.mSecond);
				}
			} else {
				if (seen == null) {
					mDriver.failure(sublist);
				}
				split(p.mFirst, p.mSecond);
			}
		}
		return result;
	}

}
