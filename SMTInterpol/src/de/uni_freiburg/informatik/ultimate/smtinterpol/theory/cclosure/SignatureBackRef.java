/*
 * Copyright (C) 2009-2026 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.smtinterpol.theory.cclosure;

/**
 * A back-reference from a representative to a signature: the representative appears in the signature's term list at
 * listIndex, and the trigger is the value stored in the global map for that signature. When the representative
 * changes (merge), this back-ref is pushed to the todo stack and processed at checkpoint (rehash, merge triggers).
 *
 * @author Jochen Hoenicke, Jürgen Christ
 */
public final class SignatureBackRef {

	private final Signature mSignature;
	private final int mListIndex;
	private final Trigger mTrigger;

	public SignatureBackRef(final Signature signature, final int listIndex, final Trigger trigger) {
		mSignature = signature;
		mListIndex = listIndex;
		mTrigger = trigger;
	}

	public Signature getSignature() {
		return mSignature;
	}

	public int getListIndex() {
		return mListIndex;
	}

	public Trigger getTrigger() {
		return mTrigger;
	}
}
