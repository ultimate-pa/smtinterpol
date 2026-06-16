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
package de.uni_freiburg.informatik.ultimate.smtinterpol.convert;

import java.util.ArrayDeque;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.FunctionSymbol;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.smtinterpol.proof.SourceAnnotation;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.cclosure.CCParameter;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.cclosure.CCTerm;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.cclosure.CClosure;

public class CCTermBuilder {
	/**
	 * The clausifier.
	 */
	private final Clausifier mClausifier;
	private final SourceAnnotation mSource;

	private final ArrayDeque<Operation> mOps = new ArrayDeque<>();
	/**
	 * The converted results as {@link CCParameter}s: the term that produced {@code mConverted.peek()} has value
	 * {@code peek().getCCTerm() + peek().getOffset()}. The offset carries the {@code +5} of an offset-free term like
	 * {@code x+5} up to the enclosing application, where it ends up in that argument's {@link CCParameter}. Offsets are
	 * {@link Rational#ZERO} (i.e. a bare {@link CCTerm}) unless offset equalities are enabled.
	 */
	private final ArrayDeque<CCParameter> mConverted = new ArrayDeque<>();

	public CCTermBuilder(Clausifier clausifier, final SourceAnnotation source) {
		mClausifier = clausifier;
		mSource = source;
	}

	private void pushResult(final CCTerm ccTerm, final Rational offset) {
		mConverted.push(CCParameter.of(ccTerm, offset));
	}

	public CCTerm convert(final Term t) {
		mOps.push(new BuildCCTerm(t));
		while (!mOps.isEmpty()) {
			mOps.pop().perform();
		}
		// The caller asked for the CCTerm of the term; a top-level numeric constant offset (e.g. the +5 of x+5) is not
		// part of the CCTerm and is recovered by the caller from the term itself, so it is dropped here (as before).
		final CCParameter res = mConverted.pop();
		assert mConverted.isEmpty();
		return res.getCCTerm();
	}

	private class BuildCCTerm implements Operation {
		private final Term mTerm;

		public BuildCCTerm(final Term term) {
			mTerm = term;
		}

		@Override
		public void perform() {
			CCTerm ccTerm = mClausifier.getCCTerm(mTerm);
			if (ccTerm != null) {
				pushResult(ccTerm, mClausifier.getTermConstant(mTerm));
			} else {
				final CClosure cclosure = mClausifier.getCClosure();
				final Term offsetFree = mClausifier.getOffsetFreeTerm(mTerm);
				if (offsetFree != mTerm) {
					// Numeric term with a non-zero constant: build the offset-free CCTerm and remember the constant.
					mOps.push(new MapOffsetFreeTerm(mTerm, mClausifier.getTermConstant(mTerm)));
					mOps.push(new BuildCCTerm(offsetFree));
				} else if (Clausifier.needCCTerm(mTerm) && ((ApplicationTerm) mTerm).getParameters().length > 0) {
					final FunctionSymbol fs = ((ApplicationTerm) mTerm).getFunction();
					if (fs.isIntern() && fs.getName() == "select") {
						mClausifier.getArrayTheory().cleanCaches();
					}
					final ApplicationTerm at = (ApplicationTerm) mTerm;
					final Term[] args = at.getParameters();
					mOps.push(new BuildCCAppTerm(at));
					for (int i = args.length - 1; i >= 0; --i) {
						mOps.push(new BuildCCTerm(args[i]));
					}
				} else {
					// We have an intern function symbol
					ccTerm = cclosure.createAnonTerm(mTerm);
					cclosure.addTerm(ccTerm, mTerm);
					mClausifier.shareCCTerm(mTerm, ccTerm);
					mClausifier.addTermAxioms(mTerm, mSource);
					pushResult(ccTerm, Rational.ZERO);
				}
			}
		}
	}

	/**
	 * Maps a numeric term with a non-zero constant to the (already built) CCTerm of its offset-free part, and pushes
	 * that CCTerm together with the constant offset.
	 */
	private class MapOffsetFreeTerm implements Operation {
		private final Term mTerm;
		private final Rational mOffset;

		public MapOffsetFreeTerm(final Term term, final Rational offset) {
			mTerm = term;
			mOffset = offset;
		}

		@Override
		public void perform() {
			final CCParameter offsetFreeParam = mConverted.pop();
			assert offsetFreeParam.getOffset().equals(Rational.ZERO) : "offset-free part must have zero offset";
			final CCTerm offsetFreeCCTerm = offsetFreeParam.getCCTerm();
			if (mClausifier.getCCTerm(mTerm) == null) {
				mClausifier.shareCCTerm(mTerm, offsetFreeCCTerm);
				mClausifier.addTermAxioms(mTerm, mSource);
			}
			pushResult(offsetFreeCCTerm, mOffset);
		}
	}

	/**
	 * Helper class to build the intermediate CCAppTerms. Note that all these terms will be func terms.
	 *
	 * @author Juergen Christ
	 */
	private class BuildCCAppTerm implements Operation {
		private final ApplicationTerm mAppTerm;

		public BuildCCAppTerm(ApplicationTerm appTerm) {
			mAppTerm = appTerm;
		}

		@Override
		public void perform() {
			final CCParameter[] args = new CCParameter[mAppTerm.getParameters().length];
			for (int i = args.length - 1; i >= 0; i--) {
				args[i] = mConverted.pop();
			}
			assert mClausifier.getCCTerm(mAppTerm) == null;
			final CCTerm ccTerm =
					mClausifier.getCClosure().createAppTerm(mAppTerm.getFunction(), args, mSource);
			mClausifier.getCClosure().addTerm(ccTerm, mAppTerm);
			mClausifier.shareCCTerm(mAppTerm, ccTerm);
			mClausifier.addTermAxioms(mAppTerm, mSource);
			// the application term itself is not numeric-offset; its value is the application
			pushResult(ccTerm, Rational.ZERO);
		}
	}
}