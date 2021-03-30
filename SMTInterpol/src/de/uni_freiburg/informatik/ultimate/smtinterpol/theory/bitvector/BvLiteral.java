package de.uni_freiburg.informatik.ultimate.smtinterpol.theory.bitvector;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.DPLLAtom;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.Literal;

public class BvLiteral {

	private boolean mSign;
	private final Literal mLiteral;
	private final Term mTerm;
	private Term mBitBlastAtom;

	// enum type der relation
	public BvLiteral(final Literal lit, final Term relationTerm, final boolean sign) {
		mLiteral = lit;
		mTerm = relationTerm;
		mSign = sign;
		mBitBlastAtom = null;
	}

	public DPLLAtom getAtom() {
		return mLiteral.getAtom();
	}

	public Term getTerm() {
		return mTerm;
	}

	public void setBitBlastAtom(final Term t) {
		mBitBlastAtom = t;
	}

	public Term getBitBlastAtom() {
		return mBitBlastAtom;
	}

	public Literal getLiteral() {
		return mLiteral;
	}

	public boolean getSign() {
		// True if the Literal has form (not Atom) OR (= not bvult(...))
		return mSign;
	}



	public boolean isBvult() {
		if (mTerm instanceof ApplicationTerm) {
			if (((ApplicationTerm) mTerm).getFunction().getName().equals("bvult")) {
				return true;
			}
		}
		return false;
	}

	public Term getLhs() {
		if (mTerm instanceof ApplicationTerm) {
			return ((ApplicationTerm) mTerm).getParameters()[0];
		}
		return null;
	}

	public Term getRhs() {
		if (mTerm instanceof ApplicationTerm) {
			return ((ApplicationTerm) mTerm).getParameters()[1];
		}
		return null;
	}

	public void setSign(final boolean sign) {
		mSign = sign;

	}

}