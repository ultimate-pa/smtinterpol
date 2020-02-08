package de.uni_freiburg.informatik.ultimate.smtinterpol.convert;

import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.ILiteral;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.NamedAtom;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.cclosure.CCTerm;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.linar.LinVar;

public class ClausifierTermInfo {
	// flags for boolean terms
	static final int POS_AXIOMS_ADDED = 1;
	static final int NEG_AXIOMS_ADDED = 2;
	static final int POS_AUX_AXIOMS_ADDED = 4;
	static final int NEG_AUX_AXIOMS_ADDED = 8;
	// flags for all interpreted or boolean terms
	static final int AUX_AXIOM_ADDED = 16;

	private int mFlags;

	private NamedAtom mAtom;
	private CCTerm mCCTerm;
	private LinVar mLAVar;
	private Rational mLAFactor;
	private Rational mLAOffset;
	private ILiteral mLiteral;

	public boolean hasCCTerm() {
		return mCCTerm != null;
	}

	public boolean hasLAVar() {
		return mLAOffset != null;
	}

	public CCTerm getCCTerm() {
		return mCCTerm;
	}

	public void setCCTerm(CCTerm ccterm) {
		mCCTerm = ccterm;
	}

	public LinVar getLAVar() {
		return mLAVar;
	}

	public Rational getLAOffset() {
		return mLAOffset;
	}

	public Rational getLAFactor() {
		return mLAFactor;
	}

	public void setLAVar(Rational factor, LinVar lv, Rational offset) {
		mLAFactor = factor;
		mLAVar = lv;
		mLAOffset = offset;
	}

	public int getFlags() {
		return mFlags;
	}

	public void setFlags(int flag) {
		mFlags |= flag;
	}
}
