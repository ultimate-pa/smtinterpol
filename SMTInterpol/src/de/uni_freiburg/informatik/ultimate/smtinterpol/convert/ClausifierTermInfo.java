package de.uni_freiburg.informatik.ultimate.smtinterpol.convert;

import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.ILiteral;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.cclosure.CCTerm;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.linar.LASharedTerm;

/**
 * A helper class to remember conversion information about all subterms and subformulas of the asserted formulas. It
 * stores for every subterm or a subformula has been converted before what its conversion is.
 *
 * For a subformula (a subterm of type Bool), we remember the auxiliary literal used for CNF conversion. For a subterm
 * we remember its CCTerm (node in the equivalence graph) if it was created, or a LASharedTerm if it lives in the theory
 * of linear arithmetic.
 *
 * There are also flags that indicate for a subformula, whether the formula was asserted positively or negatively, and
 * whether the auxiliary axioms for the positive or negative literals were added. For a subterm there are flags that
 * indicate for a subterm and whether its auxiliary axioms were added, whether it has a CCTerm or lives in linear
 * arithmetic. However, these flags are not stored in this class, but in another ScopedHashMap in Clausifier. The reason
 * is that we need to remember for each scope what the flags were at this scope.
 *
 * @author Jürgen Christ, Jochen Hoenicke
 */
public class ClausifierTermInfo {
	// flags for boolean terms
	public static final int POS_AXIOMS_ADDED = 1;
	public static final int NEG_AXIOMS_ADDED = 2;
	public static final int POS_AUX_AXIOMS_ADDED = 4;
	public static final int NEG_AUX_AXIOMS_ADDED = 8;
	// flags for all interpreted or boolean terms
	public static final int AUX_AXIOM_ADDED = 16;

	public static final int HAS_CC_TERM = 32;
	public static final int HAS_LA_TERM = 64;
	public static final int HAS_LITERAL = 128;

	private CCTerm mCCTerm;
	private LASharedTerm mLATerm;
	private ILiteral mLiteral;

	public boolean hasCCTerm() {
		return mCCTerm != null;
	}

	public boolean hasLAVar() {
		return mLATerm != null;
	}

	public CCTerm getCCTerm() {
		return mCCTerm;
	}

	public void setCCTerm(final CCTerm ccterm) {
		mCCTerm = ccterm;
	}

	public LASharedTerm getLATerm() {
		return mLATerm;
	}

	public void setLATerm(final LASharedTerm laterm) {
		mLATerm = laterm;
	}

	public ILiteral getLiteral() {
		return mLiteral;
	}

	public void setLiteral(final ILiteral literal) {
		mLiteral = literal;
	}

	@Override
	public String toString() {
		return "TermInfo[CC:" + mCCTerm + ",LA:" + mLATerm + ",lit:" + mLiteral + "]";
	}
}
