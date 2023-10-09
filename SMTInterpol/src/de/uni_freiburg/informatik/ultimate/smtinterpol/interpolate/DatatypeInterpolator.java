/*
 * Copyright (C) 2023 University of Freiburg
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

package de.uni_freiburg.informatik.ultimate.smtinterpol.interpolate;

import java.util.ArrayList;
import java.util.BitSet;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.DataType;
import de.uni_freiburg.informatik.ultimate.logic.DataType.Constructor;
import de.uni_freiburg.informatik.ultimate.logic.FunctionSymbol;
import de.uni_freiburg.informatik.ultimate.logic.SMTLIBConstants;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.Theory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.interpolate.Interpolator.LitInfo;
import de.uni_freiburg.informatik.ultimate.smtinterpol.interpolate.Interpolator.Occurrence;
import de.uni_freiburg.informatik.ultimate.smtinterpol.util.SymmetricPair;

/**
 * The interpolator for the Theory of datatypes.
 *
 * @author Leon Cacace, Jochen Hoenicke
 */
public class DatatypeInterpolator {

	private final Interpolator mInterpolator;
	private final Theory mTheory;
	private final int mNumInterpolants;
	private InterpolatorClauseInfo mClauseInfo;
	// a set for each Interpolant, to be filled with the literals of the interpolant
	private final Set<Term>[] mInterpolants;
	// the equalities of the lemma
	private HashMap<SymmetricPair<Term>, Term> mEqualityLiterals;
	private HashMap<SymmetricPair<Term>, LitInfo> mEqualityInfos;
	// the disequality of the lemma
	private HashMap<SymmetricPair<Term>, Term> mDisequalityLiterals;
	private HashMap<SymmetricPair<Term>, LitInfo> mDisequalityInfos;
	// the testers as a map from their inner Term to their Occurrence
	private HashMap<Term, LitInfo> mTestersOccurrence;
	// the testers as a map from their inner Term to their function name
	private HashMap<Term, FunctionSymbol> mTestersFunctions;
	// the ordered literals of the lemma
	private Term[] mPath;

	// the partitions for which every literal so far was shared
	BitSet mAllInA;

	private int mMaxColor;
	private int mLastColor;

	// stores for cycles if the recent relation between literals was a select or a construct
	private boolean mIsSelectRel;

	// for each partition, the boundary terms thats start the A Path
	private final Term[] mStart;
	// for each partition, the boundary terms thats end the A Path
	private final Term[] mEnd;
	//
	private final Term[] mHead;
	// for each partition, the indices of the literals where the current A-path started (-1 if there is none for that partition)
	private final int[] mStartIndices;
	// for each partition, the indices of the literals where the A-path was closed
	// but not opened (-1 if there is none for this partition)
	private final int[] mEndIndices;
	//
	private final int[] mHeadIndices;

	// array to store select functions later applied to the start of the a path
	private String[] mStartSelectors;
	// array to store constructor names for testers
	private String[] mStartConstructors;
	// array to store tester functions
	private FunctionSymbol[] mStartTesters;

	@SuppressWarnings("unchecked")
	public DatatypeInterpolator(final Interpolator interpolator) {
		mInterpolator = interpolator;
		mTheory = interpolator.mTheory;
		mNumInterpolants = interpolator.mNumInterpolants;
		mInterpolants = new Set[mNumInterpolants];
		for (int i = 0; i < mNumInterpolants; i++) {
			mInterpolants[i] = new HashSet<>();
		}
		mStart = new Term[mNumInterpolants];
		mEnd = new Term[mNumInterpolants];
		mHead = new Term[mNumInterpolants];
		mStartIndices = new int[mNumInterpolants];
		mEndIndices = new int[mNumInterpolants];
		mHeadIndices = new int[mNumInterpolants];
		mAllInA = new BitSet(mNumInterpolants);
	}

	/**
	 * Computes interpolants for a datatype lemma.
	 *
	 * @param clauseInfo the clause info for the datatype lemma.
	 * @return the array of interpolants
	 */
	public Term[] computeDatatypeInterpolants(final InterpolatorClauseInfo clauseInfo) {
		mClauseInfo = clauseInfo;
		mEqualityLiterals = new HashMap<>();
		mDisequalityLiterals = new HashMap<>();
		mEqualityInfos = new HashMap<>();
		mDisequalityInfos = new HashMap<>();
		mTestersOccurrence = new HashMap<>();
		mTestersFunctions = new HashMap<>();
		for (final Term literal : mClauseInfo.getLiterals()) {
			final ApplicationTerm atom = (ApplicationTerm) mInterpolator.getAtom(literal);
			final LitInfo atomOccurenceInfo = mInterpolator.getAtomOccurenceInfo(atom);
			final Term left = atom.getParameters()[0];
			final Term right = atom.getParameters()[1];
			if (left instanceof ApplicationTerm && ((ApplicationTerm) left).getFunction().getName().equals(SMTLIBConstants.IS)) {
				mTestersFunctions.put(((ApplicationTerm) left).getParameters()[0], ((ApplicationTerm) left).getFunction());
				mTestersOccurrence.put(((ApplicationTerm) left).getParameters()[0], atomOccurenceInfo);
			} else if (right instanceof ApplicationTerm && ((ApplicationTerm) left).getFunction().getName().equals(SMTLIBConstants.IS)) {
				mTestersFunctions.put(((ApplicationTerm) right).getParameters()[0], ((ApplicationTerm) right).getFunction());
				mTestersOccurrence.put(((ApplicationTerm) right).getParameters()[0], atomOccurenceInfo);
			}
			final SymmetricPair<Term> pair = new SymmetricPair<>(left, right);
			if (atom != literal) {
				mEqualityLiterals.put(pair, atom);
				mEqualityInfos.put(new SymmetricPair<>(left, right), atomOccurenceInfo);
			} else {
				mDisequalityLiterals.put(pair, atom);
				mDisequalityInfos.put(new SymmetricPair<>(left, right), atomOccurenceInfo);
			}

		}
		final Object[] annot = ((Object[]) clauseInfo.getLemmaAnnotation());

		switch (clauseInfo.getLemmaType()) {
		case ":dt-project":
			return interpolateDTProject(annot);
		case ":dt-tester":
			return interpolateDTTester(annot);
		case ":dt-constructor":
			return interpolateDTConstructor(annot);
		case ":dt-injective":
			return interpolateDTInjective(annot);
		case ":dt-disjoint":
			return interpolateDTDisjoint(annot);
		case ":dt-unique":
			return interpolateDTUnique(annot);
		case ":dt-cases":
			return interpolateDTCases(annot);
		case ":dt-cycle":
			return interpolateDTCycle(annot);
		default:
			throw new UnsupportedOperationException("lemma unknown in datatype interpolator");
		}
	}

	/**
	 * Interpolate a datatype uniqueness conflict. The conflict has the form
	 * {@code ((_ is cons1) u1) == true, ((_ is cons2) u2) == true, u1 == u2}. The
	 * last equality is missing if it is trivial.
	 *
	 * @param testers the argument of the :dt-unique annotation. It is a list of the
	 *                two tester terms {@code ((_ is consi) ui)}.
	 * @return The array of interpolants.
	 */
	private Term[] interpolateDTUnique(Object[] testers) {
		final ApplicationTerm firstTester = (ApplicationTerm) testers[0];
		final Term firstSymbol = firstTester.getParameters()[0];
		final LitInfo firstTesterInfo = mEqualityInfos.get(new SymmetricPair<>(mTheory.mTrue, firstTester));
		final ApplicationTerm secondTester = (ApplicationTerm) testers[1];
		final Term secondSymbol = secondTester.getParameters()[0];
		final LitInfo secondTesterInfo = mEqualityInfos.get(new SymmetricPair<>(mTheory.mTrue, secondTester));
		final LitInfo equalityInfo = (firstSymbol == secondSymbol) ? null
				: mEqualityInfos.get(new SymmetricPair<>(firstSymbol, secondSymbol));

		final Term[] interpolants = new Term[mNumInterpolants];
		for (int color = 0; color < mNumInterpolants; color++) {
			Term interpolant;
			if (firstTesterInfo.isAorShared(color) && secondTesterInfo.isAorShared(color)) {
				// Both testers are in A
				if (equalityInfo != null && equalityInfo.isBLocal(color)) {
					// equalityInfo is B local - interpolant is negated equality.
					interpolant = mTheory.term(SMTLIBConstants.NOT,
							mTheory.term(SMTLIBConstants.EQUALS, firstSymbol, secondSymbol));
				} else {
					// everything is in A
					interpolant = mTheory.mFalse;
				}
			} else if (firstTesterInfo.isBorShared(color) && secondTesterInfo.isBorShared(color)) {
				// both testers are in B
				if (equalityInfo != null && equalityInfo.isALocal(color)) {
					// equality is in A, so that is the interpolant.
					interpolant = mTheory.term(SMTLIBConstants.EQUALS, firstSymbol, secondSymbol);
				} else {
					// everything is in B
					interpolant = mTheory.mTrue;
				}
			} else {
				// one tester is A-local, the other is B-local
				final ApplicationTerm aTester = firstTesterInfo.isALocal(color) ? firstTester : secondTester;
				if (equalityInfo == null || equalityInfo.isBorShared(color)) {
					// equality is in B, the aTester is the interpolant
					interpolant = aTester;
				} else if (equalityInfo.isMixed(color)) {
					// equality is mixed, apply aTester.getFunction() to mixed var
					interpolant = mTheory.term(aTester.getFunction(), equalityInfo.getMixedVar());
				} else {
					// equality is A local, apply aTester.getFunction() to shared variable in second
					// tester.
					final Term sharedSymbol = firstTesterInfo.isALocal(color) ? secondSymbol : firstSymbol;
					interpolant = mTheory.term(aTester.getFunction(), sharedSymbol);
				}
			}
			interpolants[color] = interpolant;
		}
		return interpolants;
	}

	/**
	 * Interpolate a datatype dt-disjoint conflict. The conflict has the form
	 * {@code (cons a1 ... an) == (cons' b1 ... bn')}, where cons and cons' are
	 * different constructors.
	 *
	 * @param annot the argument of the :dt-disjoint annotation. It has the form
	 *              {@code :cons (cons a1 ... an) (cons' b1 ... bn'))}.
	 * @return The array of interpolants.
	 */
	private Term[] interpolateDTDisjoint(Object[] annot) {
		final Term[] interpolants = new Term[mNumInterpolants];

		final SymmetricPair<Term> eqLit = mEqualityInfos.keySet().iterator().next();
		final LitInfo eqInfo = mEqualityInfos.get(eqLit);

		for (int color = 0; color < mNumInterpolants; color++) {
			if (eqInfo.isAorShared(color)) {
				interpolants[color] = mTheory.mFalse;
			} else if (eqInfo.isBLocal(color)) {
				interpolants[color] = mTheory.mTrue;
			} else {
				assert eqInfo.isMixed(color);
				final Occurrence lhsOcc = eqInfo.getLhsOccur();
				final Term aTerm = lhsOcc.isALocal(color) ? eqLit.getFirst() : eqLit.getSecond();
				final FunctionSymbol aCons = ((ApplicationTerm) aTerm).getFunction();
				interpolants[color] = mTheory.term(SMTLIBConstants.IS, new String[] { aCons.getName() }, null,
						eqInfo.getMixedVar());
			}
		}
		return interpolants;
	}

	/**
	 * Interpolate a datatype dt-injective conflict. The conflict has the form
	 * {@code (cons a1 ... an) == (cons b1 ... bn), ai != bi}.
	 *
	 * @param annot the argument of the :dt-injective annotation. It has the form
	 *              {@code ((= ai bi) :cons (cons a1 ... an) (cons b1 ... bn))}.
	 * @return The array of interpolants.
	 */
	private Term[] interpolateDTInjective(Object[] annot) {
		final Term[] interpolants = new Term[mNumInterpolants];

		final ApplicationTerm diseqAtom = (ApplicationTerm) annot[0];
		final Term[] diseqParams = diseqAtom.getParameters();
		final LitInfo diseqInfo = mDisequalityInfos.get(new SymmetricPair<>(diseqParams[0], diseqParams[1]));
		final ApplicationTerm firstConsTerm = (ApplicationTerm) annot[2];
		final ApplicationTerm secondConsTerm = (ApplicationTerm) annot[3];
		final LitInfo eqInfo = mEqualityInfos.get(new SymmetricPair<>(firstConsTerm, secondConsTerm));
		String selFunc = null;

		for (int color = 0; color < mNumInterpolants; color++) {
			if (diseqInfo.isAorShared(color) && eqInfo.isAorShared(color)) {
				interpolants[color] = mTheory.mFalse;
			} else if (diseqInfo.isBorShared(color) && eqInfo.isBorShared(color)) {
				interpolants[color] = mTheory.mTrue;
			} else if (diseqInfo.isALocal(color) && eqInfo.isBLocal(color)) {
				interpolants[color] = mTheory.term(SMTLIBConstants.NOT, diseqAtom);
			} else if (diseqInfo.isBLocal(color) && eqInfo.isALocal(color)) {
				interpolants[color] = diseqAtom;
			} else {
				assert eqInfo.isMixed(color);
				if (selFunc == null) {
					selFunc = getSelectorForPair(firstConsTerm, secondConsTerm, diseqParams);
				}
				final Term sharedSelTerm = mTheory.term(selFunc, eqInfo.getMixedVar());
				final Term realDiseq = mDisequalityLiterals.get(new SymmetricPair<>(diseqParams[0], diseqParams[1]));
				final Term[] realDiseqParams = ((ApplicationTerm) realDiseq).getParameters();
				if (diseqInfo.isAorShared(color)) {
					final Term sharedTerm = realDiseqParams[eqInfo.getLhsOccur().isALocal(color) ? 1 : 0];
					interpolants[color] = mTheory.term(SMTLIBConstants.NOT,
							mTheory.term(SMTLIBConstants.EQUALS, sharedTerm, sharedSelTerm));
				} else if (diseqInfo.isBLocal(color)) {
					final Term sharedTerm = realDiseqParams[eqInfo.getLhsOccur().isALocal(color) ? 0 : 1];
					interpolants[color] = mTheory.term(SMTLIBConstants.EQUALS, sharedTerm, sharedSelTerm);
				} else {
					interpolants[color] = mTheory.term(Interpolator.EQ, diseqInfo.getMixedVar(), sharedSelTerm);
				}
			}
		}

		return interpolants;
	}

	/**
	 * Interpolate a datatype constructor conflict. The conflict has the form
	 * {@code is_cons(w) == true, w != cons(sel1(w),...,seln(w))}.
	 *
	 * @param annot the argument of the :dt-constructor annotation. It has the form
	 *              {@code (= w (cons (sel1 w) ... (seln w)))}.
	 * @return The array of interpolants.
	 */
	private Term[] interpolateDTConstructor(Object[] annot) {
		final Term[] interpolants = new Term[mNumInterpolants];

		final ApplicationTerm diseqAtom = (ApplicationTerm) annot[0];
		final Term[] diseqParams = diseqAtom.getParameters();
		final LitInfo diseqInfo = mDisequalityInfos.get(new SymmetricPair<>(diseqParams[0], diseqParams[1]));

		// tester
		final Term dataTerm = diseqParams[0];
		final FunctionSymbol constructor = ((ApplicationTerm) diseqParams[1]).getFunction();
		final ApplicationTerm testerTerm = (ApplicationTerm) mTheory.term(SMTLIBConstants.IS,
				new String[] { constructor.getName() }, null, dataTerm);
		final LitInfo testerInfo = mEqualityInfos.get(new SymmetricPair<Term>(testerTerm, mTheory.mTrue));

		for (int color = 0; color < mNumInterpolants; color ++) {
			if (testerInfo.isAorShared(color) && diseqInfo.isAorShared(color)) {
				interpolants[color] = mTheory.mFalse;
			} else if (testerInfo.isBorShared(color) && diseqInfo.isBorShared(color)) {
				interpolants[color] = mTheory.mTrue;
			} else if (testerInfo.isALocal(color) && diseqInfo.isBLocal(color)) {
				interpolants[color] = testerTerm;
			} else if (testerInfo.isBLocal(color) && diseqInfo.isALocal(color)) {
				interpolants[color] = mTheory.term(SMTLIBConstants.NOT, testerTerm);
			} else {
				// none of the equalities can be mixed.
				throw new AssertionError();
			}
		}

		return interpolants;
	}

	/**
	 * Interpolate a datatype tester conflict. The conflict has the form
	 * {@code w == cons(v1,...,vn), is_cons(w) != true} or
	 * {@code w == cons(v1,...,vn), is_cons'(w) != false}. The equality is missing
	 * if it is implied by reflexivity.
	 *
	 * @param annot the argument of the :dt-tester annotation. It has the form
	 *              {@code (= is_cons(w) true/false) :cons cons(v1,...,vn)}.
	 * @return The array of interpolants.
	 */
	private Term[] interpolateDTTester(Object[] annot) {

		final ApplicationTerm consTerm = (ApplicationTerm) annot[2];
		final ApplicationTerm goaleqTerm = (ApplicationTerm) annot[0];
		final Term testerArg = ((ApplicationTerm) goaleqTerm.getParameters()[0]).getParameters()[0];

		final SymmetricPair<Term> diseqLit = mDisequalityInfos.keySet().iterator().next();
		final LitInfo diseqInfo = mDisequalityInfos.get(diseqLit);

		final Term[] interpolants = new Term[mNumInterpolants];

		// equality is missing because it is trivial
		if (mEqualityInfos.size() == 0) {
			for (int color = 0; color < mNumInterpolants; color++) {
				if (diseqInfo.isAorShared(color)) {
					interpolants[color] = mTheory.mFalse;
				} else {
					// can not be mixed as it is always (... != true/false)
					assert(diseqInfo.isBLocal(color));
					interpolants[color] = mTheory.mTrue;
				}
			}
			return interpolants;
		}
		assert (mEqualityInfos.size() == 1);

		final SymmetricPair<Term> eqLit = mEqualityInfos.keySet().iterator().next();
		final LitInfo eqInfo = mEqualityInfos.get(eqLit);


		for (int color = 0; color < mNumInterpolants; color++) {
			if (diseqInfo.isAorShared(color) && eqInfo.isAorShared(color)) {
				interpolants[color] = mTheory.mFalse;
			} else if (diseqInfo.isBorShared(color) && eqInfo.isBorShared(color)) {
				interpolants[color] = mTheory.mTrue;
			} else {
				final Term sharedTerm = eqInfo.isMixed(color) ? eqInfo.getMixedVar() : testerArg;
				if (diseqInfo.isALocal(color)) {
					interpolants[color] = mTheory.term("not", mTheory.term(SMTLIBConstants.IS,
							new String[] { consTerm.getFunction().getName() }, null, sharedTerm));
				} else {
					interpolants[color] = mTheory.term(SMTLIBConstants.IS,
							new String[] { consTerm.getFunction().getName() }, null, sharedTerm);
				}
			}
		}
		return interpolants;
	}

	/**
	 * Interpolate a datatype dt-cycle conflict. The lemma is annotated with a cycle
	 * {@code a1,b1,a2,b2,..,an} that shows that {@code a1} is equal to a
	 * constructor call on itself. The conflict must contain {@code ai == bi} (if it
	 * is not trivial) and {@code a(i+1)} is a child of {@code bi} in the sense that
	 * either {@code bi} is a term {@code cons(..,a(i+1),...)}, or that
	 * {@code a(i+1)} is a term {@code sel(bi)} and for the corresponding
	 * constructor {@code is_cons(bi) = true} occurs negated in the lemma.
	 *
	 * @param annot the argument of the :dt-cycle annotation. It has the form
	 *              {@code :cycle a1 b1 a2 b2 ... an} where a1 == an.
	 * @return The array of interpolants.
	 */
	private Term[] interpolateDTCycle(Object[] annot) {
		assert (annot[0] == ":cycle");
		mPath = (Term[]) annot[1];
		mLastColor = mNumInterpolants;
		mMaxColor = mNumInterpolants;
		mAllInA.set(0, mNumInterpolants);
		mStartSelectors = new String[(mPath.length - 1) / 2 * 3 + 1];
		mStartConstructors = new String[(mPath.length - 1) / 2 * 3 + 1];
		mStartTesters = new FunctionSymbol[(mPath.length - 1) / 2 * 3 + 1];
		mIsSelectRel =  false;

		traverseCycleLemma();
		collectCycleInterpolants();

		final Term[] interpolants = new Term[mNumInterpolants];
		for (int color = 0; color < mNumInterpolants; color++) {
			interpolants[color] = mTheory.and(mInterpolants[color].toArray(new Term[mInterpolants[color].size()]));
		}
		return interpolants;
	}

	/**
	 * Interpolate a datatype project conflict. The conflict has the form
	 * {@code w == cons(v1,...,vn), seli(w) != vi}. The equality is missing if it is
	 * implied by reflexivity.
	 *
	 * @param annot the argument of the :dt-project annotation. It has the form
	 *              {@code (= seli(w) vi) :cons cons(v1,...,vn)}.
	 */
	private Term[] interpolateDTProject(Object[] annot) {

		final ApplicationTerm goalEq = (ApplicationTerm) annot[0];
		final Term[] interpolants = new Term[mNumInterpolants];

		// equality is missing because it is trivial
		if (mEqualityInfos.size() == 0) {
			final LitInfo diseqInfo = mDisequalityInfos.values().iterator().next();
			for (int color = 0; color < mNumInterpolants; color++) {
				if (diseqInfo.isAorShared(color)) {
					interpolants[color] = mTheory.mFalse;
				} else if (diseqInfo.isBLocal(color)) {
					interpolants[color] = mTheory.mTrue;
				} else {
					// mixed case is possible only with quantifiers
					assert diseqInfo.isMixed(color);
					final Term sharedTerm = goalEq.getParameters()[1];
					interpolants[color] = mTheory.term(Interpolator.EQ, diseqInfo.getMixedVar(), sharedTerm);
				}
			}
			return interpolants;
		}
		assert (mEqualityInfos.size() == 1);
		if (mDisequalityInfos.size() == 0) {
			final LitInfo eqInfo = mDisequalityInfos.values().iterator().next();
			for (int color = 0; color < mNumInterpolants; color++) {
				if (eqInfo.isAorShared(color)) {
					interpolants[color] = mTheory.mFalse;
				} else if (eqInfo.isBLocal(color)) {
					interpolants[color] = mTheory.mTrue;
				} else {
					throw new AssertionError();
				}
			}
			return interpolants;
		}
		assert (mDisequalityInfos.size() == 1);

		final SymmetricPair<Term> diseqLit = mDisequalityInfos.keySet().iterator().next();
		final LitInfo diseqInfo = mDisequalityInfos.get(diseqLit);

		final SymmetricPair<Term> eqLit = mEqualityInfos.keySet().iterator().next();
		final LitInfo eqInfo = mEqualityInfos.get(eqLit);

		for (int color = 0; color < mNumInterpolants; color++) {
			if (eqInfo.isAorShared(color) && diseqInfo.isAorShared(color)) {
				interpolants[color] = mTheory.mFalse;
			} else if (eqInfo.isBorShared(color) && diseqInfo.isBorShared(color)) {
				interpolants[color] = mTheory.mTrue;
			} else {
				Term shared0Term, shared1Term;
				if (eqInfo.isMixed(color)) {
					final Term consSharedTerm = eqInfo.getMixedVar();
					final ApplicationTerm selectTerm = (ApplicationTerm) goalEq.getParameters()[0];
					final FunctionSymbol selectSym = selectTerm.getFunction();
					shared0Term = shared1Term = mTheory.term(selectSym, consSharedTerm);
				} else {
					shared0Term = goalEq.getParameters()[0];
					shared1Term = goalEq.getParameters()[1];
				}
				if (diseqInfo.isMixed(color)) {
					interpolants[color] = mTheory.term(Interpolator.EQ, diseqInfo.getMixedVar(), shared1Term);
				} else if (diseqInfo.isALocal(color)) {
					interpolants[color] = mTheory.term(SMTLIBConstants.NOT,
							mTheory.term(SMTLIBConstants.EQUALS, shared0Term, goalEq.getParameters()[1]));
				} else {
					interpolants[color] = mTheory.term(SMTLIBConstants.EQUALS, shared0Term, goalEq.getParameters()[1]);
				}
			}
		}
		return interpolants;
	}

	/**
	 * Interpolate a datatype cases conflict. The conflict has the form
	 * {@code ((_ is cons1) u1) == false, ... ((_ is consn) un) == false, u1 == u2,  ... u1 == un}.
	 * The u1 == uj equalities are missing if they are trivial.
	 *
	 * @param annot the argument of the :dt-cases annotation. It is a list of the
	 *              tester terms {@code ((_ is consi) ui)}.
	 * @return The array of interpolants.
	 */
	private Term[] interpolateDTCases(Object[] annot) {
		final Term[] interpolants = new Term[mNumInterpolants];

		final ApplicationTerm firstTerm = (ApplicationTerm) annot[0];
		final Term firstSymbol = firstTerm.getParameters()[0];
		final LitInfo firstTesterInfo = mEqualityInfos.get(new SymmetricPair<>(mTheory.mFalse, firstTerm));

		for (int color = 0; color < mNumInterpolants; color++) {
			final boolean summarizeA = firstTesterInfo.isBorShared(color);
			final ArrayList<Term> interpolantTerms = new ArrayList<>();
			for (int i = 1; i < annot.length; i++) {
				final Term term = (Term) annot[i];
				final Term symbol = ((ApplicationTerm) term).getParameters()[0];
				final LitInfo testerInfo = mEqualityInfos.get(new SymmetricPair<>(term, mTheory.mFalse));
				final LitInfo eqInfo = mEqualityInfos.get(new SymmetricPair<>(symbol, firstSymbol));
				final FunctionSymbol testerFunc = ((ApplicationTerm) term).getFunction();

				if (summarizeA ? testerInfo.isBorShared(color) : testerInfo.isAorShared(color)) {
					// only summarize the equality if it is the other color
					assert eqInfo == null || !eqInfo.isMixed(color);
					if (eqInfo != null && (summarizeA ? eqInfo.isALocal(color) : eqInfo.isBLocal(color))) {
						final Term eqTerm = mTheory.term(SMTLIBConstants.EQUALS, firstSymbol, symbol);
						interpolantTerms.add(summarizeA ? eqTerm : mTheory.term(SMTLIBConstants.NOT, eqTerm));
					}
				} else {
					// find shared term
					Term sharedTerm;
					if (eqInfo == null || (summarizeA ? eqInfo.isALocal(color) : eqInfo.isBLocal(color))) {
						sharedTerm = firstSymbol;
					} else if (eqInfo.isMixed(color)) {
						sharedTerm = eqInfo.getMixedVar();
					} else {
						sharedTerm = symbol;
					}
					final Term testerTerm = mTheory.term(testerFunc, sharedTerm);
					interpolantTerms.add(summarizeA ? mTheory.term(SMTLIBConstants.NOT, testerTerm) : testerTerm);
				}
			}
			final Term[] components = interpolantTerms.toArray(new Term[interpolantTerms.size()]);
			if (summarizeA) {
				interpolants[color] = mTheory.and(components);
			} else {
				interpolants[color] = mTheory.or(components);
			}
		}
		return interpolants;
	}

	// goes through the literals for a cycle lemma
	private void traverseCycleLemma() {
		for (int i = 0; i < mPath.length - 2; i += 2) {
			final Term left = mPath[i];
			final Term right = mPath[i+1];
			if (!left.equals(right)) {
				final LitInfo literalInfo = mEqualityInfos.get(new SymmetricPair<>(left, right));

				mAllInA.and(literalInfo.mInA);
				// close and open A-paths before the literal when switches happen
				closeAPaths(literalInfo, i /2);
				openAPaths(literalInfo, i / 2);
				// close and open A-paths in the middle of mixed literals
				closeAPathsOnMixedLiterals(literalInfo, i / 2);
				openAPathsOnMixedLiterals(literalInfo, i / 2);
			}

			final Term nextTerm = mPath[i+2];
			if (isConsParentOf(right, nextTerm)) {
				mIsSelectRel = false;
				// store
				addConsToAPath((ApplicationTerm) right, i / 2);
			} else {
				assert(isSelParentOf(right, nextTerm));
				mIsSelectRel = true;
				// store
				addSelToAPath(right, (ApplicationTerm) nextTerm, i / 2);
				// close and open A-paths after the literal where the tester occurrence forces a switch
				closeAPathsForTesters((ApplicationTerm) nextTerm, i / 2);
				openAPathsForTesters((ApplicationTerm) nextTerm, i / 2);
			}
		}
	}

	//
	private void collectCycleInterpolants() {
		for (int color = 0; color < mNumInterpolants; color++) {
			if (mAllInA.get(color)) {
				assert(mInterpolants[color].isEmpty());
				mInterpolants[color].add(mTheory.mFalse);
				continue;
			}
			// APath was closed at the beginning and needs to be conected to the start of the APath
			if (mHead[color] != null) {
				assert(mEnd[color] == null);
				if (mStart[color] == null) {
					mStart[color] = mPath[0];
					mStartIndices[color] = 0;
				}
				mEnd[color] = mHead[color];
				mEndIndices[color] = mHeadIndices[color];
				addCompletedAPath(color);
			}
			// APath was opend before but still needs to be closed
			else if (mStart[color] != null) {
				assert(mEnd[color] == null);
				// TODO:
				mEnd[color] = mPath[0];
				mEndIndices[color] = 0;
				addCompletedAPath(color);
			}
		}

	}

	// store the function symbol, and needed testers to later add to the interpolantion term
	private void addConsToAPath(final ApplicationTerm consTerm, int litIndex) {
		// store the correspondng selector and tester function
		final FunctionSymbol functionSymbol = consTerm.getFunction();
		assert(functionSymbol.isConstructor());
		mStartSelectors[litIndex * 3 + 1] = getSelector((ApplicationTerm) mPath[litIndex * 2 + 1], mPath[litIndex * 2 + 2]);
		final DataType dataType = (DataType) consTerm.getSort().getSortSymbol();
		mStartConstructors[litIndex * 3 + 1] = dataType.findConstructor(functionSymbol.getName()).getName();
	}

	//
	private void addSelToAPath(final Term parentTerm, final ApplicationTerm childTerm, int litIndex) {
		final FunctionSymbol functionSymbol = childTerm.getFunction();
		// store the selector and tester function
		assert(functionSymbol.isSelector());
		mStartSelectors[litIndex * 3 + 3] = functionSymbol.getName();
		// String testerFunction = mTestersFunctions.get(((ApplicationTerm) term).getParameters()[0]);
		final FunctionSymbol testerFunction = mTestersFunctions.get(parentTerm);
		mStartTesters[litIndex * 3 + 2] = testerFunction;
	}


	// closes the A Paths where the switch occured
	private void closeAPaths(LitInfo literalInfo, int litIndex) {
		int color = mLastColor;
		final int top = mNumInterpolants - 1;

		// increase the color to go up the Tree, while the occurrence is in B, and close the A-Paths for those partitions
		while (color <= top) {
			// stop on the partition that doesn't see a switch anymore
			if (literalInfo.isAorShared(color)) {
				break;
			}
			if (literalInfo.isMixed(color)) {
				break;
			}
			// switch from shared (open A path) to B
			if (literalInfo.isBLocal(color)) {
				if (mStart[color] != null) {
					if (mIsSelectRel) {
						mEnd[color] = mPath[litIndex * 2 - 1];
					} else {
						mEnd[color] = mPath[litIndex * 2];
					}
					mEndIndices[color] = litIndex * 3;
					addCompletedAPath(color);
				} else {
					if (mIsSelectRel) {
						mHead[color] = mPath[litIndex * 2 - 1];
					} else {
						mHead[color] = mPath[litIndex * 2];
					}
					mHeadIndices[color] = litIndex * 3;
				}
			}
			color = getParent(color);
			mLastColor = color;
		}
		if (color > mMaxColor) {
			mMaxColor = color;
		}
	}

	// opens the A Path where the switch occured
	// mLastColor has to be set correctly
	// TODO : use closeAPaths() first to set mLastColor correctly
	private void openAPaths(LitInfo literalInfo, int litIndex) {
		// TODO: check for mixed lits
		// assert(mLastColor == 0 || literalInfo.isAorShared(mLastColor));

		int color = mLastColor;
		color = getALocalChild(color, literalInfo);
		// decrease the color to go down the Tree, while the occurrence is in A, and open the A Paths for those partitions
		while (color >= 0) {
			if (mAllInA.get(color)) {
				mMaxColor = color;
				mLastColor = color;
			} else {
				// stop on the partition that doesn't see a switch anymore
				if (literalInfo.isBorShared(color)) {
					assert(false);
					break;
				}
				// switch from B to A
				if (literalInfo.isALocal(color)) {
					if (mIsSelectRel) {
						mStart[color] = mPath[litIndex * 2 - 1];
					} else {
						mStart[color] = mPath[litIndex * 2];
					}
					mStartIndices[color] = litIndex * 3;
				}
			}
			mLastColor = color;
			color = getALocalChild(color, literalInfo);
		}
	}

	private void closeAPathsOnMixedLiterals(LitInfo literalInfo, int litIndex) {
		int color = mLastColor;
		// move up the tree and close A-paths for partitions that need to see a switch
		while (color <= mNumInterpolants - 1) {
			// stop as soon as no closing is needed (path can stay in A)
			if (literalInfo.isAorShared(color)) {
				break;
			}
			if (literalInfo.isMixed(color)) {
				// close the A-Path
				mEnd[color] = literalInfo.getMixedVar();
				mEndIndices[color] = litIndex * 3 + 1;
				if (mStart[color] != null) {
					mEnd[color] = literalInfo.getMixedVar();
					mEndIndices[color] = litIndex * 3 + 1;
					addCompletedAPath(color);
				}
				else {
					mHead[color] = literalInfo.getMixedVar();
					mHeadIndices[color] = litIndex * 3 + 1;
				}
			}
			// go up the tree
			color = getParent(color);
			mLastColor = color;
		}
		if (color > mMaxColor) {
			mMaxColor = color;
		}
	}

	private void openAPathsOnMixedLiterals(LitInfo literalInfo, int litIndex) {
		int color = mLastColor;
		color = getMixedChild(color, literalInfo);
		while (color <= mNumInterpolants - 1 && color >= 0) {
			if (literalInfo.isBorShared(color)) {
				break;
			}
			if (literalInfo.isMixed(color) ) {
				mStart[color] = literalInfo.getMixedVar();
				mStartIndices[color] = litIndex * 3 + 1;
			}
			mLastColor = color;
			color = getMixedChild(color, literalInfo);
		}
	}

	//
	private void closeAPathsForTesters(ApplicationTerm selTerm, int litIndex) {
		// get the occurrence of the tester
		final Occurrence testerOcc = mTestersOccurrence.get(selTerm.getParameters()[0]);
		mAllInA.and(testerOcc.mInA);
		int color = mLastColor;
		// move up the tree and close A-paths for partitions that need to see a switch
		while (color <= mNumInterpolants - 1) {
			// stop as soon as no closing is needed (path can stay in A)
			if (testerOcc.isAorShared(color)) {
				break;
			}
			// testers can't be mixed
			assert(testerOcc.isBLocal(color));
			// close the A-Path
			if (mStart[color] != null) {
				mEnd[color] = selTerm.getParameters()[0];
				mEndIndices[color] = litIndex * 3 + 2;
				addCompletedAPath(color);
			} else {
				mHead[color] = selTerm.getParameters()[0];
				mHeadIndices[color] = litIndex * 3 + 2;
			}
			// go up the tree
			color = getParent(color);
			mLastColor = color;
		}
		if (color > mMaxColor) {
			mMaxColor = color;
		}
	}

	//
	private void openAPathsForTesters(ApplicationTerm selTerm, int litIndex) {
		final Occurrence testerOcc = mTestersOccurrence.get(selTerm.getParameters()[0]);
		int color = mLastColor;
		color = getALocalChild(color, testerOcc);
		// decrease the color to go down the Tree, while the occurrence is in A, and open the A Paths for those partitions
		while (color >= 0) {
			if (mAllInA.get(color)) {
				mMaxColor = color;
				mLastColor = color;
			} else {
				// stop on the partition that doesn't see a switch anymore
				if (testerOcc.isBorShared(color)) {
					break;
				}
				// switch from B to A
				if (testerOcc.isALocal(color)) {
					// mStart[color] = mPath[litIndex * 2];
					mStart[color] = selTerm.getParameters()[0];
					mStartIndices[color] = litIndex * 3 + 2;
				}
			}
			mLastColor = color;
			color = getALocalChild(color, testerOcc);
		}
	}

	// adds the completed A path to the interpolant of the given interpolant (color)
	private void addCompletedAPath(int color) {
		Term left = mStart[color];
		final Term right = mEnd[color];
		for (int i = mStartIndices[color]; i != mEndIndices[color]; i = (i + 1) % ((mPath.length - 1) / 2 * 3 + 1)) {
			if (mStartTesters[i] != null) {
				// String s = mStartTesters[i];
				mInterpolants[color].add(mTheory.term(mStartTesters[i], left));
			}
			if (mStartConstructors[i] != null) {
				mInterpolants[color].add(mTheory.term(SMTLIBConstants.IS, new String[] { mStartConstructors[i] },
						null, left));
			}
			if (mStartSelectors[i] != null) {
				left = mTheory.term(mStartSelectors[i], left);
			}
		}
		mInterpolants[color].add(mTheory.term("=", left, right));

		mEndIndices[color] = -1;
		mStartIndices[color] = -1;
		mEnd[color] = null;
		mStart[color] = null;
	}


	// returns true if the first term is parent of the second term
	private boolean isParentTermOf(Term parent, Term child) {
		return (isConsParentOf(parent, child) || isSelParentOf(parent, child));
	}
	// returns true if the second term is a selctor application on the first term
	private boolean isSelParentOf(Term parent, Term child) {
		if (!(child instanceof ApplicationTerm)) {
			return false;
		}
		if (((ApplicationTerm) child).getFunction().isSelector()) {
			if (((ApplicationTerm) child).getParameters()[0] == parent) {
				return true;
			}
		}
		return false;
	}
	// returns true if the first term is a constructor application, that includs the second term
	private boolean isConsParentOf(Term parent, Term child) {
		if (!(parent instanceof ApplicationTerm)) {
			return false;
		}
		if (((ApplicationTerm) parent).getFunction().isConstructor()) {
			for (final Term term : ((ApplicationTerm) parent).getParameters()) {
				if (child == term) {
					return true;
				}
			}
		}
		return false;
	}


	/*
	private Term getRelevantSubTerm(ApplicationTerm applicationTerm, Term term) {
		FunctionSymbol func = applicationTerm.getFunction();
		if (func.isSelector() ) {
			return applicationTerm.getParameters()[0];
		} else if (func.isConstructor()){
			for (Term t : applicationTerm.getParameters()) {
				if ( t == term) {
					return t;
				}
			}
		}
		return null;
	}
	 */

	// returns the selector that would give the "childTerm" when applied to the "consTerm"
	private String getSelector(ApplicationTerm consTerm, Term childTerm) {
		final FunctionSymbol constructorSymbol = consTerm.getFunction();
		assert(constructorSymbol.getReturnSort().getSortSymbol().isDatatype());
		final DataType datatype = (DataType) consTerm.getSort().getSortSymbol();
		final Constructor cons = datatype.findConstructor(constructorSymbol.getName());
		final String[] s = cons.getSelectors();
		final Term[] terms = consTerm.getParameters();
		for (int i = 0; i < terms.length; i++) {
			if (childTerm.equals(terms[i])) {
				return s[i];
			}
		}
		throw new AssertionError("child term not found in constructors");
	}

	private String getSelectorForPair(ApplicationTerm cons1Term, ApplicationTerm cons2Term, Term[] childTerms) {
		final DataType datatype = (DataType) cons1Term.getSort().getSortSymbol();
		final Constructor cons = datatype.findConstructor(cons1Term.getFunction().getName());
		final String[] s = cons.getSelectors();
		final Term[] terms1 = cons1Term.getParameters();
		final Term[] terms2 = cons2Term.getParameters();
		for (int i = 0; i < terms1.length; i++) {
			if (childTerms[0] == terms1[i] && childTerms[1] == terms2[i]) {
				return s[i];
			}
		}
		throw new AssertionError("child term not found in constructors");
	}

	// returns the parent partition for the given partition (color)
	private int getParent(int color) {
		int parent = color + 1;
		while (mInterpolator.mStartOfSubtrees[parent] > color) {
			parent++;
		}
		return parent;
	}

	// returns for the given occurrence an A-local child partition of the given partition (color)
	// returns -1 if there is none
	private int getALocalChild(int color, Occurrence occ) {
		int child = color - 1;
		while (child >= mInterpolator.mStartOfSubtrees[color]) {
			if (occ.isALocal(child)) {
				return child;
			}
			child = mInterpolator.mStartOfSubtrees[child] - 1;
		}
		return -1;
	}

	// returns for the given occurrence a child partition of the given partition (color) where the occurence is mixed
	// returns -1 if there is none
	private int getMixedChild(int color, Occurrence occ) {
		int child = color - 1;
		while (child >= mInterpolator.mStartOfSubtrees[color]) {
			if (occ.isMixed(child)) {
				return child;
			}
			child = mInterpolator.mStartOfSubtrees[child] - 1;
		}
		return -1;
	}
}
// TODO: getReturnSort on functionsymbol as for dataType???