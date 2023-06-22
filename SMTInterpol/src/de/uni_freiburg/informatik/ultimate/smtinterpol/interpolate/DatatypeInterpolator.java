// TODO: copyright

package de.uni_freiburg.informatik.ultimate.smtinterpol.interpolate;

import java.util.BitSet;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.Map;
import java.util.Set;
import java.util.Vector;

import de.uni_freiburg.informatik.ultimate.logic.DataType;
import de.uni_freiburg.informatik.ultimate.logic.DataType.Constructor;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.FormulaUnLet;
import de.uni_freiburg.informatik.ultimate.logic.FunctionSymbol;
import de.uni_freiburg.informatik.ultimate.logic.SMTLIBConstants;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.logic.Theory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.interpolate.Interpolator.LitInfo;
import de.uni_freiburg.informatik.ultimate.smtinterpol.interpolate.Interpolator.Occurrence;
import de.uni_freiburg.informatik.ultimate.smtinterpol.option.SMTInterpolConstants;
import de.uni_freiburg.informatik.ultimate.smtinterpol.util.SymmetricPair;

/**
 * The interpolator for the Theory of datatypes.
 */
public class DatatypeInterpolator {
	
	private final Interpolator mInterpolator;
	private final Theory mTheory;
	private final int mNumInterpolants;
	private InterpolatorClauseInfo mClauseInfo;
	// a set for each Interpolant, to be filled with the literals of the interpolant
	private Set<Term>[] mInterpolants;
	// the equalities of the lemma
	private HashMap<SymmetricPair<Term>, LitInfo> mEqualityLiterals;
	// the disequality of the lemma
	private HashMap<SymmetricPair<Term>, LitInfo> mDisequalityLiterals;
	// the testers as a map from their inner Term to their Occurrence
	private HashMap<Term, LitInfo> mTestersOccurrence;
	// the testers as a map from their inner Term to their function name
	private HashMap<Term, FunctionSymbol> mTestersFunctions;
	// the ordered literals of the lemma
	private Term[] mPath;
	private Term mGoalEq;
	
	// the LitInfo for the literal currently working on
	private LitInfo mLitInfo;
	
	// the partitions for which every literal so far was shared
	BitSet mAllInA;
	
	private int mMaxColor;
	private int mHeadColor;
	private int mLastColor;
	
	// for each partition, the boundery terms thats start the A Path
	private Term[] mStart;
	// for each partition, the boundery terms thats end the A Path
	private Term[] mEnd;
	//
	private Term[] mHead;
	// for each partition, the indices of the literals where the current A-path started (-1 if there is none for that partition)
	private int[] mStartIndices;
	// for each partition, the indices of the literals where the A-path was closed but not opend (-1 if there is none for this partition)
	private int[] mEndIndices;
	//
	private int[] mHeadIndices;
	
	// array to store select functions later applied to the start of the a path
	private String[] mStartSelectors;
	// array to store select functions later applied to the end of the a path
	// private String[] mEndSelectors;
	// array to store constructor names for testers
	private String[] mStartConstructors;
	// array to store constructor names for testers
	// private String[] mEndConstructors;
	// array to store tester functions
	private FunctionSymbol[] mStartTesters;
	// array to store tester functions
	// private String[] mEndTesters;

	
	
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
	
	// computes Interpolants and returns them as an array
	public Term[] computeDatatypeInterpolants(final InterpolatorClauseInfo clauseInfo) {
		mClauseInfo = clauseInfo;
		// mLemmaAnnotation = clauseInfo.getLemmaAnnotation();
		mEqualityLiterals = new HashMap<>();
		mDisequalityLiterals = new HashMap<>();
		mTestersOccurrence = new HashMap<>();
		mTestersFunctions = new HashMap<>();
		for (final Term literal : mClauseInfo.getLiterals()) {
			final Term atom = mInterpolator.getAtom(literal);
			final InterpolatorAtomInfo atomTermInfo = mInterpolator.getAtomTermInfo(atom);
			final ApplicationTerm eqTerm = atomTermInfo.getEquality();
			final LitInfo atomOccurenceInfo = mInterpolator.getAtomOccurenceInfo(atom);
			Term left = eqTerm.getParameters()[0];
			Term right = eqTerm.getParameters()[1];
			if (left instanceof ApplicationTerm && ((ApplicationTerm) left).getFunction().getName().equals(SMTLIBConstants.IS)) {
				mTestersFunctions.put(((ApplicationTerm) left).getParameters()[0], ((ApplicationTerm) left).getFunction());
				mTestersOccurrence.put(((ApplicationTerm) left).getParameters()[0], atomOccurenceInfo);
			} else if (right instanceof ApplicationTerm && ((ApplicationTerm) left).getFunction().getName().equals(SMTLIBConstants.IS)) {
				mTestersFunctions.put(((ApplicationTerm) right).getParameters()[0], ((ApplicationTerm) right).getFunction());
				mTestersOccurrence.put(((ApplicationTerm) right).getParameters()[0], atomOccurenceInfo);
			}
			if (atom != literal) {
				mEqualityLiterals.put(new SymmetricPair<>(left, right), atomOccurenceInfo);			
			} else {
				mDisequalityLiterals.put(new SymmetricPair<>(left, right), atomOccurenceInfo);			
			}
			
		}
		Object[] obj = ((Object[]) clauseInfo.getLemmaAnnotation());
		// assert(obj[0] == ":cycle");
		
		switch (clauseInfo.getLemmaType()) {
		case ":dt-project":
			mGoalEq = (Term) obj[0];
			return interpolateDTProject();
		case ":dt-tester":
			mGoalEq = (Term) obj[0];
			return interpolateDTTester();
		case ":dt-constructor":
			mGoalEq = (Term) obj[0];
			return interpolateDTConstructor();
		case ":dt-injective":
			mPath = new Term[2];
			mPath[0] = (Term) obj[2];
			mPath[1] = (Term) obj[3];
			return interpolateDTInjective();
		case ":dt-disjoint":
			mPath = new Term[2];
			mPath[0] = (Term) obj[1];
			mPath[1] = (Term) obj[2];
			return interpolateDTDisjoint();
		case ":dt-unique":
			mPath = new Term[2];
			mPath[0] = (Term) obj[0];
			mPath[1] = (Term) obj[1];
			// mGoalEq = (Term) obj[0];
			return interpolateDTUnique();
		case ":dt-cases":
			mPath = new Term[obj.length];
			int i = 0;
			for (Object term : obj) {
				mPath[i] = (Term) term;
				i += 1;
			}
			// mPath = (Term[]) clauseInfo.getLemmaAnnotation();
			return interpolateDTCases();
		case ":dt-cycle":
			mPath = (Term[]) obj[1];
			assert(obj[0] == ":cycle");
			return interpolateDTCycle();
		default:
			throw new UnsupportedOperationException("lemma unknown in datatype interpolator");
		}
	}
	
	private Term[] interpolateDTUnique() {
		
		final ApplicationTerm firstTester = (ApplicationTerm) mPath[0];
		final Term firstSymbol = firstTester.getParameters()[0];
		LitInfo firstTesterInfo = mEqualityLiterals.get(new SymmetricPair<>(mTheory.mTrue, firstTester));
		final ApplicationTerm secondTester = (ApplicationTerm) mPath[1];
		final Term secondSymbol = secondTester.getParameters()[0];
		LitInfo secondTesterInfo = mEqualityLiterals.get(new SymmetricPair<>(mTheory.mTrue, secondTester));
		for (int color = 0; color < mNumInterpolants; color++) {
			if (firstSymbol.equals(secondSymbol)) {
				if (firstTesterInfo.isALocal(color)) {
					// Term build = mTheory.term(firstTester.getFunction(), firstSymbol);
					Term build = mTheory.term("=", firstTester, mTheory.mTrue);
					mInterpolants[color].add(build);
				} else if (secondTesterInfo.isALocal(color)) {
					// Term build = mTheory.term(secondTester.getFunction(), secondSymbol);
					Term build = mTheory.term("=", secondTester, mTheory.mTrue);
					mInterpolants[color].add(build);
				}
			}
		}
		// TODO: missing... check git
		
		Term[] interpolants = new Term[mNumInterpolants];
		for (int color = 0; color < mNumInterpolants; color++) {
			interpolants[color] = mTheory.and(mInterpolants[color].toArray(new Term[mInterpolants[color].size()]));
		}
		
		return interpolants;
	}

	private Term[] interpolateDTDisjoint() {
		Term[] interpolants = new Term[mNumInterpolants];
		
		SymmetricPair<Term> eqLit = mEqualityLiterals.keySet().iterator().next();
		LitInfo eqInfo = mEqualityLiterals.get(eqLit);
		
		for (int color = 0; color < mNumInterpolants; color++) {
			if (eqInfo.isAorShared(color)) {
				interpolants[color] = mTheory.mFalse;
			}
			else if (eqInfo.isBLocal(color)) {
				interpolants[color] = mTheory.mTrue;
			} else {
				assert(eqInfo.isMixed(color));
				Occurrence lhsOcc = eqInfo.getLhsOccur();
				if(lhsOcc.isALocal(color)) {
					interpolants[color] = mTheory.term(SMTLIBConstants.IS, new String[] { getConstructorName(((ApplicationTerm) mPath[0]).getFunction())}, null, eqInfo.getMixedVar());
				} else {
					interpolants[color] = mTheory.term(SMTLIBConstants.IS, new String[] { getConstructorName(((ApplicationTerm) mPath[1]).getFunction())}, null, eqInfo.getMixedVar());					
				}
			}
		}
		return interpolants;
	}

	private Term[] interpolateDTInjective() {
		Term[] interpolants = new Term[mNumInterpolants];
		
		SymmetricPair<Term> eqLit = mEqualityLiterals.keySet().iterator().next();
		LitInfo eqInfo = mEqualityLiterals.get(eqLit);		
		SymmetricPair<Term> diseqLit = mDisequalityLiterals.keySet().iterator().next();
		LitInfo diseqInfo = mDisequalityLiterals.get(diseqLit);
		
		for (int color = 0; color < mNumInterpolants; color++) {
			if (eqInfo.isALocal(color)) {
				if (diseqInfo.isAorShared(color)) {
					interpolants[color] = mTheory.mFalse;
				} else {
					assert(diseqInfo.isBLocal(color));
					interpolants[color] = mTheory.term("=", diseqLit.getFirst(), diseqLit.getSecond());
				}
			}
			else if (eqInfo.isBLocal(color)) {
				if (diseqInfo.isBorShared(color)) {
					interpolants[color] = mTheory.mTrue;
				} else {
					assert(diseqInfo.isALocal(color));
					Term build = mTheory.term("=", diseqLit.getFirst(), diseqLit.getSecond());
					interpolants[color] = mTheory.term("not", build);
				}
			}
			// equality literal is shared
			else if (eqInfo.isAorShared(color)) {
				if (diseqInfo.isBorShared(color)) {
					interpolants[color] = mTheory.mTrue;
				} else {
					assert(diseqInfo.isALocal(color));
					interpolants[color] = mTheory.mFalse;
				}
			}
			else {
				assert(eqInfo.isMixed(color));
				// get selector function
				Term child = null;
				boolean switchTerms = false;
				if (isParentTermOf(mPath[0], diseqLit.getFirst())) {
					child = diseqLit.getFirst();
				} else {
					child = diseqLit.getSecond();
					switchTerms = true;
				}
				// TODO: assume mPath is an applicationTerm, check it!!!
				String selFunc = getSelector((ApplicationTerm) mPath[0], child);

				// both literals are mixed
				if (diseqInfo.isMixed(color)) {
					Term build = mTheory.term(selFunc, eqInfo.getMixedVar());
					interpolants[color] = mTheory.term(Interpolator.EQ, diseqInfo.getMixedVar(), build);
					continue;
				}
				Occurrence lhsOcc = eqInfo.getLhsOccur();
				if (lhsOcc.isBLocal(color)) {
					switchTerms = !switchTerms;
				}
				if (diseqInfo.isAorShared(color)) {
					Term selTerm = switchTerms ? diseqLit.getSecond() : diseqLit.getFirst();
					Term build = mTheory.term(selFunc, eqInfo.getMixedVar());
					interpolants[color] = mTheory.term("not", mTheory.term("=", build, selTerm));
					// if ()
				}
				else {
					assert(diseqInfo.isBLocal(color));
					Term selTerm = switchTerms ? diseqLit.getFirst() : diseqLit.getSecond();
					Term build = mTheory.term(selFunc, eqInfo.getMixedVar());
					interpolants[color] = mTheory.term("=", build, selTerm);
				}
			}
		}
		
		return interpolants;
	}

	private Term[] interpolateDTConstructor() {
		Term[] interpolants = new Term[mNumInterpolants];
		
		SymmetricPair<Term> eqLit = mEqualityLiterals.keySet().iterator().next();
		LitInfo eqInfo = mEqualityLiterals.get(eqLit);		
		SymmetricPair<Term> diseqLit = mDisequalityLiterals.keySet().iterator().next();
		LitInfo diseqInfo = mDisequalityLiterals.get(diseqLit);
		
		for (int color = 0; color < mNumInterpolants; color ++) {
			if (diseqInfo.isBLocal(color)) {
				if (eqInfo.isALocal(color)) {
					interpolants[color] = mTheory.term("=", eqLit.getFirst(), eqLit.getSecond());
				} else {
					interpolants[color] = mTheory.mTrue;
				}
			}
			else if (diseqInfo.isALocal(color)) {
				if (eqInfo.isBLocal(color)) {
					interpolants[color] = mTheory.term("not", mTheory.term("=", diseqLit.getFirst(), diseqLit.getSecond()));
				} else {
					interpolants[color] = mTheory.mTrue;
				}
			} else {
				if (eqInfo.isBLocal(color)) {
					interpolants[color] = mTheory.mTrue;
				} else {
					interpolants[color] = mTheory.mFalse;
				}
			}
		}
		
		return interpolants;
	}

	private Term[] interpolateDTTester() {
		
		Term[] interpolants = new Term[mNumInterpolants];
		
		SymmetricPair<Term> diseqLit = mDisequalityLiterals.keySet().iterator().next();
		LitInfo diseqInfo = mDisequalityLiterals.get(diseqLit);
		
		// equality is missing because it is trivial
		if (mEqualityLiterals.size() == 0) {
			for (int color = 0; color < mNumInterpolants; color++) {
				if (diseqInfo.isAorShared(color)) {
					interpolants[color] = mTheory.mFalse;
				}
				else {
					// can not be mixed as it is always (... != true/false)
					assert(diseqInfo.isBLocal(color));
					interpolants[color] = mTheory.mTrue;
				}
			}
			return interpolants;
		}
		assert(mEqualityLiterals.size() == 1);
		
		SymmetricPair<Term> eqLit = mEqualityLiterals.keySet().iterator().next();
		LitInfo eqInfo = mEqualityLiterals.get(eqLit);
		
		for (int color = 0; color < mNumInterpolants; color++) {
			if (eqInfo.isALocal(color)) {
				if (diseqInfo.isAorShared(color)) {
					interpolants[color] = mTheory.mFalse;
				} else {
					// can not be mixed as it is always (... != true/false)
					assert(diseqInfo.isBLocal(color));
					// can be used as shared
					interpolants[color] = mTheory.term("=", diseqLit.getFirst(), diseqLit.getSecond());
				}
			}
			else if (eqInfo.isBLocal(color)) {
				if (diseqInfo.isBorShared(color)) {
					interpolants[color] = mTheory.mTrue;
				}
				else {
					// can not be mixed as it is always (... != true/false)
					assert(diseqInfo.isALocal(color));
					// can be used as shared
					interpolants[color] = mTheory.term("=", diseqLit.getFirst(), diseqLit.getSecond());
				}
			} else {
				assert(eqInfo.isMixed(color));
				if (diseqInfo.isALocal(color)) {
					interpolants[color] = mTheory.not(mTheory.term("=", eqInfo.getMixedVar(), ((ApplicationTerm) mGoalEq).getParameters()[1]));
				}
				else {
					assert(diseqInfo.isBLocal(color));
					
					Term constructor = null;
					if (eqLit.getFirst() instanceof ApplicationTerm) {
						if (((ApplicationTerm) eqLit.getFirst()).getFunction().isConstructor()) {
							constructor = eqLit.getFirst();
						}
						else {
							constructor = eqLit.getSecond();
						}
					}
					else {
						constructor = eqLit.getSecond();
					}
					interpolants[color] = mTheory.term(SMTLIBConstants.IS, new String[] { getConstructorName(((ApplicationTerm) constructor).getFunction())}, null, eqInfo.getMixedVar());
				}
			}
		}
		
		
		return interpolants;
	}

	private Term[] interpolateDTCycle() {
		mLastColor = mNumInterpolants - 1;
		mMaxColor = mNumInterpolants - 1;
		mHeadColor = mNumInterpolants - 1;
		mAllInA.set(0, mNumInterpolants);
		mStartSelectors = new String[(mPath.length - 1) / 2 * 3];
		// mEndSelectors = new String[mPath.length];
		mStartConstructors = new String[(mPath.length - 1) / 2 * 3];
		// mEndConstructors = new String[mPath.length];
		mStartTesters = new FunctionSymbol[(mPath.length - 1) / 2 * 3];
		// mEndTesters = new String[mPath.length];
		
		traverseLemma();
		
		
		Term[] interpolants = new Term[mNumInterpolants];
		for (int color = 0; color < mNumInterpolants; color++) {
			interpolants[color] = mTheory.and(mInterpolants[color].toArray(new Term[mInterpolants[color].size()]));
		}
		return interpolants;
	}
	
	// interpolates the Lemma DT_Project
	private Term[] interpolateDTProject() {
		
		Term[] interpolants = new Term[mNumInterpolants];
		
		SymmetricPair<Term> diseqLit = mDisequalityLiterals.keySet().iterator().next();
		LitInfo diseqInfo = mDisequalityLiterals.get(diseqLit);
		
		// equality is missing because it is trivial
		if (mEqualityLiterals.size() == 0) {
			for (int color = 0; color < mNumInterpolants; color++) {
				if (diseqInfo.isAorShared(color)) {
					interpolants[color] = mTheory.mFalse;
				}
				else {
					assert(diseqInfo.isBLocal(color));
					interpolants[color] = mTheory.mTrue;
				}
			}
			return interpolants;
		}
		assert(mEqualityLiterals.size() == 1);
		
		SymmetricPair<Term> eqLit = mEqualityLiterals.keySet().iterator().next();
		LitInfo eqInfo = mEqualityLiterals.get(eqLit);
		
		for (int color = 0; color < mNumInterpolants; color++) {
			// equality is in A
			if (eqInfo.isALocal(color)) {
				if (diseqInfo.isAorShared(color)) {
					interpolants[color] = mTheory.mFalse;
				}
				else if (diseqInfo.isBLocal(color)) {
					interpolants[color] = mTheory.term("=", diseqLit.getFirst(), diseqLit.getSecond());
				}
				assert(!diseqInfo.isMixed(color));
			}
			// equality is in B
			else if (eqInfo.isBLocal(color)) {
				if (diseqInfo.isBorShared(color)) {
					interpolants[color] = mTheory.mTrue;
				}
				else if (diseqInfo.isALocal(color)) {
					interpolants[color] = mTheory.term("not", mTheory.term("=", diseqLit.getFirst(), diseqLit.getSecond()));
				}
				assert(!diseqInfo.isMixed(color));
			}
			// equality is shared
			else if (eqInfo.isAorShared(color)) {
				if (diseqInfo.isAorShared(color)) {
					interpolants[color] = mTheory.mFalse;
				}
				else if (diseqInfo.isBLocal(color)) {
					interpolants[color] = mTheory.mTrue;
				}
				assert(!diseqInfo.isMixed(color));
			}
			// equality is mixed
			else if (eqInfo.isMixed(color)) {
				if (diseqInfo.isMixed(color)) {
					// TODO: 
					// ApplicationTerm goaleq = (ApplicationTerm) mLemmaAnnotation[0];
					Term selTerm = mTheory.term(((ApplicationTerm) ((ApplicationTerm) mGoalEq).getParameters()[0]).getFunction(), eqInfo.getMixedVar());
					interpolants[color] = mTheory.term(Interpolator.EQ, diseqInfo.getMixedVar(), selTerm);
				}
				else if (diseqInfo.isALocal(color)) {
					Term selTerm = mTheory.term(((ApplicationTerm) ((ApplicationTerm) mGoalEq).getParameters()[0]).getFunction(), eqInfo.getMixedVar());
					interpolants[color] = mTheory.term("=", selTerm, ((ApplicationTerm) mGoalEq).getParameters()[1]);
							// ((ApplicationTerm) diseqLit.getFirst()).getFunction().isSelector()
							// ? mTheory.term("=", eqInfo.getMixedVar(), diseqLit.getSecond())
							// : mTheory.term("=", eqInfo.getMixedVar(), diseqLit.getSecond());
					
				}
				else if (diseqInfo.isBLocal(color)) {
					if (isParentTermOf(eqLit.getFirst(), ((ApplicationTerm) mGoalEq).getParameters()[0])) {
						interpolants[color] = mTheory.term(SMTLIBConstants.IS, new String[] { getConstructorName(((ApplicationTerm) eqLit.getFirst()).getFunction())},
								null, eqInfo.getMixedVar());
					} else if (isParentTermOf(eqLit.getSecond(),  ((ApplicationTerm) mGoalEq).getParameters()[0])) {
						interpolants[color] = mTheory.term(SMTLIBConstants.IS, new String[] { getConstructorName(((ApplicationTerm) eqLit.getSecond()).getFunction())},
								null, eqInfo.getMixedVar());
					}
					else {
						assert(false);
					}
				}
			}
		}
		return interpolants;
	}
	
	public Term[] interpolateDTCases() {
		
		Term[] interpolants = new Term[mNumInterpolants];
		
		final ApplicationTerm firstTerm = (ApplicationTerm) mPath[0];
		final Term firstSymbol = firstTerm.getParameters()[0];
		LitInfo firstTesterInfo = mEqualityLiterals.get(new SymmetricPair<>(mTheory.mFalse, firstSymbol));
		// TODO: missing: if (firstTesterInfo.isALocal()) and else part
		// option 1: as Alocal but negate at the end
		// option 2: use an other tester as baseline
		for (int i = 1; i < mPath.length; i++) {
			Term term = mPath[i];
			Term symbol = ((ApplicationTerm) term).getParameters()[0];
			LitInfo testerInfo = mEqualityLiterals.get(new SymmetricPair<>(term, mTheory.mFalse));
			LitInfo eqInfo = mEqualityLiterals.get(new SymmetricPair<>(symbol, firstSymbol));
			FunctionSymbol funcSymbol = ((ApplicationTerm) term).getFunction();
			
			for (int color = 0; color < mNumInterpolants; color++) {
				if (testerInfo.isALocal(color)) {
					if (eqInfo.isAorShared(color)) {
						Term build = mTheory.term(funcSymbol, firstSymbol);
						build = mTheory.term("=", build, mTheory.mFalse);
						mInterpolants[color].add(build);
					} else if (eqInfo.isBLocal(color)) {
						// Term build = mTheory.term(fs, term);
						Term build = mTheory.term("=", term, mTheory.mFalse);
						mInterpolants[color].add(build);
					} else if (eqInfo.isMixed(color)) {
						Term build = mTheory.term(funcSymbol, eqInfo.getMixedVar());
						build = mTheory.term("=", build, mTheory.mFalse);
						mInterpolants[color].add(build);
					}
				} else {
					assert(testerInfo.isBLocal(color));
					if (eqInfo.isALocal(color) && !symbol.equals(firstSymbol)) {
						Term build = mTheory.term("=", symbol, firstSymbol);
						mInterpolants[color].add(build);
						continue;
					}
					assert(eqInfo.isBorShared(color));
				}
			}
			
		}
		
		for (int color = 0; color < mNumInterpolants; color++) {
			interpolants[color] = mTheory.and(mInterpolants[color].toArray(new Term[mInterpolants[color].size()]));
		}
		
		return interpolants;
	}
	
	
	private void traverseLemma() {
		for (int i = 0; i < mPath.length - 2; i += 2) {
			Term left = mPath[i];
			Term right = mPath[i+1];
			if (!left.equals(right)) {
				LitInfo literalInfo = mEqualityLiterals.get(new SymmetricPair<>(left, right));
				
				// TODO : lastcolor / maxcolor
				// TODO: check if mInA is correct / get Occ
				mAllInA.and(literalInfo.mInA);
				// close and open A-paths before the literal when switches happen
				closeAPaths(literalInfo, i /2);
				openAPaths(literalInfo, i / 2);
				// close and open A-paths in the middle of mixed literals
				closeAPathsOnMixedLiterals(literalInfo, i / 2);
				openAPathsOnMixedLiterals(literalInfo, i / 2);
			}
			
			Term nextTerm = mPath[i+2];
			if (isConsParentOf(right, nextTerm)) {
				// store
				addConsToAPath((ApplicationTerm) right, i / 2);
			}
			else {
				assert(isSelParentOf(right, nextTerm));
				// store 
				addSelToAPath((ApplicationTerm) nextTerm, i / 2);
				// close and open A-paths after the literal where the tester occurrence forces a switch
				closeAPathsForTesters((ApplicationTerm) nextTerm, i / 2);
				openAPathsForTesters((ApplicationTerm) nextTerm, i / 2);
			}
			
		}
		/*
		if (!mAllInA.isEmpty()) {
			// TODO: set interpolants to false / true
		} 
		*/
		for (int color = 0; color < mNumInterpolants; color++) {
			if (mAllInA.get(color)) {
				assert(mInterpolants[color].isEmpty());
				mInterpolants[color].add(mTheory.mFalse);
			}
			
			
			/* // int color = mLastColor;
			while (color <= mNumInterpolants + 1) {
				if (mInterpolator.mStartOfSubtrees[mHeadColor] == mInterpolator.mStartOfSubtrees[color]) {
					break;
				}
				mEnd[color] = mPath[-1];
				color = getParent(color);
			}
			// TODO: build occ
			Occurrence occ = mInterpolator.new Occurrence();
			while (color > mHeadColor) {
				mStart[color] = mPath[-1];
				color = getALocalChild(color, occ);
			}
			*/
			
			// APath was closed at the beginning and needs to be conected to the start of the APath
			if (mHead[color] != null) {
				assert(mEnd[color] == null);
				if (mStart[color] != null) {
					mEnd[color] = mHead[color];
					mEndIndices[color] = mHeadIndices[color];
				}
				else {
					// TODO:
					mStart[color] = mPath[0];
					mStartIndices[color] = 0;
					mEnd[color] = mHead[color];
					mEndIndices[color] = mHeadIndices[color];
				}
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
		FunctionSymbol functionSymbol = consTerm.getFunction();
		assert(functionSymbol.isConstructor());
		mStartSelectors[litIndex * 3 + 2] = getSelector((ApplicationTerm) mPath[litIndex * 2 + 1], mPath[litIndex * 2 + 2]);
		DataType dataType = (DataType) consTerm.getSort().getSortSymbol();
		mStartConstructors[litIndex * 3 + 2] = dataType.findConstructor(functionSymbol.getName()).getName();
	}
	
	// 
	private void addSelToAPath(final ApplicationTerm term, int litIndex) {
		FunctionSymbol functionSymbol = term.getFunction();
		// store the selector and tester function
		assert(functionSymbol.isSelector());
		mStartSelectors[litIndex * 3 + 2] = functionSymbol.getName();
		// String testerFunction = mTestersFunctions.get(((ApplicationTerm) term).getParameters()[0]);
		FunctionSymbol testerFunction = mTestersFunctions.get(((ApplicationTerm) term).getFunction());
		mStartTesters[litIndex * 3 + 2] = testerFunction;
	}

	
	// closes the A Paths where the switch occured 
	private void closeAPaths(LitInfo literalInfo, int litIndex) {
		int color = mLastColor;
		int top = mNumInterpolants - 1;
		
		// increase the color to go up the Tree, while the occurrence is in B, and close the A-Paths for those partitions
		while (color <= top) {
			// stop on the partition that doesn't see a switch anymore
			if (literalInfo.isAorShared(color)) {
				break;
			}
			if (literalInfo.isMixed(color)) {
				break;
			}
			// TODO: check if correct to clear
			mAllInA.clear();
			// switch from shared (open A path) to B
			if (literalInfo.isBLocal(color)) {
				if (mStart[color] != null) {
					mEnd[color] = mPath[litIndex * 2];
					mEndIndices[color] = litIndex * 3;
					addCompletedAPath(color);
				} else {
					mHead[color] = mPath[litIndex * 2];
					mHeadIndices[color] = litIndex * 3;
				}
			}
			mLastColor = color;
			color = getParent(color);
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
		// decrease the color to go down the Tree, while the occurrence is in A, and open the A Paths for those partitions
		while (color >= 0) {
			if (mAllInA.get(color)) {
				mMaxColor = color;
				mLastColor = color;
				mHeadColor = color;
			} else {
				// stop on the partition that doesn't see a switch anymore
				if (literalInfo.isBorShared(color)) {
					break;
				}
				// switch from B to A
				if (literalInfo.isALocal(color)) {
					mStart[color] = mPath[litIndex * 2];
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
			mAllInA.clear();
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
			mLastColor = color;
			color = getParent(color);
		}
		if (color > mMaxColor) {
			mMaxColor = color;
		}
	}
	
	private void openAPathsOnMixedLiterals(LitInfo literalInfo, int litIndex) {
		int color = mLastColor;
		
		while (color <= mNumInterpolants - 1 && color >= 0) {
			if (literalInfo.isBorShared(color)) {
				break;
			}
			if (literalInfo.isMixed(color) ) {
				mStart[color] = literalInfo.getMixedVar();
				mStartIndices[color] = litIndex * 3 + 1;
			}
			color = getMixedChild(color, literalInfo);
		}
	}
	
	// 
	private void closeAPathsForTesters(ApplicationTerm selTerm, int litIndex) {
		// get the occurrence of the tester
		Occurrence testerOcc = mTestersOccurrence.get(selTerm.getParameters()[0]);
		mAllInA.and(testerOcc.mInA);
		int color = mLastColor;
		// move up the tree and close A-paths for partitions that need to see a switch
		while (color <= mNumInterpolants - 1) {
			// stop as soon as no closing is needed (path can stay in A)
			if (testerOcc.isAorShared(color)) {
				break;
			}
			mAllInA.clear();
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
			mLastColor = color;
			// go up the tree
			color = getParent(color);
		}
		if (color > mMaxColor) {
			mMaxColor = color;
		}
	}
	
	// 
	private void openAPathsForTesters(ApplicationTerm selTerm, int litIndex) {
		Occurrence testerOcc = mTestersOccurrence.get(selTerm.getParameters()[0]);
		int color = mLastColor;
		// decrease the color to go down the Tree, while the occurrence is in A, and open the A Paths for those partitions
		while (color >= 0) {
			if (mAllInA.get(color)) {
				mMaxColor = color;
				mLastColor = color;
				mHeadColor = color;
			} else {
				// stop on the partition that doesn't see a switch anymore
				if (testerOcc.isBorShared(color)) {
					break;
				}
				// switch from B to A
				if (testerOcc.isALocal(color)) {
					mStart[color] = mPath[litIndex * 2];
					mStartIndices[color] = litIndex * 3;
				}				
			}
			mLastColor = color;
			color = getALocalChild(color, testerOcc);
		}
	}
	
	// adds the completed A path to the interpolant of the given interpolant (color)
	private void addCompletedAPath(int color) {
		Term left = mStart[color];
		Term right = mEnd[color];
		// TODO: check if modulo iss set correctly
		for (int i = mStartIndices[color]; i != mEndIndices[color]; i = (i + 1) % ((mPath.length - 1) / 2 * 3)) {
			if (mStartSelectors[i] != null) {
				if (mStartTesters[i] != null) {
					// String s = mStartTesters[i];
					mInterpolants[color].add(mTheory.term(mStartTesters[i], left));
				}
				if (mStartConstructors[i] != null) {
					mInterpolants[color].add(mTheory.term(SMTLIBConstants.IS, new String[] { mStartConstructors[i] },
							null, left));
				}
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
			for (Term term : ((ApplicationTerm) parent).getParameters()) {
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
		FunctionSymbol constructorSymbol = consTerm.getFunction();
		assert(constructorSymbol.getReturnSort().getSortSymbol().isDatatype());
		DataType datatype = (DataType) consTerm.getSort().getSortSymbol();
		Constructor cons = datatype.findConstructor(constructorSymbol.getName());
		String[] s = cons.getSelectors();
		Term[] terms = consTerm.getParameters();
		for (int i = 0; i < terms.length; i++) {
			if (childTerm.equals(terms[i])) {
				return s[i];
			}
		}
		throw new AssertionError("child term not found in constructors");
	}
	
	// returns the name of the constructor. Used to build testers
	private String getConstructorName(FunctionSymbol constructor) {
		DataType dataType = (DataType) constructor.getReturnSort().getSortSymbol();
		return dataType.findConstructor(constructor.getName()).getName();

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
			// TODO: 
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
			// TODO: 
			if (occ.isMixed(child)) {
				return child;
			}
			child = mInterpolator.mStartOfSubtrees[child] - 1;
		}
		return -1;
	}
	
}

// TODO: getReturnSort on functionsymbol as for dataType???