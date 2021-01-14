package de.uni_freiburg.informatik.ultimate.smtinterpol.theory.bitvector;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.ConstantTerm;
import de.uni_freiburg.informatik.ultimate.logic.FunctionSymbol;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.logic.Theory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.BooleanVarAtom;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.Clause;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.DPLLAtom;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.Literal;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.util.Pair;
import de.uni_freiburg.informatik.ultimate.util.datastructures.ScopedArrayList;

public class BitBlaster {

	private final Theory mTheory;
	private final ScopedArrayList<Literal> mLiterals;
	private final ScopedArrayList<Term> mAllTerms;
	private final HashMap<String, TermVariable> mVarPrefix;
	private final HashMap<Term, DPLLAtom> mBoolAtoms;
	private final ScopedArrayList<Clause> mClauses;
	private final HashMap<Term, Term[]> mEncTerms; // Term[0] is the least bit, the most right bit of Term
	private final HashMap<String, Term> mEncAtoms;
	private final BVUtils mBVUtils;
	private final int mStackLevel;

	public BitBlaster(final Theory theory, final int engineStackLevel, final ScopedArrayList<Literal> allLiterals,
			final ScopedArrayList<Term> allTerms) {
		mTheory = theory;
		mLiterals = allLiterals;
		mAllTerms = allTerms;
		mVarPrefix = new HashMap<>();
		mEncTerms = new HashMap<>();
		mEncAtoms = new HashMap<>();
		mBVUtils = new BVUtils(mTheory);
		mBoolAtoms = new HashMap<>();
		mClauses = new ScopedArrayList<>();
		mStackLevel = engineStackLevel;
	}

	public Term bitBlasting() {
		Term equisatProp;
		final Term[] propSkeleton = new Term[mLiterals.size()];
		for (int i = 0; i < mLiterals.size(); i++) {
			// TODO atom status
			final String atomPrefix = "At_" + i;
			final TermVariable boolVar = mTheory.createFreshTermVariable(atomPrefix, mTheory.getSort("Bool"));
			mBoolAtoms.put(boolVar, new BooleanVarAtom(boolVar, mStackLevel));
			mEncAtoms.put(atomPrefix, boolVar);
			if (mLiterals.get(i).getSign() == -1) {
				propSkeleton[i] = mTheory.not(boolVar);
			} else {
				propSkeleton[i] = boolVar;
			}
			mVarPrefix.put(atomPrefix, boolVar);
		}
		for (final Term term : mAllTerms) {
			// e(t), t in terms. Terms Size long Array of bool vars with e(t)_i being var at position i
			mEncTerms.put(term, getEncodedTerm(term));
		}
		// Initial propositional configuration
		equisatProp = mTheory.and(propSkeleton);
		for (final Term t : propSkeleton) {
			addClause(t);
		}

		// add BVConstraint of Atoms as conjunct
		for (int i = 0; i < mLiterals.size(); i++) {
			final DPLLAtom atom = mLiterals.get(i).getAtom();
			final Term encAtom = mEncAtoms.get("At_" + i);
			final Term bvConstraint = getBvConstraintAtom(encAtom, atom);
			equisatProp = mTheory.and(equisatProp, bvConstraint);
		}
		// add BVConstraint of all subterms as conjunct
		for (final Term term : mAllTerms) {
			final Term bvConstraint = getBvConstraintTerm(term);
			equisatProp = mTheory.and(equisatProp, bvConstraint);
		}
		return equisatProp;
	}

	/*
	 * Encodes bitvector Term in an Array of same lenth as the size of the bitvector Term.
	 * The Array contains Fresh Boolean Variables with name:
	 * "e(term)_i" where e stands for encoded, term is the input term and i the current position in the Array
	 */
	private Term[] getEncodedTerm(final Term term) {
		final BigInteger sizeBig = mTheory.toNumeral(term.getSort().getIndices()[0]);
		final int size = sizeBig.intValue();
		final Term[] boolvector = new Term[size];
		for (int i = 0; i < size; i++) {
			final String termPrefix = "e(" + term + ")_" + i;
			final TermVariable tv = mVarPrefix.get(termPrefix);
			final TermVariable boolVar;
			if (tv != null) {
				boolVar = tv;
			} else {
				boolVar = mTheory.createFreshTermVariable(termPrefix, mTheory.getSort("Bool"));
				mBoolAtoms.put(boolVar, new BooleanVarAtom(boolVar, mStackLevel));
				mVarPrefix.put(termPrefix, boolVar);
			}
			boolvector[i] = boolVar;
		}
		return boolvector;
	}

	// returns the boolean variable representing term
	private TermVariable getNewBoolVar(final Term term, final int bit) {
		final String prefix = "e(" + term.toString() + ")_" + bit;
		final TermVariable tv = mVarPrefix.get(prefix);
		if (tv == null) {
			throw new UnsupportedOperationException("Boolean variable was not genereated: " + term);
		} else {
			return tv;
		}
	}

	/*
	 * Creates BVConstraint for Atom's
	 * For equals:
	 * (AND lhs_i = rhs_i) <=> encAtom
	 * For bvult:
	 * TODO
	 */
	private Term getBvConstraintAtom(final Term encAtom, final DPLLAtom atom) {
		if (atom instanceof BVEquality) {
			// (AND lhs_i = rhs_i) <=> encAtom
			final BVEquality bveqatom = (BVEquality) atom;
			final BigInteger sizeBig = mTheory.toNumeral(bveqatom.getLHS().getSort().getIndices()[0]);
			final int size = sizeBig.intValue();
			final Term[] eqconj = new Term[size];
			for (int i = 0; i < size; i++) {
				final Term equals =
						// TODO check effizienz bei großen BITVECS
						mTheory.and(
								mTheory.or(mTheory.not(getNewBoolVar(bveqatom.getLHS(), i)),
										getNewBoolVar(bveqatom.getRHS(), i)),
								mTheory.or(mTheory.not(getNewBoolVar(bveqatom.getRHS(), i)),
										getNewBoolVar(bveqatom.getLHS(), i)));
				eqconj[i] = equals;
			}
			final Term eqconjunction = mTheory.and(eqconj);
			final Term iff = mTheory.and(mTheory.or(mTheory.not(encAtom), eqconjunction),
					mTheory.or(mTheory.not(eqconjunction), encAtom));
			System.out.println("ATOM CNF:");
			final Term cnfTerm = toCNF(iff);
			cnfToClause((ApplicationTerm) cnfTerm);
			return iff;
		} else if (atom instanceof BVInEquality) {
			final BVInEquality bveqatom = (BVInEquality) atom;
			// unsigned operants, holds if cout is false
			final Term bvult =
					mTheory.not(adder(mEncTerms.get(bveqatom.getLHS()), negate(mEncTerms.get(bveqatom.getRHS())),
							mTheory.mTrue).getSecond());

			// TODO signed
			final Term iff = mTheory.and(mTheory.or(mTheory.not(encAtom), bvult),
					mTheory.or(mTheory.not(bvult), encAtom));
			final Term cnfTerm = toCNF(iff);
			cnfToClause((ApplicationTerm) cnfTerm);
			return iff;
		}
		throw new UnsupportedOperationException("Unknown Atom");
	}

	private Term getBvConstraintTerm(final Term term) {
		final Term[] encTerm = mEncTerms.get(term);
		if (term instanceof TermVariable) {
			return mTheory.mTrue;
		}
		if (term instanceof ConstantTerm) {
			final Term[] constresult = new Term[encTerm.length];
			for (int i = 0; i < encTerm.length; i++) {
				Term boolVar;
				final String termstring = BVUtils.getConstAsString((ConstantTerm) term);
				if (termstring.charAt(termstring.length() - 1 - i) == '1') {
					boolVar = mTheory.mTrue;
				} else {
					boolVar = mTheory.mFalse;
				}
				mBoolAtoms.put(boolVar, new BooleanVarAtom(boolVar, mStackLevel));
				final Term iff = mTheory.and(mTheory.or(mTheory.not(encTerm[i]), boolVar),
						mTheory.or(mTheory.not(boolVar), encTerm[i]));
				equivalenceAsClausel(encTerm[i], boolVar);
				constresult[i] = iff;
			}
			return mTheory.and(constresult);
		}
		if (term instanceof ApplicationTerm) {
			final ApplicationTerm appterm = (ApplicationTerm) term;
			final FunctionSymbol fsym = appterm.getFunction();
			if (appterm.getParameters().length == 0) {
				// Variable but not instanceof TermVariable
				return mTheory.mTrue;
			}
			// Appterm, not a Variable:
			if (fsym.isIntern()) {
				Term[] conjunction = new Term[encTerm.length];
				final Term[] constraint = new Term[encTerm.length];
				switch (fsym.getName()) {
				case "bvand": {
					for (int i = 0; i < encTerm.length; i++) {
						final Term and = mTheory.or(mTheory.not(getNewBoolVar(appterm.getParameters()[0], i)),
								mTheory.not(getNewBoolVar(appterm.getParameters()[1], i)));
						conjunction[i] = and;
					}
					break;
				}
				case "bvor": {
					for (int i = 0; i < encTerm.length; i++) {
						final Term or = mTheory.or(getNewBoolVar(appterm.getParameters()[0], i),
								getNewBoolVar(appterm.getParameters()[1], i));
						conjunction[i] = or;
					}
					break;
				}
				case "bvnot": {
					for (int i = 0; i < encTerm.length; i++) {
						final Term not = mTheory.not(getNewBoolVar(appterm.getParameters()[0], i));
						conjunction[i] = not;
					}
					break;
				}
				case "bvadd": {
					conjunction =
							adder(mEncTerms.get(appterm.getParameters()[0]), mEncTerms.get(appterm.getParameters()[1]),
									mTheory.mFalse).getFirst();
					break;
				}
				case "bvsub": {
					conjunction =
							adder(mEncTerms.get(appterm.getParameters()[0]),
									negate(mEncTerms.get(appterm.getParameters()[1])),
									mTheory.mTrue).getFirst();
					break;
				}
				case "bvshl": {
					final int stage =
							mTheory.toNumeral(appterm.getParameters()[1].getSort().getIndices()[0]).intValue() - 1;
					conjunction = leftshift(appterm.getParameters()[0], appterm.getParameters()[1], stage);
					break;
				}
				case "bvmul": {
					final int stage =
							mTheory.toNumeral(appterm.getParameters()[1].getSort().getIndices()[0]).intValue() - 1;
					conjunction = multiplier(appterm.getParameters()[0], appterm.getParameters()[1], stage);
					break;
				}
				case "bvudiv":
					final int stage =
							mTheory.toNumeral(appterm.getParameters()[1].getSort().getIndices()[0]).intValue() - 1;
					conjunction = multiplier(appterm.getParameters()[0], appterm.getParameters()[1], stage);
					// conjunction extended by 2 Constraints
					// encTerm * b + r = a
					// r < b
					break;
				case "bvurem":
				case "bvlshr":
				case "bvneg":
				case "concat":
				default:
					throw new UnsupportedOperationException(
							"Unsupported functionsymbol for bitblasting: " + fsym.getName());
				}
				for (int i = 0; i < conjunction.length; i++) {
					termConstraintToClausel(conjunction, encTerm);
					final Term iff = mTheory.and(mTheory.or(mTheory.not(encTerm[i]), conjunction[i]),
							mTheory.or(mTheory.not(conjunction[i]), encTerm[i]));
					constraint[i] = iff;
				}

				return mTheory.and(constraint);
			}
		}

		throw new UnsupportedOperationException("Unknown BVConstraint for term: " + term);
	}

	// negates each term in terms
	private Term[] negate(final Term[] terms) {
		final Term[] negateresult = new Term[terms.length];
		for (int i = 0; i < terms.length; i++) {
			negateresult[i] = mTheory.not(terms[i]);
		}
		return negateresult;
	}

	private Term sumAdder(final Term a, final Term b, final Term cin) {
		final Term xor = mTheory.and(mTheory.or(mTheory.not(a), mTheory.not(b), cin),
				mTheory.or(mTheory.not(a), b, mTheory.not(cin)),
				mTheory.or(a, mTheory.not(b), mTheory.not(cin)),
				mTheory.or(a, b, cin));
		return xor;
	}

	/*
	 * returns a xor b xor cin in CNF
	 * Check Performance compared to CNf Algo
	 */
	private Term sumAdderOld(final Term a, final Term b, final Term cin) {
		assert isTermLiteral(a);
		assert isTermLiteral(b);
		if (cin instanceof ApplicationTerm) {
			final ApplicationTerm cinApp = (ApplicationTerm) cin;
			if (cinApp.getParameters().length > 0) {
				assert cinApp.getFunction().getName().equals("and");
				final List<List<Term>> cinAsSet = new ArrayList<>();
				final Set<Term> resultConj = new HashSet<>();
				for (int i = 0; i < cinApp.getParameters().length; i++) {
					final List<Term> disjunction = new ArrayList<>();
					if (isTermLiteral(cinApp.getParameters()[i])) {
						resultConj.add(
								mTheory.or(mTheory.not(a), mTheory.not(b), cinApp.getParameters()[i]));
						resultConj.add(mTheory.or(a, b, cinApp.getParameters()[i]));

						disjunction.add(mTheory.not(cinApp.getParameters()[i]));
						cinAsSet.add(disjunction);
					} else if (cinApp.getParameters()[i] instanceof ApplicationTerm) {
						final ApplicationTerm disj = (ApplicationTerm) cinApp.getParameters()[i];
						assert (disj.getFunction().getName().equals("or"));
						// cin is a conjunction of disjunctions
						resultConj.add(mTheory.or(a, b, disj.getParameters()[0], disj.getParameters()[1]));
						resultConj.add(
								mTheory.or(mTheory.not(a), mTheory.not(b), mTheory.not(disj.getParameters()[0]),
										mTheory.not(disj.getParameters()[1])));
						for (int j = 0; j < disj.getParameters().length; j++) {
							assert isTermLiteral(disj.getParameters()[j]);
							disjunction.add(mTheory.not(disj.getParameters()[j]));
						}
						cinAsSet.add(disjunction);
						// throw new UnsupportedOperationException("Fehler fix!");
					} else {
						throw new UnsupportedOperationException("Unexpected carryAdder result");
					}
				}

				final List<List<Term>> cartProduct = cartesianProduct(cinAsSet);
				for (final List<Term> disjunction : cartProduct) {
					final Term disjuncTerm = listToDisjunction(disjunction, false);
					resultConj.add(mTheory.or(disjuncTerm, a, mTheory.not(b)));
					resultConj.add(mTheory.or(disjuncTerm, b, mTheory.not(a)));
				}
				Term[] result = new Term[resultConj.size()];
				result = resultConj.toArray(result);
				return mTheory.and(result);
			} else {
				assert cin.equals(mTheory.mFalse);
				return mTheory.and(mTheory.or(mTheory.not(a), mTheory.not(b)),
						mTheory.or(a, b));
			}
		} else if (isTermLiteral(cin)) {
			return mTheory.and(mTheory.or(mTheory.not(a), mTheory.not(b), cin),
					mTheory.or(mTheory.not(a), b, mTheory.not(cin)),
					mTheory.or(a, mTheory.not(b), mTheory.not(cin)),
					mTheory.or(a, b, cin));
		}
		throw new UnsupportedOperationException("Unexpected carryAdder result");
		// return mTheory.xor(a, mTheory.xor(b, cin));
	}

	/*
	 * return true, if term is either an atom or a negated atom
	 */
	private boolean isTermLiteral(final Term t) {
		if (t instanceof TermVariable) {
			return true;
		} else if (t instanceof ApplicationTerm) {
			final ApplicationTerm ap = (ApplicationTerm) t;
			if (ap.getFunction().getName().equals("not")) {
				if ((ap.getParameters().length == 1) && (ap.getParameters()[0] instanceof TermVariable)) {
					return true;
				}
			}
		}
		return false;
	}

	// returns ((a and b) or (mTheory.(a xor b) and cin)) in CNF
	private Term carryAdder(final Term a, final Term b, final Term cin) {
		if (cin.equals(mTheory.mFalse)) {
			return mTheory.and(a, b);
		} else if (cin.equals(mTheory.mTrue)) {
			return mTheory.or(a, b);
			// throw new UnsupportedOperationException("TODO nicht in CNF");
		}
		return mTheory.and(mTheory.or(a, b), mTheory.or(a, cin), mTheory.or(b, cin));
	}

	private Term[] carryBits(final Term[] encA, final Term[] encB, final Term cin) {
		assert encA.length == encB.length;
		final Term[] carryBits = new Term[encA.length];
		carryBits[0] = cin;
		for (int i = 1; i < encA.length; i++) {
			carryBits[i] = carryAdder(encA[i - 1], encB[i - 1], carryBits[i - 1]);
		}
		return carryBits;
	}

	private Pair<Term[], Term> adder(final Term[] encA, final Term[] encB, final Term cin) {
		assert encA.length == encB.length;
		final Term[] sumResult = new Term[encA.length];
		final Term[] carryBits = carryBits(encA, encB, cin);
		for (int i = 0; i < encA.length; i++) {
			// System.out.println("IN: " + mTheory.xor(encA[i], mTheory.xor(encB[i], carryBits[i])).toStringDirect());
			sumResult[i] = sumAdder(encA[i], encB[i], carryBits[i]);
			// System.out.println("OUT: " + sumResult[i].toStringDirect());
		}
		final Term cout = carryBits[carryBits.length - 1];
		return new Pair<>(sumResult, cout);
	}

	/*
	 * Barrel Shifter
	 * TODO optimize, as soon as b[log_2 size] is 1, return zerobitvec
	 */
	private Term[] leftshift(final Term a, final Term b, final int stage) {
		final Term[] encA = mEncTerms.get(a);
		final Term[] encB = mEncTerms.get(b);
		final Term[] shiftResult = new Term[encA.length];
		if (stage == -1) {
			return encA;
		} else {
			for (int i = 0; i < encA.length; i++) {
				System.out.println(b);
				if (b instanceof ConstantTerm) {
					final String bAsString = BVUtils.getConstAsString((ConstantTerm) b);
					if (bAsString.charAt(bAsString.length() - 1 - stage) == '1') {
						if (i >= Math.pow(2, stage)) {
							shiftResult[i] = mTheory.or(mTheory.not(encB[stage]),
									leftshift(a, b, stage - 1)[i - (int) Math.pow(2, stage)]);
						} else {
							shiftResult[i] = mTheory.or(mTheory.not(encB[stage]), mTheory.mFalse);
						}
					} else {
						System.out.println(encB[stage]);
						shiftResult[i] = mTheory.or(encB[stage], leftshift(a, b, stage - 1)[i]);
					}
				} else {
					if (i >= Math.pow(2, stage)) {
						// ifthenelse in CNF (not a or b) and (a or c)
						shiftResult[i] = mTheory.and(
								mTheory.or(mTheory.not(encB[stage]),
										leftshift(a, b, stage - 1)[i - (int) Math.pow(2, stage)]),
								mTheory.or(encB[stage], leftshift(a, b, stage - 1)[i]));
					} else {
						shiftResult[i] = mTheory.and(mTheory.or(mTheory.not(encB[stage]), mTheory.mFalse),
								mTheory.or(encB[stage], leftshift(a, b, stage - 1)[i]));
					}
				}
			}
		}
		return shiftResult;
	}

	/*
	 * Used, when b is not a term in the orginial formula, therefore mEncTerms.get(b) would be null
	 * TODO testen, pc laufzeit etc achtung
	 */
	private Term[] leftshiftMul(final Term a, final Term b, final int stage) {
		final Term[] encA = mEncTerms.get(a);
		final Term[] shiftResult = new Term[encA.length];
		if (stage == -1) {
			return encA;
		} else {
			for (int i = 0; i < encA.length; i++) {
				if (b instanceof ConstantTerm) {
					final String bAsString = BVUtils.getConstAsString((ConstantTerm) b);
					if (bAsString.charAt(bAsString.length() - 1 - stage) == '1') {
						if (i >= Math.pow(2, stage)) {
							shiftResult[i] =
									leftshiftMul(a, b, stage - 1)[i - (int) Math.pow(2, stage)];
						} else {
							shiftResult[i] = mTheory.mFalse;
						}
					} else {
						shiftResult[i] = leftshiftMul(a, b, stage - 1)[i];
					}
				} else {
					throw new UnsupportedOperationException(
							" Can only be used in multiplier, second argument needs to be ConstantTerm");
				}
			}
		}
		return shiftResult;
	}

	private Term[] multiplier(final Term a, final Term b, final int stage) {
		final Term[] encA = mEncTerms.get(a);
		final Term[] encB = mEncTerms.get(b);
		final int size = encA.length;
		final Term[] zeroVec = new Term[size];
		Arrays.fill(zeroVec, mTheory.mFalse);
		if (stage == -1) {
			return zeroVec;
		} else {
			final Term[] mul = multiplier(a, b, stage - 1);
			final Term[] shift;
			if (stage != 0) {
				final String s = Integer.toString(stage, 2);
				final String stageAsBits = "#b" + new String(new char[size - s.length()]).replace("\0", "0") + s;
				shift = leftshiftMul(a, mTheory.binary(stageAsBits), size - 1);
			} else {
				// a shifted by 0 = a
				shift = encA;
			}
			final Term[] ite = new Term[size];
			for (int i = 0; i < size; i++) {
				if (b instanceof ConstantTerm) {
					final String bString = BVUtils.getConstAsString((ConstantTerm) b);
					if (bString.charAt(bString.length() - stage - 1) == '1') {
						ite[i] = mTheory.or(mTheory.not(encB[stage]), shift[i]);
					} else {
						ite[i] = mTheory.or(encB[stage], mTheory.mFalse);
					}
				} else {
					// mTheory.ifthenelse(encB[stage], shift[i], mTheory.mFalse);
					ite[i] = mTheory.and(
							mTheory.or(mTheory.not(encB[stage]), shift[i]),
							mTheory.or(encB[stage], mTheory.mFalse));
				}

			}
			final Term[] sum = adder(mul, ite, mTheory.mFalse).getFirst();
			return sum;
		}
	}

	/*
	 * adds clauses for a term of from: lhs <=> rhs
	 * lhs and rhs must be a literal
	 */
	private void equivalenceAsClausel(final Term lhs, final Term rhs) {
		addClause(mTheory.or(mTheory.not(lhs), rhs));
		addClause(mTheory.or(mTheory.not(rhs), lhs));
	}

	private void cnfToClause(final ApplicationTerm term) {
		for (int i = 0; i < term.getParameters().length; i++) {
			addClause(term.getParameters()[i]);
		}
	}

	private Term toCNF(final Term term) {
		final NnfTransformer nnf = new NnfTransformer();
		final Term nnfTerm = nnf.transform(term); // TODO FIX RECURSION
		final CnfTransformer cnf = new CnfTransformer();
		final Term cnfTerm = cnf.transform(cnf.transform(nnfTerm));
		final CleanTransfomer cleaner = new CleanTransfomer();
		final Term cleanTerm = cleaner.transform(cnfTerm);
		System.out.println("CNF SIZE: " + ((ApplicationTerm) cleanTerm).getParameters().length);
		return cleanTerm;
	}

	/*
	 *
	 */
	private void termConstraintToClausel(final Term[] conjunction, final Term[] encTerm) {
		final Term[] constraint = new Term[conjunction.length];
		for (int i = 0; i < conjunction.length; i++) {
			final Term iff = mTheory.and(mTheory.or(mTheory.not(encTerm[i]), conjunction[i]),
					mTheory.or(mTheory.not(conjunction[i]), encTerm[i]));
			constraint[i] = iff;
		}
		System.out.println("TERM CNF:");
		final Term cnfTerm = toCNF(mTheory.and(constraint));
		cnfToClause((ApplicationTerm) cnfTerm);
	}

	/*
	 * reports the term Constraint as Clauses
	 * correct
	 */
	private void termConstraintToClauselOLD(final Term conjunction, final Term encTerm) {
		if (conjunction instanceof ApplicationTerm) {
			final ApplicationTerm appConjunction = (ApplicationTerm) conjunction;
			if (appConjunction.getFunction().getName().equals("and")) {
				cnfEqAtomGetClauses(appConjunction, encTerm);
			} else {
				assert (conjunction.equals(mTheory.mFalse));
				addClause(mTheory.not(encTerm));
			}
		} else {
			assert (conjunction instanceof TermVariable);
			equivalenceAsClausel(encTerm, conjunction);
		}
	}

	/*
	 * Gets all clauses from a Formula of form: (CNF) <=> Atom
	 */
	private void cnfEqAtomGetClauses(final ApplicationTerm cnfTerm, final Term atom) {
		assert cnfTerm.getFunction().getName().equals("and");
		final List<List<Term>> cnf = new ArrayList<>();
		final List<Term> encTermList = new ArrayList<>();
		encTermList.add(atom);
		cnf.add(encTermList);
		for (int j = 0; j < cnfTerm.getParameters().length; j++) {
			final List<Term> disjunction = new ArrayList<>();
			if (cnfTerm.getParameters()[j] instanceof ApplicationTerm) {
				final ApplicationTerm appDisjunction =
						(ApplicationTerm) cnfTerm.getParameters()[j];
				if (appDisjunction.getFunction().getName().equals("or")) {
					for (int k = 0; k < appDisjunction.getParameters().length; k++) {
						disjunction.add(mTheory.not(appDisjunction.getParameters()[k])); // has to be negated
					}
					// add Clauses for: (Atom => (CNF))
					addClause(mTheory.or(listToDisjunction(disjunction, true), mTheory.not(atom)));
					cnf.add(disjunction);
				} else if (appDisjunction.getParameters().length == 1) {
					addClause(mTheory.or(cnfTerm.getParameters()[j], mTheory.not(atom)));
					// Wenn fehler, dann hier andere richtung der implikation
				} else {
					throw new UnsupportedOperationException("Not in CNF: " + cnfTerm);
				}
			} else {
				addClause(mTheory.or(cnfTerm.getParameters()[j], mTheory.not(atom)));
				// Wenn fehler, dann hier andere richtung der implikation
			}
		}
		// add Clauses for: ((CNF) => Atom)
		final List<List<Term>> cartProduct = cartesianProduct(cnf);
		for (final List<Term> disjunction : cartProduct) {
			addClause(listToDisjunction(disjunction, false));
		}
	}

	/*
	 * get's a list of terms,
	 * returns these terms as disjunction
	 * if negated is set to true, each disjunct will be negated
	 * TODO: Doppel Negation vermeiden!! für code übersicht
	 */
	private Term listToDisjunction(final List<Term> list, final boolean negate) {
		assert !list.isEmpty();
		Term[] disjArray = new Term[list.size()];
		disjArray = list.toArray(disjArray);
		for (int i = 0; i < list.size(); i++) {
			if (negate) {
				disjArray = negate(disjArray);
			}
		}
		return mTheory.or(disjArray);
	}

	// From https://rosettacode.org/wiki/Cartesian_product_of_two_or_more_lists#Java
	private List<List<Term>> cartesianProduct(final List<List<Term>> lists) {
		final List<List<Term>> product = new ArrayList<>();
		// We first create a list for each value of the first list
		cartesianProduct(product, new ArrayList<>(), lists);
		return product;
	}

	private void cartesianProduct(final List<List<Term>> result, final List<Term> existingTupleToComplete,
			final List<List<Term>> valuesToUse) {
		for (final Term value : valuesToUse.get(0)) {
			final List<Term> newExisting = new ArrayList<>(existingTupleToComplete);
			newExisting.add(value);
			// If only one column is left
			if (valuesToUse.size() == 1) {
				// We create a new list with the exiting tuple for each value with the value
				// added
				result.add(newExisting);
			} else {
				// If there are still several columns, we go into recursion for each value
				final List<List<Term>> newValues = new ArrayList<>();
				// We build the next level of values
				for (int i = 1; i < valuesToUse.size(); i++) {
					newValues.add(valuesToUse.get(i));
				}
				cartesianProduct(result, newExisting, newValues);
			}
		}
	}

	private void addClause(final Term term) {
		mClauses.add(mBVUtils.getClause(term, mBoolAtoms, mStackLevel));
	}

	public Collection<DPLLAtom> getBoolAtoms() {
		return mBoolAtoms.values();
	}

	public ScopedArrayList<Clause> getClauses() {
		return mClauses;
	}

}
