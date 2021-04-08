package de.uni_freiburg.informatik.ultimate.smtinterpol.theory.bitvector;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.HashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.ConstantTerm;
import de.uni_freiburg.informatik.ultimate.logic.FunctionSymbol;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.logic.Theory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.BooleanVarAtom;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.Clause;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.DPLLAtom;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.DPLLAtom.TrueAtom;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.Literal;
import de.uni_freiburg.informatik.ultimate.smtinterpol.proof.LeafNode;
import de.uni_freiburg.informatik.ultimate.smtinterpol.proof.SourceAnnotation;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.util.Pair;
import de.uni_freiburg.informatik.ultimate.util.datastructures.ScopedArrayList;

/**
 * TODO
 *
 * @author Max Barth (max.barth95@gmx.de)
 *
 */

public class BitBlaster {
	private final Theory mTheory;
	private ScopedArrayList<Literal> mInputLiterals;
	private HashMap<String, TermVariable> mVarPrefix; // Maps enc_term indices to their bool vars.
	private HashMap<Term, DPLLAtom> mBoolAtoms; // All Bool Atoms, aux varaibles too
	private ScopedArrayList<Clause> mClauses; // Output clauses
	private HashMap<Term, Term[]> mEncTerms; // Term[0] is the least bit, the most right bit of Term
	private HashMap<Term, Term> mBitBlastAtoms; // ensures that Bitblasting happens only once for each Atom
	private HashMap<Term, Literal> mLiterals; // Maps mEncAtoms to mInputLiterals
	private int mStackLevel;

	private final HashMap<Term, ScopedArrayList<Clause>> mBitBlastingResult;
	private ScopedArrayList<Clause> mClauseCopy;


	public BitBlaster(final Theory theory) {
		mTheory = theory;
		mBitBlastingResult = new HashMap<>(); // Save previous BitBlasting results
	}



	public void bitBlasting(final ScopedArrayList<Literal> allLiterals,
			final LinkedHashSet<Term> allTerms, final int engineStackLevel) {
		mStackLevel = engineStackLevel;
		mInputLiterals = allLiterals;
		mVarPrefix = new HashMap<>();
		mEncTerms = new HashMap<>();
		mBitBlastAtoms = new HashMap<>();
		mBoolAtoms = new HashMap<>();
		mLiterals = new HashMap<>();
		mClauses = new ScopedArrayList<>();
		mClauseCopy = new ScopedArrayList<>();

		Term equisatProp;
		final Term[] propSkeleton = new Term[mInputLiterals.size()];
		for (int i = 0; i < mInputLiterals.size(); i++) {
			final Term bitblastingAtom = createBoolAtom(i);
			if (mInputLiterals.get(i).getSign() == 1) {
				propSkeleton[i] = bitblastingAtom;
			} else {
				propSkeleton[i] = mTheory.not(bitblastingAtom);
			}
		}
		for (final Term term : allTerms) {
			// e(t), t in terms. Terms Size long Array of bool vars with e(t)_i being var at position i
			if (term.getSort().isBitVecSort()) {
				mEncTerms.put(term, getEncodedTerm(term));
			}

		}
		// Initial propositional configuration
		equisatProp = mTheory.and(propSkeleton);
		toClauses(equisatProp);

		// add BVConstraint of Atoms as conjunct
		for (final Term atom : mBitBlastAtoms.keySet()) {
			getBvConstraintAtom(atom, mBitBlastAtoms.get(atom));
		}

		// add BVConstraint of all subterms as conjunct
		for (final Term term : allTerms) {
			mClauseCopy = new ScopedArrayList<>();
			getBvConstraintTerm(term);
			if (!mBitBlastingResult.containsKey(term)) {
				// save BVConstraints for term
				mBitBlastingResult.put(term, mClauseCopy);
				mClauseCopy = new ScopedArrayList<>();
			}
		}

	}

	private Term createBoolAtom(final int i) {
		Term atom = mInputLiterals.get(i).getAtom().getSMTFormula(mTheory);

		final String atomPrefix = "At_" + i;
		final Term boolVar = mTheory.createFreshTermVariable(atomPrefix, mTheory.getSort("Bool"));
		final DPLLAtom dpll = new BooleanVarAtom(boolVar, mStackLevel);

		mBoolAtoms.put(boolVar, dpll);
		mLiterals.put(boolVar, mInputLiterals.get(i));



		assert atom instanceof ApplicationTerm;
		final ApplicationTerm apAtom = (ApplicationTerm) atom;
		assert apAtom.getFunction().getName().equals("=");

		if (apAtom.getParameters()[0] instanceof ApplicationTerm) {
			if (((ApplicationTerm) apAtom.getParameters()[0]).getFunction().getName().equals("bvult")) {
				atom = apAtom.getParameters()[0];
			}
		} else if (apAtom.getParameters()[1] instanceof ApplicationTerm) {
			if (((ApplicationTerm) apAtom.getParameters()[1]).getFunction().getName().equals("bvult")) {
				atom = apAtom.getParameters()[1];
			}
		}


		mBitBlastAtoms.put(atom, boolVar);
		return boolVar;
	}



	/*
	 * Encodes bitvector Term in an Array of same lenth as the size of the bitvector Term.
	 * The Array contains Fresh Boolean Variables with name:
	 * "e(term)_i" where e stands for encoded, term is the input term and i the current position in the Array/BitVec
	 */
	private Term[] getEncodedTerm(final Term term) {
		assert term.getSort().isBitVecSort();
		final BigInteger sizeBig = mTheory.toNumeral(term.getSort().getIndices()[0]);
		final int size = sizeBig.intValue();

		final Term[] boolvector = new Term[size];
		for (int i = 0; i < size; i++) {
			final String termPrefix = "e_(" + term + ")_" + i;
			final TermVariable tv = mVarPrefix.get(termPrefix);
			final TermVariable boolVar;
			if (tv != null) {
				boolVar = tv;
			} else {
				boolVar = (TermVariable) createBoolAtom(termPrefix);
				mVarPrefix.put(termPrefix, boolVar);
			}
			boolvector[i] = boolVar;
		}
		return boolvector;
	}

	/*
	 * Creates BVConstraint for Atom's
	 * For equals:
	 * (AND lhs_i = rhs_i) <=> encAtom
	 * For bvult:
	 * not(bvadd (lhs not(rhs)).cout) <=> encAtom
	 */
	private void getBvConstraintAtom(final Term atom, final Term encAtom) {
		if (atom instanceof ApplicationTerm) {
			final ApplicationTerm apAtom = (ApplicationTerm) atom;
			final Term lhs = apAtom.getParameters()[0];
			final Term rhs = apAtom.getParameters()[1];

			if (((ApplicationTerm) atom).getFunction().getName().equals("=")) {
				// (AND lhs_i = rhs_i) <=> encAtom
				final BigInteger sizeBig = mTheory.toNumeral(lhs.getSort().getIndices()[0]);
				final int size = sizeBig.intValue();
				final Term[] eqconj = new Term[size];
				final Literal atLit = getLiteral(encAtom);
				if (size == 1) { // TODO after which size is bvcomp faster?
					for (int i = 0; i < size; i++) {
						// creates 2*size + 2^size Clauses, Only faster for small sizes
						final Literal lhsLit = getLiteral(mEncTerms.get(lhs)[i]);
						final Literal rhsLit = getLiteral(mEncTerms.get(rhs)[i]);
						final Literal[] lit1 = { atLit.negate(), lhsLit, rhsLit.negate() };
						addClause(lit1);
						final Literal[] lit2 = { atLit.negate(), lhsLit.negate(), rhsLit };
						addClause(lit2);
						eqconj[i] =
								mTheory.or(mTheory.and(mEncTerms.get(lhs)[i],
										mEncTerms.get(rhs)[i]),
										mTheory.and(mTheory.not(mEncTerms.get(rhs)[i]),
												mTheory.not(mEncTerms.get(lhs)[i])));
					}
					final Term eqconjunction = mTheory.and(eqconj);
					toClauses(mTheory.or(mTheory.not(eqconjunction), encAtom));
				} else {
					// usign bvcomp method to determin equality
					final Term[] bvxnor = new Term[size];
					for (int i = 0; i < size; i++) {
						final Term boolVar = createBoolAtom(null);
						final Literal at = getLiteral(boolVar);
						final Literal lhsLit = getLiteral(mEncTerms.get(lhs)[i]);
						final Literal rhsLit = getLiteral(mEncTerms.get(rhs)[i]);
						final Literal[] lit1 = { at, lhsLit, rhsLit };
						addClause(lit1);
						final Literal[] lit2 = { at, lhsLit.negate(), rhsLit.negate() };
						addClause(lit2);
						final Literal[] lit3 = { at.negate(), lhsLit, rhsLit.negate() };
						addClause(lit3);
						final Literal[] lit4 = { at.negate(), lhsLit.negate(), rhsLit };
						addClause(lit4);
						bvxnor[i] = boolVar;

						final Literal[] lit5 = { atLit.negate(), at };
						addClause(lit5);
					}
					toClauses(mTheory.or(encAtom, mTheory.not(mTheory.and(bvxnor))));
				}


			} else if (((ApplicationTerm) atom).getFunction().getName().equals("bvult")) {
				// bvult, holds if cout is false
				final Term bvult =
						mTheory.not(adder(mEncTerms.get(((ApplicationTerm) atom).getParameters()[0]),
								negate(mEncTerms.get(((ApplicationTerm) atom).getParameters()[1])),
								mTheory.mTrue, null).getSecond());

				final Literal bvultLit = getLiteral(bvult);
				final Literal atLit = getLiteral(encAtom);
				final Literal[] lit1 = { atLit.negate(), bvultLit };
				addClause(lit1);
				final Literal[] lit2 = { atLit, bvultLit.negate() };
				addClause(lit2);
			} else {
				throw new UnsupportedOperationException("Unknown Atom");
			}
		}
	}

	/*
	 * Bitblasting for all terms, reports the result as Clause to mClauses.
	 * If there exist an BitBlastngResult for this term, we'll add this instead
	 */
	private void getBvConstraintTerm(final Term term) {
		mClauseCopy = new ScopedArrayList<>();
		if (mBitBlastingResult.containsKey(term)) {
			mClauses.addAll(createClauseCopy(mBitBlastingResult.get(term)));
			return;
		}
		if (term instanceof TermVariable) {
			return;
		} else if (term instanceof ConstantTerm) {
			final Term[] encTerm = mEncTerms.get(term);
			// adds a Clause for each index
			for (int i = 0; i < encTerm.length; i++) {
				Term boolVar;
				final String termstring = BVUtils.getConstAsString((ConstantTerm) term);
				if (termstring.charAt(termstring.length() - 1 - i) == '1') {
					boolVar = mTheory.mTrue;
				} else {
					boolVar = mTheory.mFalse;
				}
				final DPLLAtom dpll = new BooleanVarAtom(boolVar, mStackLevel);
				mBoolAtoms.put(boolVar, dpll);
				addClauses(mTheory.or(mTheory.not(encTerm[i]), boolVar));
				addClauses(mTheory.or(mTheory.not(boolVar), encTerm[i]));

			}
		} else if (term instanceof ApplicationTerm) {
			final ApplicationTerm appterm = (ApplicationTerm) term;
			final FunctionSymbol fsym = appterm.getFunction();
			if (appterm.getParameters().length == 0) {
				// Variable but not instanceof TermVariable
				return;
			}
			if (fsym.isIntern()) {
				switch (fsym.getName()) {
				case "=":
				case "and":
				case "or":
				case "not":
				case "ite": {
					// CClosure should have dealt with this.
					return;
				}
				}
				final Term[] encTerm = mEncTerms.get(term);
				Term[] conjunction = new Term[encTerm.length];
				switch (fsym.getName()) {
				case "bvand": {
					for (int i = 0; i < encTerm.length; i++) {
						final Term and = mTheory.and(mEncTerms.get(appterm.getParameters()[0])[i],
								mEncTerms.get(appterm.getParameters()[1])[i]);
						conjunction[i] = and;
					}
					break;
				}
				case "bvor": {
					for (int i = 0; i < encTerm.length; i++) {
						final Term or = mTheory.or(mEncTerms.get(appterm.getParameters()[0])[i],
								mEncTerms.get(appterm.getParameters()[1])[i]);
						conjunction[i] = or;
					}
					break;
				}
				case "bvnot": {
					for (int i = 0; i < encTerm.length; i++) {
						final Term not = mTheory.not(mEncTerms.get(appterm.getParameters()[0])[i]);
						conjunction[i] = not;
					}
					break;
				}
				case "bvneg": {
					conjunction[encTerm.length - 1] =
							mTheory.not(mEncTerms.get(appterm.getParameters()[0])[encTerm.length - 1]);
					for (int i = 0; i < encTerm.length - 1; i++) {
						conjunction[i] = mEncTerms.get(appterm.getParameters()[0])[i];
					}
					break;
				}
				case "bvadd": {
					adder(mEncTerms.get(appterm.getParameters()[0]), mEncTerms.get(appterm.getParameters()[1]),
							mTheory.mFalse, encTerm).getFirst();
					// return, clauses will be created and saved in the Adder
					return;
				}
				case "bvsub": {
					conjunction =
							adder(mEncTerms.get(appterm.getParameters()[0]),
									negate(mEncTerms.get(appterm.getParameters()[1])),
									mTheory.mTrue, null).getFirst();
					break;
				}
				case "bvshl": {
					final int stage =
							mTheory.toNumeral(appterm.getParameters()[1].getSort().getIndices()[0]).intValue() - 1;
					conjunction = shift(appterm.getParameters()[0], appterm.getParameters()[1], stage, true);
					break;
				}
				case "bvmul": {
					final int stage =
							mTheory.toNumeral(appterm.getParameters()[1].getSort().getIndices()[0]).intValue() - 1;
					multiplier(appterm.getParameters()[0], appterm.getParameters()[1], stage, encTerm);
					return;
				}

				case "bvlshr": {
					final int stage =
							mTheory.toNumeral(appterm.getParameters()[1].getSort().getIndices()[0]).intValue() - 1;
					conjunction = shift(appterm.getParameters()[0], appterm.getParameters()[1], stage, false);
					break;
				}
				case "concat": {
					conjunction = concatArrays(mEncTerms.get(appterm.getParameters()[0]),
							mEncTerms.get(appterm.getParameters()[1]));
					break;
				}
				case "extract": {
					conjunction = Arrays.copyOfRange(mEncTerms.get(appterm.getParameters()[0]),
							Integer.parseInt(appterm.getFunction().getIndices()[1]),
							Integer.parseInt(appterm.getFunction().getIndices()[0]) + 1);
					break;
				}
				case "bvudiv": {
					// b != 0 => e(t) * b + r = a
					// b != 0 => r < b
				}
				case "bvurem":
					// b != 0 => q * b + e(t) = a
					// b != 0 => e(t) < b
					division(appterm, conjunction, encTerm);
					return;
				default:
					throw new UnsupportedOperationException(
							"Unsupported functionsymbol for bitblasting: " + fsym.getName());
				}
				for (int i = 0; i < conjunction.length; i++) {
					toClauses(mTheory.or(mTheory.not(conjunction[i]), encTerm[i]));
					toClauses(mTheory.or(mTheory.not(encTerm[i]), conjunction[i]));
				}
			}
		} else {
			throw new UnsupportedOperationException("Unknown BVConstraint for term: " + term);
		}
	}

	/*
	 * Creates a Copy of all Input Clauses.
	 * Thereofore it searches for the current equivalent atoms or
	 * creates them if they didnt occure beforehand (AuxVars).
	 * After collecting the needed Atoms, a new Clause is created.
	 * We cannot re use old Clauses and therefore old Atoms, which have been created in a previous BitBlasting runs!
	 */
	private Collection<Clause> createClauseCopy(final ScopedArrayList<Clause> scopedArrayList) {
		// Auxar Map, maps oldAuxVar to newAuxVar
		final HashMap<Literal, Literal> auxVarMap = new HashMap<>();

		final ScopedArrayList<Clause> result = new ScopedArrayList<>();
		for (final Clause clause : scopedArrayList) {
			final Literal[] literal = new Literal[clause.getSize()];

			for (int i = 0; i < clause.getSize(); i++) {
				final Literal lit = clause.getLiteral(i);

				// look for the the new encoded term, corresponding to the old encoded term

				final String VarPrefix = lit.getAtom().getSMTFormula(mTheory).toStringDirect();
				final Pattern p = Pattern.compile("(e_\\(.*\\)_\\d*)");
				final Matcher m = p.matcher(VarPrefix);

				if (m.find()) {
					final String stringsdasda = m.group();
					final DPLLAtom newlit = mBoolAtoms.get(mVarPrefix.get(stringsdasda));

					if (lit.getSign() == 1) {
						literal[i] = newlit;
					} else {
						literal[i] = newlit.negate();
					}
				}
				else if (VarPrefix.contains("At")) { // Case Input Atom
					assert false;
				} else { // Case AuxVar
					Literal newAuxVar;
					if (auxVarMap.containsKey(lit)) {
						newAuxVar = auxVarMap.get(lit);
					} else if (auxVarMap.containsKey(lit.negate())) {
						// auxVarMap can contain the negated literal as Key
						newAuxVar = auxVarMap.get(lit.negate());
					} else {
						// create and add new auxvar if it doesnt contain the old auxvar
						final TermVariable boolVar = mTheory.createFreshTermVariable("aux", mTheory.getSort("Bool"));
						final DPLLAtom dpll = new BooleanVarAtom(boolVar, mStackLevel);
						mBoolAtoms.put(boolVar, dpll);
						auxVarMap.put(lit, dpll);
						newAuxVar = dpll;
					}
					if (lit.getSign() == 1) {
						literal[i] = newAuxVar;
					} else {
						literal[i] = newAuxVar.negate();
					}
				}
			}
			final Clause cl = new Clause(literal, mStackLevel);
			cl.setProof(new LeafNode(-1, SourceAnnotation.EMPTY_SOURCE_ANNOT));
			result.add(cl);
		}
		return result;
	}


	/*
	 * The return values of adder and multiplier are aux vars
	 */
	private void division(final ApplicationTerm appterm, final Term[] conjunction, final Term[] encTerm) {
		final FunctionSymbol fsym = appterm.getFunction();
		final Term[] encA = mEncTerms.get(appterm.getParameters()[0]);
		final Term[] encB = mEncTerms.get(appterm.getParameters()[1]);
		final int stage =
				mTheory.toNumeral(appterm.getParameters()[1].getSort().getIndices()[0]).intValue() - 1;
		final Term[] remainder;
		final Term[] product;
		if (fsym.getName().equals("bvudiv")) {
			remainder = createBoolVarArray(conjunction.length);
			product = multiplier(encTerm, encB, stage, null);
		} else if (fsym.getName().equals("bvurem")) {
			remainder = encTerm;
			product = multiplier(createBoolVarArray(conjunction.length), encB, stage, null);
		} else {
			throw new UnsupportedOperationException(
					"Unsupported functionsymbol for bitblasting: " + fsym.getName());
		}

		final Term[] sum = adder(product, remainder, mTheory.mFalse, null).getFirst();

		// Term lhs = (encB != False);
		final Term lhs = mTheory.or(encB);
		final Term bvult =
				mTheory.not(adder(remainder, negate(encB), mTheory.mTrue, null).getSecond());
		for (int i = 0; i < conjunction.length; i++) {
			conjunction[i] = mTheory.and(
					mTheory.or(mTheory.not(sum[i]), encA[i]),
					mTheory.or(mTheory.not(encA[i]), sum[i]));
		}

		// divisionConstraint:
		final Term divisionConstraint = mTheory.or(mTheory.not(lhs), mTheory.and(conjunction));
		toClauses(divisionConstraint);

		// remainderConstraint:
		final Literal bvultLit = getLiteral(bvult);
		for (int i = 0; i < encB.length; i++) {
			final Literal lhsLit = getLiteral(encB[i]);
			final Literal[] lit1 = { bvultLit, lhsLit.negate() };
			addClause(lit1);
		}

	}

	// 00 concat 01 = 0001
	// as Array: [0 0] concat [1 0] = [1 0 0 0]
	private Term[] concatArrays(final Term[] b, final Term[] a) {
		final Term[] result = Arrays.copyOf(a, a.length + b.length);
		System.arraycopy(b, 0, result, a.length, b.length);
		return result;
	}

	// negates each term in terms array
	private Term[] negate(final Term[] terms) {
		final Term[] negateresult = new Term[terms.length];
		for (int i = 0; i < terms.length; i++) {
			negateresult[i] = mTheory.not(terms[i]);
		}
		return negateresult;
	}

	/*
	 * returns an AuxVar representing (a xor b xor cin). Clauses for this auxvar will be created and saved directly.
	 */
	private Term sumAdder(final Term aTerm, final Term bTerm, final Term cin, final Term encAdd) {
		final Literal b = getLiteral(bTerm);

		final Literal at;
		Term result;
		if (encAdd == null) { // adder was called by multiplier or similar functions
			final Term boolVar = createBoolAtom(null);
			at = getLiteral(boolVar);
			result = boolVar;
		} else {
			at = getLiteral(encAdd);
			result = encAdd;
		}

		final Literal a = getLiteral(aTerm);

		if (cin.equals(mTheory.mFalse)) {
			if (aTerm.equals(mTheory.mFalse)) {
				final Literal[] lit2 = { at, b.negate() };
				addClause(lit2);
				final Literal[] lit3 = { at.negate(), b };
				addClause(lit3);
			} else {
				final Literal[] lit2 = { at, a, b.negate() };
				addClause(lit2);
				final Literal[] lit4 = { at, a.negate(), b, };
				addClause(lit4);
				final Literal[] lit6 = { at.negate(), a, b, };
				addClause(lit6);
				final Literal[] lit7 = { at.negate(), a.negate(), b.negate() };
				addClause(lit7);
			}
		} else if (cin.equals(mTheory.mTrue)) {
			if (aTerm.equals(mTheory.mFalse)) {
				final Literal[] lit2 = { at, b };
				addClause(lit2);
				final Literal[] lit3 = { at.negate(), b.negate() };
				addClause(lit3);
			} else {
				final Literal[] lit2 = { at.negate(), a, b.negate() };
				addClause(lit2);
				final Literal[] lit4 = { at.negate(), a.negate(), b, };
				addClause(lit4);
				final Literal[] lit6 = { at, a, b, };
				addClause(lit6);
				final Literal[] lit7 = { at, a.negate(), b.negate() };
				addClause(lit7);
			}
		} else {
			final Literal c = getLiteral(cin);

			if (aTerm.equals(mTheory.mFalse)) {
				final Literal[] lit2 = { at, c, b.negate() };
				addClause(lit2);
				final Literal[] lit4 = { at, c.negate(), b, };
				addClause(lit4);
				final Literal[] lit6 = { at.negate(), c, b, };
				addClause(lit6);
				final Literal[] lit7 = { at.negate(), c.negate(), b.negate() };
				addClause(lit7);

			} else {

				final Literal[] lit1 = { at, a.negate(), b.negate(), c.negate() };
				addClause(lit1);
				final Literal[] lit2 = { at, a, b.negate(), c };
				addClause(lit2);
				final Literal[] lit3 = { at, a, b, c.negate() };
				addClause(lit3);
				final Literal[] lit4 = { at, a.negate(), b, c };
				addClause(lit4);

				final Literal[] lit5 = { at.negate(), a, b.negate(), c.negate() };
				addClause(lit5);
				final Literal[] lit6 = { at.negate(), a, b, c };
				addClause(lit6);
				final Literal[] lit7 = { at.negate(), a.negate(), b.negate(), c };
				addClause(lit7);
				final Literal[] lit8 = { at.negate(), a.negate(), b, c.negate() };
				addClause(lit8);
			}
		}
		return result;
	}

	// returns ((a and b) or (mTheory.(a xor b) and cin)) in CNF
	// cin is either false or AuxVar
	private Term carryAdder(final Term aTerm, final Term bTerm, final Term cin) {
		if (aTerm.equals(mTheory.mFalse)) {
			// TODO
			return createAuxVar(mTheory.and(mTheory.or(aTerm, bTerm), mTheory.or(aTerm, cin), mTheory.or(bTerm, cin)));
		}
		if (cin.equals(mTheory.mFalse)) {
			return createAuxVar(mTheory.and(aTerm, bTerm)); // optimize
		} else if (cin.equals(mTheory.mTrue)) {
			return createAuxVar(mTheory.or(aTerm, bTerm)); // optimize
		} else {
			// return mTheory.and(mTheory.or(aTerm, bTerm), mTheory.or(aTerm, cin), mTheory.or(bTerm, cin));
			final Literal a = getLiteral(aTerm);
			final Literal b = getLiteral(bTerm);
			final Literal c = getLiteral(cin);

			final Term boolVar = createBoolAtom(null);

			final Literal auxVar = getLiteral(boolVar);

			final Literal[] lit1 = { auxVar, a.negate(), b.negate() };
			addClause(lit1);
			final Literal[] lit2 = { auxVar, a.negate(), c.negate() };
			addClause(lit2);
			final Literal[] lit3 = { auxVar, b.negate(), c.negate() };
			addClause(lit3);

			final Literal[] lit4 = { auxVar.negate(), b, a };
			addClause(lit4);
			final Literal[] lit5 = { auxVar.negate(), a, c };
			addClause(lit5);
			final Literal[] lit6 = { auxVar.negate(), b, c };
			addClause(lit6);

			return boolVar;
		}
	}

	private Term createBoolAtom(String name) {
		if (name == null) {
			name = "AuxVar";
		}
		final TermVariable boolVar = mTheory.createFreshTermVariable(name, mTheory.getSort("Bool"));
		final DPLLAtom dpll = new BooleanVarAtom(boolVar, mStackLevel);
		mBoolAtoms.put(boolVar, dpll);
		return boolVar;
	}

	private Term[] carryBits(final Term[] encA, final Term[] encB, final Term cin) {
		assert encA.length == encB.length;
		final Term[] carryBits = new Term[encA.length + 1];
		carryBits[0] = cin;
		for (int i = 1; i <= encA.length; i++) {
			carryBits[i] = carryAdder(encA[i - 1], encB[i - 1], carryBits[i - 1]);

		}
		return carryBits;
	}

	private Pair<Term[], Term> adder(final Term[] encA, final Term[] encB, final Term cin, final Term[] encAdd) {
		assert encA.length == encB.length;
		final Term[] sumResult = new Term[encA.length];
		final Term[] carryBits = carryBits(encA, encB, cin);
		for (int i = 0; i < encA.length; i++) {
			if (encAdd != null) {
				// will create the clauses directly
				sumResult[i] = sumAdder(encA[i], encB[i], carryBits[i], encAdd[i]);
			} else {
				// won't create clauses, used in the multiplier etc.
				sumResult[i] = sumAdder(encA[i], encB[i], carryBits[i], null);
			}
		}
		final Term cout = carryBits[carryBits.length - 1];
		return new Pair<>(sumResult, cout);
	}

	// create all auxiliary variables, needed to get rid of recursions
	private Term[][] createBoolVarMap(final int stage, final int indices) {
		final Term[][] boolvarmap = new Term[stage][indices];
		for (int s = 0; s < stage; s++) {
			for (int i = 0; i < indices; i++) {
				final String stageRec = "rec_" + i + "_" + s;
				final Term boolVar = createBoolAtom(stageRec);
				boolvarmap[s][i] = boolVar;
			}
		}
		return boolvarmap;
	}


	// create all bool variables representing an bitvector
	private Term[] createBoolVarArray(final int indices) {
		final Term[] boolvarArray = new Term[indices];
		for (int i = 0; i < indices; i++) {
			final String stageRec = "aux_" + i;
			final Term boolVar = createBoolAtom(stageRec);
			boolvarArray[i] = boolVar;
		}

		return boolvarArray;
	}

	/*
	 * Check if a aux var helps in the cnf process
	 * If (appterm.getParameters().length > 1), create auxvar and add it to cnf
	 * Else return input
	 */
	private Term createAuxVar(final Term represented) {
		if (represented instanceof ApplicationTerm) {
			final ApplicationTerm appterm = (ApplicationTerm) represented;
			if (appterm.getParameters().length > 1) { // Maybe only worth, if appterm is a conjunction
				final Term boolVar = createBoolAtom(null);
				toClauses(mTheory.and(mTheory.or(mTheory.not(boolVar), represented),
						mTheory.or(mTheory.not(represented), boolVar)));
				return boolVar;
			}
		}
		//Probably not worth to add the Aux Var
		return represented;
	}


	/*
	 * Barrel Shifter
	 * Optimization: a<<b = ite(b3 \/ b4, (0,0,0,0), ls(a,b, log_2(length a) - 1))
	 * leftshift, true if bvshl. False if bvlshr
	 */
	private Term[] shift(final Term a, final Term b, int stage, final boolean leftshift) {

		final Term[] encA = mEncTerms.get(a);
		final Term[] encB = mEncTerms.get(b);
		final Term[] shiftResult = new Term[encA.length];

		// Log Base 2, rounded up
		final int logTwo = (int) Math.ceil((float) (Math.log(encA.length) / Math.log(2)));
		final Term[][] boolvarmap = createBoolVarMap(logTwo, encA.length);
		// if any enB[x] with x > log_2(encA.length) is true, then shift result is zero BitVec
		for (int i = 0; i < encA.length; i++) {
			final List<Term> disj = new ArrayList<>();
			for (int k = logTwo; k < encB.length; k++) {
				disj.add(encB[k]);
			}
			final Term disjunction = listToDisjunction(disj, false);
			shiftResult[i] = mTheory.and(mTheory.or(mTheory.not(disjunction), mTheory.mFalse),
					mTheory.or(mTheory.or(disjunction), boolvarmap[logTwo - 1][i]));
		}
		// Only consider stages smaller than maximal shift distance
		stage = logTwo;
		for (int s = 0; s < stage; s++) {
			for (int i = 0; i < encA.length; i++) {
				final int pow = (int) Math.pow(2, s);
				final Term ifTerm;
				final Term elseTerm;
				Term thenTerm;
				if (s == 0) {
					ifTerm = encB[0];
					elseTerm = encA[i];
					// rightshift
					if ((i + pow < encA.length) && !leftshift) {
						thenTerm = encA[i + pow];
						// leftshift
					} else if (i >= pow && leftshift) {
						thenTerm = encA[i - pow];
						// no shift
					} else {
						thenTerm = mTheory.mFalse;
					}
					// ifthenelse in CNF (not a or b) and (a or c)
				} else {
					ifTerm = encB[s];
					elseTerm = boolvarmap[s - 1][i];
					if ((i + pow < encA.length) && !leftshift) {
						thenTerm = boolvarmap[s - 1][i + pow];
					} else if (i >= pow && leftshift) {
						thenTerm = boolvarmap[s - 1][i - pow];
					} else {
						thenTerm = mTheory.mFalse;
					}
				}
				// Add Auxiliary variables and their represented term (ifte), as clauses
				// Save in Set to prevent douplicats?
				toClausesIte(boolvarmap[s][i], ifTerm, elseTerm, thenTerm);
			}
		}
		return shiftResult;
	}

	/*
	 * get's a list of terms,
	 * returns these terms as disjunction
	 * if negated is set to true, each disjunct will be negated
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

	/*
	 * Used, when b is not a term in the orginial formula, therefore mEncTerms.get(b) would be null
	 * No need for AuxVars since we can calculate the actual shift result
	 */
	private Term[] leftshiftMul(final Term[] encA, final String b, final int stage) {
		final Term[] shiftResult = new Term[encA.length];
		if (stage == -1) {
			return encA;
		} else {
			for (int i = 0; i < encA.length; i++) {
				if (b.charAt(b.length() - 1 - stage) == '1') {
					if (i >= Math.pow(2, stage)) {
						shiftResult[i] =
								leftshiftMul(encA, b, stage - 1)[i - (int) Math.pow(2, stage)];
					} else {
						shiftResult[i] = mTheory.mFalse;
					}
				} else {
					shiftResult[i] = leftshiftMul(encA, b, stage - 1)[i];
				}
			}
		}
		return shiftResult;
	}

	private Term[] multiplier(final Term a, final Term b, final int stage, final Term[] encMul) {
		final Term[] encA = mEncTerms.get(a);
		final Term[] encB = mEncTerms.get(b);
		return multiplier(encA, encB, stage, encMul);
	}

	/*
	 * Multiplier withouth recursion. Instead we use aux vars.
	 * returns null, if encMul was given. Then clauses will be created during the process
	 */
	private Term[] multiplier(final Term[] encA, final Term[] encB, final int stage, final Term[] encMul) {
		final int size = encA.length;
		final Term[] zeroVec = new Term[size];
		Arrays.fill(zeroVec, mTheory.mFalse);
		final Term[][] boolvarmap = createBoolVarMap(stage + 1, encA.length);
		if (stage == 0) {
			if (encMul == null) {
				return zeroVec;
			} else {
				for (int i = 0; i < size; i++) {
					final Literal result = getLiteral(encMul[i]);
					final Literal[] lit6 = { result.negate() };
					addClause(lit6);
				}
				return null;
			}
		}
		// Create AuxVars for each, except last.
		for (int s = 0; s < stage; s++) {
			final Term[] mul;
			final Term[] shift;
			if (s == 0) {
				mul = zeroVec;
				shift = encA;
			} else {
				// Auxiliary Variable
				mul = boolvarmap[s - 1];
				String SAsString = Integer.toString(s, 2);
				SAsString = new String(new char[size - SAsString.length()]).replace("\0", "0") + SAsString;
				shift = leftshiftMul(encA, SAsString, size - 1);
			}
			final Term[] ifte = new Term[size];
			for (int i = 0; i < size; i++) {
				Term t;
				if (encB[i].equals(mTheory.mTrue)) {
					t = mTheory.or(mTheory.not(encB[s]), shift[i]);
				} else if (encB[i].equals(mTheory.mFalse)) {
					t = mTheory.or(encB[s], mTheory.mFalse);
				}
				else {
					// mTheory.ifthenelse(encB[stage], shift[i], mTheory.mFalse);
					t = mTheory.and(
							mTheory.or(mTheory.not(encB[s]), shift[i]),
							mTheory.or(encB[s], mTheory.mFalse));
				}
				ifte[i] = createAuxVar(t);
			}

			adder(mul, ifte, mTheory.mFalse, boolvarmap[s]).getFirst();
		}
		// Last stage
		final Term[] shift;
		// stage must not be 0 at this point!
		String SAsString = Integer.toString(stage, 2);
		SAsString = new String(new char[size - SAsString.length()]).replace("\0", "0") + SAsString;
		shift = leftshiftMul(encA, SAsString, size - 1);

		final Term[] ifte = new Term[size];
		for (int i = 0; i < size; i++) {
			Term t;
			if (encB[i].equals(mTheory.mTrue)) {
				t = mTheory.or(mTheory.not(encB[stage]), shift[i]);
			} else if (encB[i].equals(mTheory.mFalse)) {
				t = mTheory.or(encB[stage], mTheory.mFalse);
			} else {
				// mTheory.ifthenelse(encB[stage], shift[i], mTheory.mFalse);
				t = mTheory.and(
						mTheory.or(mTheory.not(encB[stage]), shift[i]),
						mTheory.or(encB[stage], mTheory.mFalse));
			}
			ifte[i] = createAuxVar(t);
		}
		final Term[] sum = adder(boolvarmap[stage - 1], ifte, mTheory.mFalse, encMul).getFirst();
		if (encMul == null) {
			return sum;
		} else {
			return null;
		}
	}


	/*
	 * Transforms the term into cnf and collects the clauses.
	 */
	private void toClauses(final Term term) {
		final CleanTransfomer cleaner = new CleanTransfomer();
		final NnfTransformer nnf = new NnfTransformer();
		final Term nnfTerm = nnf.transform(term);
		final CnfTransformer cnf = new CnfTransformer();
		final Term cnfTerm = cnf.transform(cnf.transform(nnfTerm));
		final Term cleanTerm = cleaner.transform(cnfTerm);
		if (cleanTerm instanceof ApplicationTerm) {
			final ApplicationTerm appClean = (ApplicationTerm) cleanTerm;
			if (appClean.getFunction().getName().equals("and")) {
				for (int i = 0; i < appClean.getParameters().length; i++) {
					addClauses(appClean.getParameters()[i]);
				}
				return;
			}
		}
		addClauses(cleanTerm);

	}


	/*
	 * atom <=> ite into cnf
	 * Add Clauses of (boolVar <=> ifte) to dpll
	 * ifte arguments need to be literals
	 */
	private void toClausesIte(final Term atom, final Term ifTerm, final Term elseTerm, final Term thenTerm) {
		final Literal atomlit = getLiteral(atom);
		final Literal ifLit = getLiteral(ifTerm);
		final Literal elseLit = getLiteral(elseTerm);
		final Literal thenLit = getLiteral(thenTerm);
		if (!thenTerm.equals(mTheory.mFalse)) {
			final Literal[] lit1 = { atomlit, ifLit.negate(), thenLit.negate() };
			addClause(lit1);
			final Literal[] lit2 = { atomlit.negate(), ifLit, elseLit };
			addClause(lit2);
			final Literal[] lit3 = { atomlit.negate(), ifLit.negate(), thenLit };
			addClause(lit3);
			final Literal[] lit4 = { atomlit, elseLit.negate(), elseLit };
			addClause(lit4);
		} else {
			// thenTerm = mTheory.mFalse;
			final Literal[] lit1 = { atomlit.negate(), ifLit, elseLit };
			addClause(lit1);
			final Literal[] lit2 = { atomlit.negate(), ifLit.negate() };
			addClause(lit2);
		}
		final Literal[] lit5 = { atomlit, ifLit.negate(), ifLit };
		addClause(lit5);
		final Literal[] lit6 = { atomlit, ifLit, elseLit.negate() };
		addClause(lit6);
	}

	private Literal getLiteral(final Term term) {
		if(term instanceof ApplicationTerm) {
			final ApplicationTerm appterm = (ApplicationTerm) term;
			final FunctionSymbol fsym = appterm.getFunction();
			if (fsym.getName().equals("not")) {
				assert mBoolAtoms.containsKey(appterm.getParameters()[0]);
				return mBoolAtoms.get(appterm.getParameters()[0]).negate();
			}
		}
		assert mBoolAtoms.containsKey(term);
		return mBoolAtoms.get(term);
	}

	private void addClause(final Literal[] literal) {
		assert !(literal.length == 0);
		if (literal[0].equals(mTheory.mTrue) && literal.length == 1) {
			return;
		}
		final Clause cl = new Clause(literal, mStackLevel);
		cl.setProof(new LeafNode(-1, SourceAnnotation.EMPTY_SOURCE_ANNOT));
		mClauses.add(cl);
		mClauseCopy.add(cl);
	}

	/*
	 * term must be a disjunction or literal
	 */
	private void addClauses(final Term term) {
		assert !term.equals(mTheory.mFalse);
		if (term.equals(mTheory.mTrue)) {
			return;
		}
		final ArrayList<Literal> literals = new ArrayList<>();
		if (term instanceof ApplicationTerm) {
			final ApplicationTerm appterm = (ApplicationTerm) term;
			final FunctionSymbol fsym = appterm.getFunction();
			if (fsym.getName().equals("or")) {
				for (int i = 0; i < appterm.getParameters().length; i++) {
					literals.add(getLiteral(appterm.getParameters()[i]));
				}
			} else if (fsym.getName().equals("true")) {
				literals.add(new TrueAtom());
			} else {
				literals.add(getLiteral(term));
			}
		} else {
			literals.add(getLiteral(term));
		}

		final Clause cl = new Clause(literals.toArray(new Literal[literals.size()]), mStackLevel);
		cl.setProof(new LeafNode(-1, SourceAnnotation.EMPTY_SOURCE_ANNOT));
		mClauses.add(cl);
		mClauseCopy.add(cl);
	}

	public Collection<DPLLAtom> getBoolAtoms() {
		return mBoolAtoms.values();
	}

	public ScopedArrayList<Clause> getClauses() {
		return mClauses;
	}

	public Literal[] getNegatedInputLiterals() {
		final Literal[] lit = new Literal[mInputLiterals.size()];
		for (int i = 0; i < mInputLiterals.size(); i++) {
			lit[i] = mInputLiterals.get(i).negate();
		}
		return lit;
	}

	public HashMap<Term, Literal> getLiteralMap() {
		return mLiterals;
	}
}