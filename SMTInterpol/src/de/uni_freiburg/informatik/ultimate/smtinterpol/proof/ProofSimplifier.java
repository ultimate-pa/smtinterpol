/*
 * Copyright (C) 2009-2017 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.smtinterpol.proof;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.BitSet;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.logic.AnnotatedTerm;
import de.uni_freiburg.informatik.ultimate.logic.Annotation;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.ConstantTerm;
import de.uni_freiburg.informatik.ultimate.logic.FormulaUnLet;
import de.uni_freiburg.informatik.ultimate.logic.FunctionSymbol;
import de.uni_freiburg.informatik.ultimate.logic.LambdaTerm;
import de.uni_freiburg.informatik.ultimate.logic.QuantifiedFormula;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.SMTLIBConstants;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermTransformer;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.logic.Theory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.DefaultLogger;
import de.uni_freiburg.informatik.ultimate.smtinterpol.LogProxy;
import de.uni_freiburg.informatik.ultimate.smtinterpol.convert.SMTAffineTerm;
import de.uni_freiburg.informatik.ultimate.smtinterpol.util.SymmetricPair;

/**
 * This class simplifies SMTInterpol proof into a simpler proof format.
 *
 * @author Jochen Hoenicke
 */
public class ProofSimplifier extends TermTransformer {
	/**
	 * The SMT script (mainly used to create terms).
	 */
	Script mSkript;
	/**
	 * The proof rules creator
	 */
	ProofRules mProofRules;
	/**
	 * The logger where errors are reported.
	 */
	LogProxy mLogger;
	private final MinimalProofChecker mChecker;

	private HashMap<FunctionSymbol, LambdaTerm> mAuxDefs;

	private final static String ANNOT_PROVED = ":proved";

	/**
	 * Create a proof checker.
	 *
	 * @param script
	 *            An SMT2 script.
	 * @param logger
	 *            The logger where errors are reported.
	 */
	public ProofSimplifier(final Script script) {
		mSkript = script;
		mProofRules = new ProofRules(script.getTheory());
		mLogger = new DefaultLogger();
		mChecker = new MinimalProofChecker(mSkript, new DefaultLogger());
	}

	private Term annotateProved(final Term provedTerm, final Term proof) {
		return proof.getTheory().annotatedTerm(new Annotation[] { new Annotation(ANNOT_PROVED, provedTerm) }, proof);
	}

	private Term provedTerm(final AnnotatedTerm annotatedTerm) {
		assert annotatedTerm.getAnnotations()[0].getKey() == ANNOT_PROVED;
		return (Term) annotatedTerm.getAnnotations()[0].getValue();
	}

	private Term stripAnnotation(final Term term) {
		if (term instanceof AnnotatedTerm && ((AnnotatedTerm) term).getAnnotations()[0].getKey() == ANNOT_PROVED) {
			return ((AnnotatedTerm) term).getSubterm();
		}
		return term;
	}

	private Term subproof(final AnnotatedTerm annotatedTerm) {
		assert annotatedTerm.getAnnotations()[0].getKey() == ANNOT_PROVED;
		return annotatedTerm.getSubterm();
	}

	private boolean checkProof(final Term proof, final ProofLiteral[] expectedLits) {
		final ProofLiteral[] actual = mChecker.getProvedClause(mAuxDefs, proof);
		final HashSet<ProofLiteral> expectedSet = new HashSet<>();
		expectedSet.addAll(Arrays.asList(expectedLits));
		assert expectedSet.size() == actual.length;
		for (final ProofLiteral lit : actual) {
			assert expectedSet.contains(lit);
		}
		return true;
	}

	private Term convertResolution(final Term[] newParams) {
		Term accum = stripAnnotation(newParams[0]);
		for (int i = 1; i < newParams.length; i++) {
			final AnnotatedTerm pivotPlusProof = (AnnotatedTerm) newParams[i];
			/* Check if it is a pivot-annotation */
			assert (pivotPlusProof.getAnnotations().length == 1
					&& pivotPlusProof.getAnnotations()[0].getKey() == ":pivot")
				: "Unexpected Annotation in resolution parameter: " + pivotPlusProof;
			Term pivot = (Term) pivotPlusProof.getAnnotations()[0].getValue();
			final boolean negated = isApplication(SMTLIBConstants.NOT, pivot);
			if (negated) {
				pivot = ((ApplicationTerm) pivot).getParameters()[0];
			}
			final Term subproof = stripAnnotation(pivotPlusProof.getSubterm());

			if (negated) {
				// term occurs negated in subproof, positive in accum
				accum = mProofRules.resolutionRule(pivot, accum, subproof);
			} else {
				accum = mProofRules.resolutionRule(pivot, subproof, accum);
			}
		}
		return accum;
	}

	private Term convertClause(final Term[] newParams) {
		assert newParams.length == 1;
		assert newParams[0] instanceof AnnotatedTerm;
		// the argument is the proved clause.
		// the annots are currently discarded
		final AnnotatedTerm annotTerm = (AnnotatedTerm) newParams[0];
		return annotTerm.getSubterm();
	}

	private Term removeNot(Term proof, Term candidateTerm, boolean positive) {
		while (isApplication("not", candidateTerm)) {
			proof = mProofRules.resolutionRule(candidateTerm, positive ? proof : mProofRules.notIntro(candidateTerm),
					positive ? mProofRules.notElim(candidateTerm) : proof);
			candidateTerm = ((ApplicationTerm) candidateTerm).getParameters()[0];
			positive = !positive;
		}
		return proof;
	}

	private Term removeQuoted(Term proof, final Term quotedTerm, final Term term, final boolean polarity) {
		final Term quotedEq = proof.getTheory().term("=", quotedTerm, term);
		if (polarity) {
			proof = mProofRules.resolutionRule(term, proof, mProofRules.iffElim1(quotedEq));

		} else {
			proof = mProofRules.resolutionRule(term, mProofRules.iffElim2(quotedEq), proof);
		}
		return mProofRules.resolutionRule(quotedEq, mProofRules.delAnnot(quotedTerm), proof);
	}

	private Term convertAsserted(final Term assertedProof) {
		assert mProofRules.isProofRule(ProofRules.ASSUME, assertedProof);
		final Term assertedFormula = ((ApplicationTerm) assertedProof).getParameters()[0];
		return removeNot(assertedProof, assertedFormula, true);
	}

	private Term convertTermITE(final Term[] clause) {
		assert isApplication("=", clause[clause.length - 1]);
		Term iteTerm = ((ApplicationTerm) clause[clause.length - 1]).getParameters()[0];
		final Term goal = ((ApplicationTerm) clause[clause.length - 1]).getParameters()[1];
		final ArrayList<Term> intermediates = new ArrayList<>();
		final ArrayList<Term> proofs = new ArrayList<>();
		for (int i = 0; i < clause.length - 1; i++) {
			assert isApplication("ite", iteTerm);
			intermediates.add(iteTerm);
			final Term[] iteParams = ((ApplicationTerm) iteTerm).getParameters();
			if (clause[i] == iteParams[0]) {
				proofs.add(removeNot(mProofRules.ite2(iteTerm), iteParams[0], true));
				iteTerm = iteParams[2];
			} else {
				assert isApplication("not", clause[i]);
				assert ((ApplicationTerm) clause[i]).getParameters()[0] == iteParams[0];
				proofs.add(removeNot(mProofRules.ite1(iteTerm), iteParams[0], false));
				iteTerm = iteParams[1];
			}
		}
		assert iteTerm == goal;
		if (proofs.size() > 1) {
			final Theory t = goal.getTheory();
			// build transitivity proof
			intermediates.add(goal);
			Term proof = mProofRules.trans(intermediates.toArray(new Term[intermediates.size()]));
			for (int i = 0; i < proofs.size(); i++) {
				final Term eqTerm = t.term("=", intermediates.get(i), intermediates.get(i + 1));
				proof = mProofRules.resolutionRule(eqTerm, proofs.get(i), proof);
			}
			return proof;
		} else {
			assert proofs.size() == 1;
			return proofs.get(0);
		}
	}

	/**
	 * Check the tautology that introduces an exists.
	 *
	 * @param clause the clause to check
	 * @param subst  the substitution used in the tautology; these are currently
	 *               fresh variables.
	 * @return true iff the clause is well-formed.
	 */
	private Term convertTautForallElim(final Term[] clause, final Term[] subst) {
		// clause[0] is (not (forall ((x1...)) F )).
		// subst is (y1, ..., yn).
		// clause[1] is F [y1/x1]...[yn/xn].
		assert clause.length == 2 && isApplication("not", clause[0]);
		final Term quotedForall = ((ApplicationTerm) clause[0]).getParameters()[0];
		final Term forall = unquote(quotedForall);
		final QuantifiedFormula qf = (QuantifiedFormula) forall;
		assert qf.getQuantifier() == QuantifiedFormula.FORALL;

		// subst must contain one substitution for each variable
		assert qf.getVariables().length == subst.length;

		// peculiarity of proof format: remove quotes if substitution changes something.
		final AnnotatedTerm subproof = substituteInQuantInst(subst, qf);
		Term proof = removeNot(stripAnnotation(subproof), provedTerm(subproof), true);
		final Term quotedEq = mSkript.term(SMTLIBConstants.EQUALS, quotedForall, forall);
		proof = removeQuoted(proof, quotedForall, forall, false);
		return proof;
	}

	/**
	 * Check the tautology that introduces an exists.
	 *
	 * @param clause the clause to check
	 * @param subst  the substitution used in the tautology; these are currently
	 *               fresh variables.
	 * @return true iff the clause is well-formed.
	 */
	private Term convertTautExistsIntro(final Term[] clause, final Term[] subst) {
		// clause[0] is (exists ((x1...)) F ).
		// subst is (y1, ..., yn).
		// clause[1] is (not F [y1/x1]...[yn/xn]).
		assert clause.length == 2;
		final QuantifiedFormula qf = (QuantifiedFormula) clause[0];
		assert qf.getQuantifier() == QuantifiedFormula.EXISTS;
		final TermVariable[] universalVars = qf.getVariables();
		assert universalVars.length == subst.length;

		Term proof = mProofRules.existsIntro(subst, qf);
		// remove negations
		final FormulaUnLet unletter = new FormulaUnLet();
		final Term result = unletter.unlet(mSkript.let(universalVars, subst, qf.getSubformula()));
		proof = removeNot(proof, result, false);
		return proof;
	}

	/**
	 * Check the tautology that eliminates an exists.
	 *
	 * @param clause     the clause to check
	 * @param skolemFuns the Skolemization used in the tautology.
	 * @return true iff the clause is well-formed.
	 */
	private Term convertTautExistsElim(final Term[] clause, final Term[] skolemFuns) {
		// clause[0]: not (exists ((x...)) F
		// clause[1]: (let ((x skolem...)) F)
		assert clause.length == 2 && isApplication("not", clause[0]);
		final Term existsAtom = ((ApplicationTerm) clause[0]).getParameters()[0];
		final QuantifiedFormula qf = (QuantifiedFormula) existsAtom;
		assert qf.getQuantifier() == QuantifiedFormula.EXISTS;
		return removeNot(mProofRules.existsElim(qf), clause[1], true);
	}

	private Term convertTautIte1Helper(final Term iteAtom, final Term iteTrueCase, final boolean polarity) {
		final Term iteTrueCaseEq = iteAtom.getTheory().term("=", iteAtom, iteTrueCase);
		final Term proof = mProofRules.resolutionRule(iteTrueCaseEq, mProofRules.ite1(iteAtom),
				polarity ? mProofRules.iffElim1(iteTrueCaseEq) : mProofRules.iffElim2(iteTrueCaseEq));
		return removeNot(proof, iteTrueCase, !polarity);
	}

	private Term convertTautIte2Helper(final Term iteAtom, final Term iteFalseCase, final boolean polarity) {
		final Term iteFalseCaseEq = iteAtom.getTheory().term("=", iteAtom, iteFalseCase);
		final Term proof = mProofRules.resolutionRule(iteFalseCaseEq, mProofRules.ite2(iteAtom),
				polarity ? mProofRules.iffElim1(iteFalseCaseEq) : mProofRules.iffElim2(iteFalseCaseEq));
		return removeNot(proof, iteFalseCase, !polarity);
	}

	private Term convertTautIte(final String tautKind, final Term[] clause) {
		assert clause.length == 3;
		final boolean negated = isApplication("not", clause[0]);
		final Term iteAtom = negated ? negate(clause[0]) : clause[0];
		assert isApplication("ite", iteAtom);
		final Term[] iteParams = ((ApplicationTerm) iteAtom).getParameters();
		switch (tautKind) {
		case ":ite+1":
			// iteAtom, ~cond, ~then
			return removeNot(convertTautIte1Helper(iteAtom, iteParams[1], true), iteParams[0], false);
		case ":ite+2":
			// iteAtom, cond, ~else
			return removeNot(convertTautIte2Helper(iteAtom, iteParams[2], true), iteParams[0], true);
		case ":ite+red":
			// iteAtom, ~then, ~else
			return mProofRules.resolutionRule(iteParams[0],
					convertTautIte2Helper(iteAtom, iteParams[2], true), convertTautIte1Helper(iteAtom, iteParams[1], true));
		case ":ite-1":
			// ~iteAtom, ~cond, then
			return removeNot(convertTautIte1Helper(iteAtom, iteParams[1], false), iteParams[0], false);
		case ":ite-2":
			// ~iteAtom, cond, else
			return removeNot(convertTautIte2Helper(iteAtom, iteParams[2], false), iteParams[0], true);
		case ":ite-red": {
			// ~iteAtom, then, else
			return mProofRules.resolutionRule(iteParams[0],
					convertTautIte2Helper(iteAtom, iteParams[2], false), convertTautIte1Helper(iteAtom, iteParams[1], false));
		}
		}
		throw new AssertionError();
	}

	private Term convertTautExcludedMiddle(final String name, final Term[] clause) {
		assert clause.length == 2;
		final boolean isEqTrue = name == ":excludedMiddle1";

		// Check for the form: (+ (! (= p true) :quoted) - p) :excludedMiddle1
		// or (+ (! (= p false) :quoted) + p) :excludedMiddle2
		final Term quotedAtom = clause[0];
		final boolean isQuotedQuant = ((AnnotatedTerm) quotedAtom).getAnnotations()[0].getKey().equals(":quotedQuant");
		final Term equality = isQuotedQuant ? unquoteExpand(quotedAtom) : unquote(quotedAtom);
		assert isApplication("=", equality);
		final Term[] eqArgs = ((ApplicationTerm) equality).getParameters();
		final Term lit = clause[1];
		assert isApplication("not", lit) == isEqTrue;
		final Term atom = isEqTrue ? negate(lit) : lit;
		assert eqArgs.length == 2 && eqArgs[0] == atom && isApplication(isEqTrue ? "true" : "false", eqArgs[1]);

		// now proof equality, lit
		Term proof = isEqTrue
				? mProofRules.resolutionRule(eqArgs[1], mProofRules.trueIntro(), mProofRules.iffIntro2(equality))
				: mProofRules.resolutionRule(eqArgs[1], mProofRules.iffIntro1(equality), mProofRules.falseElim());

		final Term expandEq = mSkript.term(SMTLIBConstants.EQUALS, quotedAtom, equality);
		final Term expandProof = isQuotedQuant ? proveAuxExpand(quotedAtom, equality)
				: mProofRules.delAnnot(quotedAtom);
		proof = mProofRules.resolutionRule(equality, proof, mProofRules.iffElim1(expandEq));
		proof = mProofRules.resolutionRule(expandEq, expandProof, proof);
		proof = removeNot(proof, atom, !isEqTrue);
		return proof;
	}

	private Term convertTautElimIntro(final String ruleName, final Term[] clauseLits) {
		final String func = ruleName.substring(1, ruleName.length() - 1);
		final boolean isElim = ruleName.endsWith("-");

		Term mainAtom = clauseLits[0];
		if (isElim) {
			assert isApplication(SMTLIBConstants.NOT, clauseLits[0]);
			mainAtom = ((ApplicationTerm) clauseLits[0]).getParameters()[0];
		}
		final Term quotedAtom = mainAtom;
		final boolean isQuotedQuant = mainAtom instanceof AnnotatedTerm;
		if (isQuotedQuant) {
			mainAtom = unquoteExpand(mainAtom);
		}
		assert isApplication(func, mainAtom);
		final Term[] mainParams = ((ApplicationTerm) mainAtom).getParameters();

		int pos = -1;
		if (func.equals(SMTLIBConstants.AND) ? isElim : !isElim) {
			// An and-, or+, =>+ rule have only one additional lit
			assert clauseLits.length == 2;
			for (int i = 0; i < mainParams.length; i++) {
				final boolean negated = func.equals(SMTLIBConstants.OR)
						|| (func.equals(SMTLIBConstants.IMPLIES) && i == mainParams.length - 1);
				if (clauseLits[1] == (negated ? mSkript.term(SMTLIBConstants.NOT, mainParams[i]) : mainParams[i])) {
					pos = i;
					break;
				}
			}
			assert pos != -1;
		}
		Term proof;
		switch (ruleName) {
		case ":or+":
			proof = mProofRules.orIntro(pos, mainAtom);
			break;
		case ":or-":
			proof = mProofRules.orElim(mainAtom);
			break;
		case ":and+":
			proof = mProofRules.andIntro(mainAtom);
			break;
		case ":and-":
			proof = mProofRules.andElim(pos, mainAtom);
			break;
		case ":=>+":
			proof = mProofRules.impIntro(pos, mainAtom);
			break;
		case ":=>-":
			proof = mProofRules.impElim(mainAtom);
			break;
		default:
			throw new AssertionError();
		}
		// remove double negations
		if (func.equals(SMTLIBConstants.AND) ? isElim : !isElim) {
			// An and-, or+, =>+ rule have only one additional lit
			assert clauseLits.length == 2;
			final boolean negated = func.equals(SMTLIBConstants.OR)
					|| (func.equals(SMTLIBConstants.IMPLIES) && pos == mainParams.length - 1);
			proof = removeNot(proof, mainParams[pos], !negated);
		} else {
			for (int i = 0; i < mainParams.length; i++) {
				final boolean negated = func.equals(SMTLIBConstants.AND)
						|| (func.equals(SMTLIBConstants.IMPLIES) && i < mainParams.length - 1);
				proof = removeNot(proof, mainParams[i], !negated);
			}
		}
		if (isQuotedQuant) {
			final Term expandEq = mSkript.term(SMTLIBConstants.EQUALS, quotedAtom, mainAtom);
			if (isElim) {
				proof = mProofRules.resolutionRule(mainAtom, mProofRules.iffElim2(expandEq), proof);
			} else {
				proof = mProofRules.resolutionRule(mainAtom, proof, mProofRules.iffElim1(expandEq));
			}
			proof = mProofRules.resolutionRule(expandEq, proveAuxExpand(quotedAtom, mainAtom), proof);
		}
		return proof;
	}

	/**
	 * Check an select over store lemma for correctness. If a problem is found, an
	 * error is reported.
	 *
	 * @param clause the clause to check.
	 */
	private Term convertTautStore(final Term[] clause) {
		// Store tautology have the form
		// (@tautology (! (= (select (store a i v) i) v) :store))
		assert clause.length ==1;
		final Term eqlit = clause[0];
		assert isApplication("=", eqlit);
		final Term[] sides = ((ApplicationTerm) eqlit).getParameters();
		assert isApplication("select", sides[0]);
		final ApplicationTerm select = (ApplicationTerm) sides[0];
		final Term store = select.getParameters()[0];
		assert isApplication("store", store);
		final Term[] storeArgs = ((ApplicationTerm) store).getParameters();
		assert storeArgs[1] == select.getParameters()[1] && storeArgs[2] == sides[1];

		return mProofRules.selectStore1(storeArgs[0], storeArgs[1], storeArgs[2]);
	}

	private Term convertTautDiff(final Term[] clause) {
		// lit0: (= a b)
		// lit1: ~(= (select a (diff a b)) (select b (diff a b)))
		assert clause.length == 2;
		final Term arrEq = clause[0];
		assert isApplication("=", arrEq);
		final Term[] arrays = ((ApplicationTerm) arrEq).getParameters();
		// we could check the second equality, but the proof check in tautology will catch any problems
		return mProofRules.extDiff(arrays[0], arrays[1]);
	}

	private Term convertTautLowHigh(final String ruleName, final Term literal) {
		final Theory theory = literal.getTheory();
		final boolean isToInt = ruleName.startsWith(":toInt");
		final boolean isHigh = ruleName.endsWith("High");
		// isLow: (<= (+ (- arg0) (* d candidate) ) 0)
		// aka. (>= (- arg0 (* d candidate)) 0)
		// isHigh: (not (<= (+ (- arg0) (* d candidate) |d|) 0)
		// aka. (< (- arg0 (* d candidate)) |d|)
		// where candidate is (div arg0 d) or (to_int arg0) and d is 1 for toInt.

		final Term atom = isHigh ? negate(literal): literal;
		assert isApplication("<=", atom);
		final Term[] leArgs = ((ApplicationTerm) atom).getParameters();
		final SMTAffineTerm lhs = new SMTAffineTerm(leArgs[0]);
		assert isZero(leArgs[1]);
		assert leArgs[0].getSort().getName() == (isToInt ? "Real" : "Int");

		final String func = isToInt ? "to_int" : "div";
		// search for the toInt or div term; note that there can be several div terms in case of a nested div.
		for (final Term candidate : lhs.getSummands().keySet()) {
			if (isApplication(func, candidate)) {
				final Term[] args = ((ApplicationTerm) candidate).getParameters();
				// compute d
				final Rational d;
				SMTAffineTerm summand;
				if (isToInt) {
					d = Rational.ONE;
					summand = new SMTAffineTerm(candidate);
				} else {
					final SMTAffineTerm arg1 = new SMTAffineTerm(args[1]);
					assert arg1.isConstant();
					d = arg1.getConstant();
					assert !d.equals(Rational.ZERO);
					summand = new SMTAffineTerm(candidate);
					summand.mul(d);
				}
				// compute expected term and check that lhs equals it.
				final SMTAffineTerm expected = new SMTAffineTerm(args[0]);
				expected.negate();
				expected.add(summand);
				if (isHigh) {
					expected.add(d.abs());
				}
				if (lhs.equals(expected)) {
					Term axiomTerm;
					Term proof;
					switch (ruleName) {
					case ":toIntLow": {
						axiomTerm = theory.term(SMTLIBConstants.LEQ,
								theory.term(SMTLIBConstants.TO_REAL, candidate), args[0]);
						proof = mProofRules.toIntLow(args[0]);
						break;
					}
					case ":toIntHigh": {
						axiomTerm = theory.term(SMTLIBConstants.LT, args[0],
								theory.term(SMTLIBConstants.PLUS, theory.term(SMTLIBConstants.TO_REAL, candidate),
										Rational.ONE.toTerm(args[0].getSort())));
						proof = mProofRules.toIntHigh(args[0]);
						break;
					}
					case ":divLow": {
						axiomTerm = theory.term(SMTLIBConstants.LEQ,
								theory.term(SMTLIBConstants.MUL, args[1], candidate), args[0]);
						proof = mProofRules.divLow(args[0], args[1]);
						final Term zero = Rational.ZERO.toTerm(args[1].getSort());
						proof = res(theory.term(SMTLIBConstants.EQUALS, args[1], zero),
								proof, proveTrivialDisequality(args[1], zero));
						break;
					}
					case ":divHigh": {
						axiomTerm = theory.term(SMTLIBConstants.LT, args[0],
								theory.term(SMTLIBConstants.PLUS, theory.term(SMTLIBConstants.MUL, args[1], candidate),
										theory.term(SMTLIBConstants.ABS, args[1])));
						proof = mProofRules.divHigh(args[0], args[1]);
						final Term zero = Rational.ZERO.toTerm(args[1].getSort());
						proof = res(theory.term(SMTLIBConstants.EQUALS, args[1], zero),
								proof, proveTrivialDisequality(args[1], zero));
						break;
					}
					default:
						throw new AssertionError();
					}
					final Term realAtom = isHigh ? atom : theory.term(SMTLIBConstants.LT, leArgs[1], leArgs[0]);
					if (ruleName.equals(":divHigh")) {
						final Term realAbsD = theory.term(SMTLIBConstants.ABS, args[1]);
						final Term absD = d.abs().toTerm(args[1].getSort());
						final Term absDivisor = theory.term(SMTLIBConstants.LEQ, realAbsD, absD);
						proof = res(axiomTerm, proof, mProofRules.farkas(new Term[] {realAtom, axiomTerm, absDivisor},
								new BigInteger[] { BigInteger.ONE, BigInteger.ONE, BigInteger.ONE }));
						proof = res(absDivisor, mProofRules.eqLeq(realAbsD, absD), proof);
						proof = res(theory.term(SMTLIBConstants.EQUALS, realAbsD, absD),
								proveAbsConstant(d, args[0].getSort()), proof);
					} else {
						proof = res(axiomTerm, proof, mProofRules.farkas(new Term[] {realAtom, axiomTerm},
								new BigInteger[] { BigInteger.ONE, BigInteger.ONE }));
					}
					if (!isHigh) {
						proof = res(realAtom, mProofRules.total(leArgs[0], leArgs[1]), proof);
					}
					return proof;
				}
			}
		}
		throw new AssertionError();
	}

	private Term convertTautology(final Term taut) {
		final AnnotatedTerm annotTerm = (AnnotatedTerm) taut;
		final Term clause = annotTerm.getSubterm();
		final Term[] clauseLits;
		if (isApplication("or", clause)) {
			clauseLits = ((ApplicationTerm) clause).getParameters();
		} else {
			clauseLits = new Term[] { clause };
		}
		assert annotTerm.getAnnotations().length == 1;
		final Annotation annot = annotTerm.getAnnotations()[0];
		final String ruleName = annot.getKey();
		Term proof = null;
		switch (ruleName) {
		case ":true+":
			assert isApplication("true", clause);
			proof = mProofRules.trueIntro();
			break;
		case ":false-":
			assert isApplication("not", clause)
					&& isApplication("false", ((ApplicationTerm) clause).getParameters()[0]);
			proof = mProofRules.falseElim();
			break;
		case ":or+":
		case ":or-":
		case ":and+":
		case ":and-":
		case ":=>+":
		case ":=>-": {
			proof = convertTautElimIntro(ruleName, clauseLits);
			break;
		}
		case ":=+1": {
			assert clauseLits.length == 3;
			final Term eqTerm = clauseLits[0];
			assert isApplication("=", eqTerm);
			final Term[] eqParams = ((ApplicationTerm) eqTerm).getParameters();
			assert eqParams.length == 2;
			proof = mProofRules.iffIntro1(eqTerm);
			assert eqParams[0] == clauseLits[1];
			proof = removeNot(proof, eqParams[0], true);
			assert eqParams[1] == clauseLits[2];
			proof = removeNot(proof, eqParams[1], true);
			break;
		}
		case ":=+2": {
			assert clauseLits.length == 3;
			final Term eqTerm = clauseLits[0];
			assert isApplication("=", eqTerm);
			final Term[] eqParams = ((ApplicationTerm) eqTerm).getParameters();
			assert eqParams.length == 2;
			proof = mProofRules.iffIntro2(eqTerm);
			assert isApplication("not", clauseLits[1]);
			assert eqParams[0] == ((ApplicationTerm) clauseLits[1]).getParameters()[0];
			proof = removeNot(proof, eqParams[0], false);
			assert isApplication("not", clauseLits[2]);
			assert eqParams[1] == ((ApplicationTerm) clauseLits[2]).getParameters()[0];
			proof = removeNot(proof, eqParams[0], false);
			break;
		}
		case ":=-1": {
			assert clauseLits.length == 3;
			assert isApplication("not", clauseLits[0]);
			final Term eqTerm = ((ApplicationTerm) clauseLits[0]).getParameters()[0];
			assert isApplication("=", eqTerm);
			final Term[] eqParams = ((ApplicationTerm) eqTerm).getParameters();
			assert eqParams.length == 2;
			proof = mProofRules.iffElim1(eqTerm);
			assert eqParams[0] == clauseLits[1];
			proof = removeNot(proof, eqParams[0], true);
			assert isApplication("not", clauseLits[2]);
			assert eqParams[1] == ((ApplicationTerm) clauseLits[2]).getParameters()[0];
			proof = removeNot(proof, eqParams[1], false);
			break;
		}
		case ":=-2": {
			assert clauseLits.length == 3;
			assert isApplication("not", clauseLits[0]);
			final Term eqTerm = ((ApplicationTerm) clauseLits[0]).getParameters()[0];
			assert isApplication("=", eqTerm);
			final Term[] eqParams = ((ApplicationTerm) eqTerm).getParameters();
			assert eqParams.length == 2;
			proof = mProofRules.iffElim2(eqTerm);
			assert isApplication("not", clauseLits[1]);
			assert eqParams[0] == ((ApplicationTerm) clauseLits[1]).getParameters()[0];
			proof = removeNot(proof, eqParams[0], false);
			assert eqParams[1] == clauseLits[2];
			proof = removeNot(proof, eqParams[1], true);
			break;
		}
		case ":xor+1": {
			assert isApplication("or", clause);
			final Term quotedTerm = clauseLits[0];
			final boolean isQuotedQuant = quotedTerm instanceof AnnotatedTerm;
			final Term xorTerm = isQuotedQuant ? unquoteExpand(quotedTerm) : quotedTerm;
			assert isApplication("xor", xorTerm);
			final Term[] xorParams = ((ApplicationTerm) xorTerm).getParameters();
			proof = mProofRules.xorIntro(xorParams, new Term[] { xorParams[0] }, new Term[] { xorParams[1] });
			proof = removeNot(proof, xorParams[0], true);
			proof = removeNot(proof, xorParams[1], false);
			if (isQuotedQuant) {
				final Term expandEq = mSkript.term(SMTLIBConstants.EQUALS, quotedTerm, xorTerm);
				proof = mProofRules.resolutionRule(xorTerm, proof, mProofRules.iffElim1(expandEq));
				proof = mProofRules.resolutionRule(expandEq, proveAuxExpand(quotedTerm, xorTerm), proof);
			}
			break;
		}
		case ":xor+2": {
			assert isApplication("or", clause);
			final Term quotedTerm = clauseLits[0];
			final boolean isQuotedQuant = quotedTerm instanceof AnnotatedTerm;
			final Term xorTerm = isQuotedQuant ? unquoteExpand(quotedTerm) : quotedTerm;
			assert isApplication("xor", xorTerm);
			final Term[] xorParams = ((ApplicationTerm) xorTerm).getParameters();
			proof = mProofRules.xorIntro(xorParams, new Term[] { xorParams[1] }, new Term[] { xorParams[0] });
			proof = removeNot(proof, xorParams[0], false);
			proof = removeNot(proof, xorParams[1], true);
			if (isQuotedQuant) {
				final Term expandEq = mSkript.term(SMTLIBConstants.EQUALS, quotedTerm, xorTerm);
				proof = mProofRules.resolutionRule(xorTerm, proof, mProofRules.iffElim1(expandEq));
				proof = mProofRules.resolutionRule(expandEq, proveAuxExpand(quotedTerm, xorTerm), proof);
			}
			break;
		}
		case ":xor-1": {
			assert isApplication("or", clause);
			assert isApplication("not", clauseLits[0]);
			final Term quotedTerm = ((ApplicationTerm) clauseLits[0]).getParameters()[0];
			final boolean isQuotedQuant = quotedTerm instanceof AnnotatedTerm;
			final Term xorTerm = isQuotedQuant ? unquoteExpand(quotedTerm) : quotedTerm;
			assert isApplication("xor", xorTerm);
			final Term[] xorParams = ((ApplicationTerm) xorTerm).getParameters();
			proof = mProofRules.xorIntro(new Term[] { xorParams[0] }, new Term[] { xorParams[1] }, xorParams);
			proof = removeNot(proof, xorParams[0], true);
			proof = removeNot(proof, xorParams[1], true);
			if (isQuotedQuant) {
				final Term expandEq = mSkript.term(SMTLIBConstants.EQUALS, quotedTerm, xorTerm);
				proof = mProofRules.resolutionRule(xorTerm, mProofRules.iffElim2(expandEq), proof);
				proof = mProofRules.resolutionRule(expandEq, proveAuxExpand(quotedTerm, xorTerm), proof);
			}
			break;
		}
		case ":xor-2": {
			assert isApplication("or", clause);
			assert isApplication("not", clauseLits[0]);
			final Term quotedTerm = ((ApplicationTerm) clauseLits[0]).getParameters()[0];
			final boolean isQuotedQuant = quotedTerm instanceof AnnotatedTerm;
			final Term xorTerm = isQuotedQuant ? unquoteExpand(quotedTerm) : quotedTerm;
			assert isApplication("xor", xorTerm);
			final Term[] xorParams = ((ApplicationTerm) xorTerm).getParameters();
			proof = mProofRules.xorElim(xorParams, new Term[] { xorParams[0] }, new Term[] { xorParams[1] });
			proof = removeNot(proof, xorParams[0], false);
			proof = removeNot(proof, xorParams[1], false);
			if (isQuotedQuant) {
				final Term expandEq = mSkript.term(SMTLIBConstants.EQUALS, quotedTerm, xorTerm);
				proof = mProofRules.resolutionRule(xorTerm, mProofRules.iffElim2(expandEq), proof);
				proof = mProofRules.resolutionRule(expandEq, proveAuxExpand(quotedTerm, xorTerm), proof);
			}
			break;
		}
		case ":ite+1":
		case ":ite+2":
		case ":ite+red":
		case ":ite-1":
		case ":ite-2":
		case ":ite-red": {
			proof = convertTautIte(ruleName, clauseLits);
			break;
		}
		case ":exists-": {
			proof = convertTautExistsElim(clauseLits, (Term[]) annot.getValue());
			break;
		}
		case ":exists+": {
			proof = convertTautExistsIntro(clauseLits, (Term[]) annot.getValue());
			break;
		}
		case ":forall-": {
			proof = convertTautForallElim(clauseLits, (Term[]) annot.getValue());
			break;
		}
		case ":termITE": {
			assert isApplication("or", clause);
			proof = convertTermITE(clauseLits);
			break;
		}
		case ":trueNotFalse": {
			final Theory t = taut.getTheory();
			proof = mProofRules.resolutionRule(t.mTrue, mProofRules.trueIntro(), mProofRules.resolutionRule(t.mFalse,
					mProofRules.iffElim2(t.term("=", t.mTrue, t.mFalse)), mProofRules.falseElim()));
			break;
		}
		case ":excludedMiddle1":
		case ":excludedMiddle2":
			assert isApplication("or", clause);
			proof = convertTautExcludedMiddle(ruleName, clauseLits);
			break;
		case ":divHigh":
		case ":divLow":
		case ":toIntHigh":
		case ":toIntLow":
			proof = convertTautLowHigh(ruleName, clause);
			break;
		case ":store":
			proof = convertTautStore(clauseLits);
			break;
		case ":diff":
			proof = convertTautDiff(clauseLits);
			break;
		default: {
			proof = mProofRules.oracle(termToProofLiterals(clause), annotTerm.getAnnotations());
			break;
		}
		}
		assert checkProof(proof, termToProofLiterals(clause));
		return proof;
	}

	private Term convertMP(final Term[] newParams) {
		assert newParams.length == 2;
		assert newParams[1] instanceof AnnotatedTerm;
		// the first argument is a normal proof of a formula.
		// the second argument is a rewrite proof and annotated with the proved term.
		final AnnotatedTerm annotImp = (AnnotatedTerm) newParams[1];
		final Term implicationTerm = (ApplicationTerm) annotImp.getAnnotations()[0].getValue();
		final boolean isEquality = isApplication(SMTLIBConstants.EQUALS, implicationTerm);
		assert isEquality || isApplication(SMTLIBConstants.IMPLIES, implicationTerm);
		Term lhsTerm = ((ApplicationTerm) implicationTerm).getParameters()[0];
		final Term rhsTerm = ((ApplicationTerm) implicationTerm).getParameters()[1];

		final Term impElim = isEquality ? mProofRules.iffElim2(implicationTerm)
				: mProofRules.impElim(implicationTerm);
		final Term impClause = mProofRules.resolutionRule(implicationTerm, annotImp.getSubterm(),
				removeNot(impElim, lhsTerm, false));
		boolean positive = true;
		while (isApplication("not", lhsTerm)) {
			lhsTerm = ((ApplicationTerm) lhsTerm).getParameters()[0];
			positive = !positive;
		}
		return removeNot(mProofRules.resolutionRule(lhsTerm, positive ? newParams[0] : impClause,
				positive ? impClause : newParams[0]), rhsTerm, true);
	}

	private Term convertTrans(final Term[] newParams) {
		final Term[] intermediateTerms = new Term[newParams.length + 1];
		Term lastTerm = null;
		for (int i = 0; i < newParams.length; i++) {
			final ApplicationTerm provedEq = (ApplicationTerm) provedTerm((AnnotatedTerm) newParams[i]);
			assert isApplication(SMTLIBConstants.EQUALS, provedEq);
			assert provedEq.getParameters().length == 2;
			assert i == 0 || lastTerm == provedEq.getParameters()[0];
			intermediateTerms[i] = provedEq.getParameters()[0];
			lastTerm = provedEq.getParameters()[1];
		}
		intermediateTerms[newParams.length] = lastTerm;
		Term clause = mProofRules.trans(intermediateTerms);
		for (int i = 0; i < newParams.length; i++) {
			final ApplicationTerm provedEq = (ApplicationTerm) provedTerm((AnnotatedTerm) newParams[i]);
			final Term subproof = subproof((AnnotatedTerm) newParams[i]);
			clause = mProofRules.resolutionRule(provedEq, subproof, clause);
		}
		final Term provedTerm = clause.getTheory().term(SMTLIBConstants.EQUALS, intermediateTerms[0],
				intermediateTerms[newParams.length]);
		return annotateProved(provedTerm, clause);
	}

	private Term convertCong(final Term[] newParams) {
		final ApplicationTerm leftEquality = (ApplicationTerm) provedTerm((AnnotatedTerm) newParams[0]);
		final Theory t = newParams[0].getTheory();
		assert isApplication(SMTLIBConstants.EQUALS, leftEquality);
		final ApplicationTerm oldFunc = (ApplicationTerm) leftEquality.getParameters()[1];
		final Term[] oldFuncParams = oldFunc.getParameters();
		final Term[] newFuncParams = oldFuncParams.clone();
		final Term[] newLit = new Term[oldFuncParams.length];
		final Term[] newLitProof = new Term[oldFuncParams.length];
		int pos = 1;
		for (int i = 0; i < oldFuncParams.length; i++) {
			// check if we rewrite this argument
			if (pos < newParams.length) {
				final ApplicationTerm provedEquality = (ApplicationTerm) provedTerm((AnnotatedTerm) newParams[pos]);
				assert isApplication(SMTLIBConstants.EQUALS, provedEquality);
				if (provedEquality.getParameters()[0] == oldFuncParams[i]) {
					// we rewrite the argument
					newFuncParams[i] = provedEquality.getParameters()[1];
					newLit[i] = provedEquality;
					newLitProof[i] = subproof((AnnotatedTerm) newParams[pos]);
					pos++;
					continue;
				}
			}
			// use reflexivity by default
			newLit[i] = t.term(SMTLIBConstants.EQUALS, oldFuncParams[i], oldFuncParams[i]);
			newLitProof[i] = mProofRules.refl(oldFuncParams[i]);
		}
		assert pos == newParams.length;

		final Term newFunc = t.term(oldFunc.getFunction(), newFuncParams);
		final Term congEquality = t.term(SMTLIBConstants.EQUALS, oldFunc, newFunc);
		Term proof = mProofRules.cong(oldFunc, newFunc);
		final HashSet<Term> eliminated = new HashSet<>();
		for (int i = 0; i < newFuncParams.length; i++) {
			if (!eliminated.contains(newLit[i])) {
				proof = mProofRules.resolutionRule(newLit[i], newLitProof[i], proof);
				eliminated.add(newLit[i]);
			}
		}
		// build transitivity with left equality, unless it is a reflexivity
		if (leftEquality.getParameters()[0] != leftEquality.getParameters()[1]) {
			Term transProof = mProofRules.trans(leftEquality.getParameters()[0], oldFunc, newFunc);
			transProof = mProofRules.resolutionRule(leftEquality, subproof((AnnotatedTerm) newParams[0]), transProof);
			proof = mProofRules.resolutionRule(congEquality, proof, transProof);
		}
		return annotateProved(t.term(SMTLIBConstants.EQUALS, leftEquality.getParameters()[0], newFunc), proof);
	}

	private Term convertRewriteIntern(final Term lhs, final Term rhs) {
		final Theory theory = lhs.getTheory();
		// simple case first
		if (rhs == lhs) {
			return mProofRules.refl(lhs);
		}

		// term x can be rewritten to (not (! (= x false) :quoted))
		if (isApplication("not", rhs)) {
			final Term quotedAtom = negate(rhs);
			if (quotedAtom instanceof AnnotatedTerm) {
				final Term unquotedAtom = unquote(quotedAtom);
				if (isApplication("=", unquotedAtom)) {
					final ApplicationTerm rhsApp = (ApplicationTerm) unquotedAtom;
					if (isApplication("false", rhsApp.getParameters()[1])
							&& lhs == rhsApp.getParameters()[0]) {
						final Term rhsLit = theory.term("not", rhsApp);
						final Term lhsEqRhsLit = theory.term("=", lhs, rhsLit);
						Term proofLhsEqRhsLit;
						Term proofUnquote = mProofRules.resolutionRule(theory.term("=", quotedAtom, unquotedAtom),
								mProofRules.delAnnot(quotedAtom), mProofRules.symm(unquotedAtom, quotedAtom));
						final Term falseTerm = rhsApp.getParameters()[1];
						proofLhsEqRhsLit = proveIff(lhsEqRhsLit,
								mProofRules.resolutionRule(rhsApp, mProofRules.notIntro(rhsLit), mProofRules.iffElim2(rhsApp)),
								mProofRules.resolutionRule(rhsApp, mProofRules.iffIntro1(rhsApp), mProofRules.notElim(rhsLit)));
						proofLhsEqRhsLit = mProofRules.resolutionRule(falseTerm, proofLhsEqRhsLit, mProofRules.falseElim());
						proofUnquote = mProofRules.resolutionRule(theory.term("=", unquotedAtom, quotedAtom), proofUnquote,
								mProofRules.cong(rhsLit, rhs));
						return mProofRules.resolutionRule(theory.term("=", lhs, rhsLit), proofLhsEqRhsLit,
								mProofRules.resolutionRule(theory.term("=", rhsLit, rhs), proofUnquote,
										mProofRules.trans(lhs, rhsLit, rhs)));
					}
				}
			}
		}

		if (rhs instanceof AnnotatedTerm) {
			final Term unquoteRhs = unquote(rhs);

			/* check for quoted auxiliary literals */
			if (lhs == unquoteRhs) {
				return mProofRules.resolutionRule(theory.term("=", rhs, lhs), mProofRules.delAnnot(rhs),
						mProofRules.symm(lhs, rhs));
			}

			/* second case: boolean functions are created as equality with true */
			if (isApplication("=", unquoteRhs)) {
				final Term[] rhsArgs = ((ApplicationTerm) unquoteRhs).getParameters();
				if (rhsArgs.length == 2 && isApplication("true", rhsArgs[1])) {
					/* check if we need to expand an @aux application */
					final boolean needsExpand = lhs != rhsArgs[0] && (rhsArgs[0] instanceof ApplicationTerm
							&& mAuxDefs.containsKey(((ApplicationTerm) rhsArgs[0]).getFunction()));
					if (needsExpand || lhs == rhsArgs[0]) {
						final Term transitivity = needsExpand ? mProofRules.trans(lhs, rhsArgs[0], unquoteRhs, rhs)
								: mProofRules.trans(lhs, unquoteRhs, rhs);

						final Term equality2 = theory.term("=", unquoteRhs, rhs);
						final Term proof2 = mProofRules.resolutionRule(theory.term("=", rhs, unquoteRhs),
								mProofRules.delAnnot(rhs), mProofRules.symm(unquoteRhs, rhs));

						final Term equality1 = theory.term("=", rhsArgs[0], unquoteRhs);
						final Term proof1 = mProofRules.resolutionRule(rhsArgs[1], mProofRules.trueIntro(),
								mProofRules.resolutionRule(rhsArgs[0],
										mProofRules.resolutionRule(unquoteRhs, mProofRules.iffIntro1(equality1),
												mProofRules.iffElim1(unquoteRhs)),
										mProofRules.resolutionRule(unquoteRhs, mProofRules.iffIntro2(unquoteRhs),
												mProofRules.iffIntro2(equality1))));
						Term proof = mProofRules.resolutionRule(equality1, proof1,
								mProofRules.resolutionRule(equality2, proof2, transitivity));
						if (needsExpand) {
							proof = mProofRules
									.resolutionRule(theory.term("=", lhs, rhsArgs[0]),
											mProofRules.resolutionRule(theory.term("=", rhsArgs[0], lhs),
													mProofRules.expand(rhsArgs[0]), mProofRules.symm(lhs, rhsArgs[0])),
											proof);
						}
						return proof;
					}
				}
			}
		}

		if (isApplication("<=", lhs)) {
			final Term[] lhsParams = ((ApplicationTerm) lhs).getParameters();
			assert isZero(lhsParams[1]);
			return proveRewriteWithLeq(lhs, rhs, true);
		}

		// eq is rewritten to quotedCC
		if (isApplication("=", lhs)) {
			/* compute affine term for lhs */
			final Term[] lhsParams = ((ApplicationTerm) lhs).getParameters();
			assert lhsParams.length == 2;

			// check rewrites for trivial disequality / equality.
			if (isApplication("false", rhs)) {
				final Term proofNotLhs = proveTrivialDisequality(lhsParams[0], lhsParams[1]);
				return mProofRules.resolutionRule(rhs,
						mProofRules.resolutionRule(lhs, mProofRules.iffIntro1(theory.term("=", lhs, rhs)), proofNotLhs),
						mProofRules.falseElim());
			} else if (isApplication("true", rhs)) {
				// since we canonicalize SMTAffineTerms, they can only be equal if they are
				// identical.
				assert lhsParams[0] == lhsParams[1];
				return mProofRules.resolutionRule(rhs, mProofRules.trueIntro(), mProofRules.resolutionRule(lhs,
						mProofRules.refl(lhsParams[0]), mProofRules.iffIntro2(theory.term("=", lhs, rhs))));
			}

			final Term unquoteRhs = unquote(rhs);
			final Term equality2 = theory.term("=", unquoteRhs, rhs);
			final Term proof2 = mProofRules.resolutionRule(theory.term("=", rhs, unquoteRhs),
					mProofRules.delAnnot(rhs), mProofRules.symm(unquoteRhs, rhs));

			assert isApplication("=", unquoteRhs);
			final Term[] rhsParams = ((ApplicationTerm) unquoteRhs).getParameters();
			assert rhsParams.length == 2;

			if (lhs == unquoteRhs) {
				// lhs and rhs are the same (modulo quote)
				return proof2;
			}

			final Term equality1 = theory.term("=", lhs, unquoteRhs);
			Term proof1;
			if (lhsParams[1] == rhsParams[0] && lhsParams[0] == rhsParams[1]) {
				// lhs and rhs are only swapped
				proof1 = proveIff(equality1, mProofRules.symm(rhsParams[0], rhsParams[1]),
						mProofRules.symm(lhsParams[0], lhsParams[1]));
			} else {
				// Now it must be an LA equality that got normalized in a different way.
				assert lhsParams[0].getSort().isNumericSort();
				proof1 = proveRewriteWithLinEq(lhs, unquoteRhs);
			}
			return mProofRules.resolutionRule(equality1, proof1,
					mProofRules.resolutionRule(equality2, proof2, mProofRules.trans(lhs, unquoteRhs, rhs)));
		}
		throw new AssertionError();
	}

	private Term convertRewriteLeq(final String rewriteRule, final Term rewrite, final Term lhs, final Term rhs) {
		// (<= c 0) --> true/false if c is constant.
		assert isApplication("<=", lhs);
		final Term[] params = ((ApplicationTerm) lhs).getParameters();
		assert params.length == 2 && isZero(params[1]);
		final Rational param0 = SMTAffineTerm.convertConstant((ConstantTerm) params[0]);
		final boolean isTrue = rewriteRule == ":leqTrue";
		if (isTrue) {
			assert param0.signum() <= 0 && isApplication("true", rhs);
			final Term falseLhs = lhs.getTheory().term("<", params[1], params[0]);
			return proveIffTrue(rewrite,
					mProofRules.resolutionRule(falseLhs, mProofRules.total(params[0], params[1]),
							mProofRules.farkas(new Term[] { falseLhs }, new BigInteger[] { BigInteger.ONE })));
		} else {
			assert param0.signum() > 0 && isApplication("false", rhs);
			return proveIffFalse(rewrite, mProofRules.farkas(new Term[] { lhs }, new BigInteger[] { BigInteger.ONE }));
		}
	}

	private Term convertRewriteNot(final Term rewrite, final Term lhs, final Term rhs) {
		// lhs: (not lhsAtom)
		assert isApplication("not", lhs);
		final Term lhsAtom = ((ApplicationTerm) lhs).getParameters()[0];
		if (isApplication("false", lhsAtom)) {
			// not false = true
			assert isApplication("true", rhs);
			return proveIffTrue(rewrite,
					mProofRules.resolutionRule(lhsAtom, mProofRules.notIntro(lhs), mProofRules.falseElim()));
		}
		if (isApplication("true", lhsAtom)) {
			// not true = false
			assert isApplication("false", rhs);
			return proveIffFalse(rewrite,
					mProofRules.resolutionRule(lhsAtom, mProofRules.trueIntro(), mProofRules.notElim(lhs)));
		}
		if (isApplication("not", lhsAtom)) {
			// not (not x) = x
			assert rhs == ((ApplicationTerm) lhsAtom).getParameters()[0];
			return proveIff(rewrite,
					mProofRules.resolutionRule(lhsAtom, mProofRules.notIntro(lhsAtom), mProofRules.notElim(lhs)),
					mProofRules.resolutionRule(lhsAtom, mProofRules.notIntro(lhs), mProofRules.notElim(lhsAtom)));
		}
		throw new AssertionError();
	}

	private Term convertRewriteTrueNotFalse(final Term lhs, final Term rhs) {
		// expect lhs: (= ... true ... false ...)), rhs: false
		final Theory t = lhs.getTheory();
		assert isApplication("=", lhs) && isApplication("false", rhs);
		final Term[] lhsParams = ((ApplicationTerm) lhs).getParameters();
		int trueIdx = -1, falseIdx = -1;
		for (int i = 0; i < lhsParams.length; i++) {
			final Term term = lhsParams[i];
			if (isApplication("true", term)) {
				trueIdx = i;
			}
			if (isApplication("false", term)) {
				falseIdx = i;
			}
		}
		assert trueIdx >= 0 && falseIdx >= 0;
		Term clause;
		final Term trueEqFalse = t.term(SMTLIBConstants.EQUALS, lhsParams[trueIdx], lhsParams[falseIdx]);
		clause = mProofRules.resolutionRule(trueEqFalse, mProofRules.equalsElim(trueIdx, falseIdx, lhs),
				mProofRules.iffElim2(trueEqFalse));
		clause = mProofRules.resolutionRule(lhs, mProofRules.iffIntro1(t.term(SMTLIBConstants.EQUALS, lhs, rhs)),
				clause);
		clause = mProofRules.resolutionRule(lhsParams[falseIdx],
				mProofRules.resolutionRule(lhsParams[trueIdx], mProofRules.trueIntro(), clause),
				mProofRules.falseElim());
		return clause;
	}

	Term convertRewriteEqTrueFalse(final String rewriteRule, final Term lhs, final Term rhs) {
		// lhs: (= l1 true ln), rhs: (not (or (not l1) ... (not ln)))
		// lhs: (= l1 false ln), rhs: (not (or l1 ... ln))
		// duplicated entries in lhs should be removed in rhs.
		final boolean trueCase = rewriteRule.equals(":eqTrue");
		assert isApplication("=", lhs);
		int trueFalseIdx = -1;
		final Term[] params = ((ApplicationTerm) lhs).getParameters();
		final LinkedHashSet<Integer> args = new LinkedHashSet<>();
		for (int i = 0; i < params.length; i++) {
			final Term t = params[i];
			if (isApplication(trueCase ? "true" : "false", t)) {
				trueFalseIdx = i;
			} else {
				args.add(i);
			}
		}
		assert trueFalseIdx >= 0;
		final Theory theo = lhs.getTheory();

		final Term rewrite = theo.term(SMTLIBConstants.EQUALS, lhs, rhs);
		Term proofRhs = null;
		final Term rhsAtom = ((ApplicationTerm) rhs).getParameters()[0];
		if (args.size() > 1 || !trueCase) {
			assert isApplication(SMTLIBConstants.NOT, rhs);
			proofRhs = mProofRules.notIntro(rhs);
			if (args.size() > 1) {
				assert isApplication(SMTLIBConstants.OR, rhsAtom);
				proofRhs = res(rhsAtom, proofRhs, mProofRules.orElim(rhsAtom));
			}
		}
		Term proofLhs = params.length > 2 ? mProofRules.equalsIntro(lhs) : null;
		for (int i = 0; i < params.length - 1; i++) {
			final Term equality = theo.term(SMTLIBConstants.EQUALS, params[i], params[i+1]);
			final Term iffIntro = trueCase ? mProofRules.iffIntro2(equality) : mProofRules.iffIntro1(equality);
			proofLhs = res(equality, iffIntro, proofLhs);
		}
		// proofRhs: (not? l1), ..., (not? ln), rhs.
		// proofLhs: ~true/false, ~? l1,...,~? ln, lhs.
		// introduce all distinct arguments
		int orPos = 0;
		for (final int pos : args) {
			final Term arg = params[pos];
			final Term notArg = theo.term(SMTLIBConstants.NOT, arg);
			final Term orArg = trueCase ? notArg : arg;
			if (args.size() > 1) {
				if (trueCase) {
					proofRhs = res(notArg, proofRhs, mProofRules.notElim(notArg));
					proofLhs = res(arg, mProofRules.notIntro(notArg), proofLhs);
				}
				proofLhs = res(orArg, proofLhs, mProofRules.orIntro(orPos++, rhsAtom));
			}
			final Term argTrueFalse = theo.term(SMTLIBConstants.EQUALS, arg, params[trueFalseIdx]);
			proofRhs = trueCase ? res(arg, mProofRules.iffElim1(argTrueFalse), proofRhs)
					: res(arg, proofRhs, mProofRules.iffElim2(argTrueFalse));
			final Term equalsElim = params.length > 2 ? mProofRules.equalsElim(pos, trueFalseIdx, lhs)
					: trueFalseIdx == 1 ? null : mProofRules.symm(params[1], params[0]);
			proofRhs = res(argTrueFalse, equalsElim, proofRhs);
		}
		if (args.size() > 1 || !trueCase) {
			proofLhs = res(rhsAtom, proofLhs, mProofRules.notElim(rhs));
		}
		// proofLhs: ~true/false, ~rhs, lhs.
		// proofRhs: ~true/false, ~lhs, rhs.
		final Term proof = proveIff(rewrite, proofRhs, proofLhs);
		return trueCase ? res(params[trueFalseIdx], mProofRules.trueIntro(), proof)
				: res(params[trueFalseIdx], proof, mProofRules.falseElim());
	}

	private Term convertRewriteToXor(final String rule, final Term rewrite, final Term lhs, final Term rhs) {
		// expect lhs: (=/distinct a b), rhs: (not? (xor a b))
		assert isApplication(rule == ":eqToXor" ? "=" : "distinct", lhs);
		Term xorTerm = rhs;
		if (rule == ":eqToXor") {
			xorTerm = negate(xorTerm);
		}
		assert isApplication("xor", xorTerm);
		final Term[] eqParams = ((ApplicationTerm) lhs).getParameters();
		final Term[] xorParams = ((ApplicationTerm) xorTerm).getParameters();
		assert xorParams.length == 2 && eqParams.length == 2;
		assert xorParams[0] == eqParams[0] && xorParams[1] == eqParams[1];
		final Term eqLhs = rewrite.getTheory().term("=", eqParams[0], eqParams[1]);
		final Term proofEqToNotXor = mProofRules.resolutionRule(eqParams[0],
				mProofRules.resolutionRule(eqParams[1],
						mProofRules.xorIntro(new Term[] { xorParams[0] }, new Term[] { xorParams[1] }, xorParams),
						mProofRules.iffElim1(eqLhs)),
				mProofRules.resolutionRule(eqParams[1], mProofRules.iffElim2(eqLhs),
						mProofRules.xorElim(new Term[] { xorParams[0] }, new Term[] { xorParams[1] }, xorParams)));
		final Term proofNotXorToEq = mProofRules.resolutionRule(eqParams[0],
				mProofRules.resolutionRule(eqParams[1], mProofRules.iffIntro1(eqLhs),
						mProofRules.xorIntro(xorParams, new Term[] { xorParams[0] }, new Term[] { xorParams[1] })),
				mProofRules.resolutionRule(eqParams[1],
						mProofRules.xorIntro(xorParams, new Term[] { xorParams[1] }, new Term[] { xorParams[0] }),
						mProofRules.iffIntro2(eqLhs)));
		final Term iffIntro1, iffIntro2;
		if (rule == ":eqToXor") {
			iffIntro1 = mProofRules.resolutionRule(rhs, mProofRules.iffIntro1(rewrite), mProofRules.notElim(rhs));
			iffIntro2 = mProofRules.resolutionRule(rhs, mProofRules.notIntro(rhs), mProofRules.iffIntro2(rewrite));
		} else {
			iffIntro1 = mProofRules.resolutionRule(lhs, mProofRules.distinctIntro(lhs),
					mProofRules.iffIntro2(rewrite));
			iffIntro2 = mProofRules.resolutionRule(lhs, mProofRules.iffIntro1(rewrite),
					mProofRules.distinctElim(0, 1, lhs));
		}
		return mProofRules.resolutionRule(eqLhs, mProofRules.resolutionRule(xorTerm, proofNotXorToEq, iffIntro1),
				mProofRules.resolutionRule(xorTerm, iffIntro2, proofEqToNotXor));
	}

	private Term convertRewriteXorNot(final Term rewrite, final Term lhs, final Term rhs) {
		// lhs: (xor (not? arg0) (not? arg1)), rhs: (not? (xor arg0 arg1))
		final Theory theory = rewrite.getTheory();
		boolean rhsNegated = false;
		Term rhsAtom = rhs;
		if (isApplication("not", rhs)) {
			rhsNegated = !rhsNegated;
			rhsAtom = ((ApplicationTerm) rhs).getParameters()[0];
		}
		assert isApplication("xor", lhs) && isApplication("xor", rhsAtom);
		final Term[] lhsArgs = ((ApplicationTerm) lhs).getParameters();
		final Term[] rhsArgs = ((ApplicationTerm) rhsAtom).getParameters();
		final ArrayList<Term> pairs = new ArrayList<>();
		assert lhsArgs.length == rhsArgs.length;

		Term[] xorAllArgs = null;
		Term xorAll = null;
		Term proofXorAll = null;
		boolean polarity = false;
		// Build xorAll = xor(~p1, p1,...) for all literals negatedin lhs.
		// Build proof for polarity * xorAll.
		for (int i = 0; i < lhsArgs.length; i++) {
			// If lhsArg contains not, remove it, and switch polarity.
			// Then check it equals the corresponding rhsArg
			final Term lhsArg = lhsArgs[i];
			final Term rhsArg = rhsArgs[i];
			if (isApplication("not", lhsArg)) {
				// prove +(xor lhsArgs[i] rhsArgs[i])
				final Term[] xorNotArgs = new Term[] { lhsArg, rhsArg };
				final Term xorNot = theory.term("xor", xorNotArgs);
				final Term proofXorNot = mProofRules.resolutionRule(rhsArg,
						mProofRules.resolutionRule(lhsArg, mProofRules.notIntro(lhsArg),
								mProofRules.xorIntro(xorNotArgs, new Term[] { rhsArg }, new Term[] { lhsArg })),
						mProofRules.resolutionRule(lhsArg,
								mProofRules.xorIntro(xorNotArgs, new Term[] { lhsArg }, new Term[] { rhsArg }),
								mProofRules.notElim(lhsArg)));
				pairs.add(lhsArg);
				pairs.add(rhsArg);
				final Term[] xorAllNextArgs = pairs.toArray(new Term[pairs.size()]);
				final Term xorAllNext = theory.term("xor", xorAllNextArgs);
				// Now compute the proof for !polarity * xorAllNext
				if (proofXorAll == null) {
					proofXorAll = proofXorNot;
				} else {
					Term proofStep = polarity
							? mProofRules.xorElim(xorAllNextArgs, xorAllArgs, xorNotArgs)
							: mProofRules.xorIntro(xorAllNextArgs, xorAllArgs, xorNotArgs);
					proofStep = mProofRules.resolutionRule(xorNot, proofXorNot, proofStep);
					proofXorAll = mProofRules.resolutionRule(xorAll,
							polarity ? proofXorAll : proofStep,
							polarity ? proofStep : proofXorAll);
				}
				xorAllArgs = xorAllNextArgs;
				xorAll = xorAllNext;
				polarity = !polarity;
				assert rhsArg == ((ApplicationTerm) lhsArg).getParameters()[0];
			} else {
				assert rhsArg == lhsArg;
			}
		}
		assert pairs.size() > 0;
		// The lemma is well-formed if all nots cancel out.
		assert rhsNegated == polarity;

		Term proof1, proof2;
		proof1 = mProofRules.xorIntro(lhsArgs, rhsNegated ? rhsArgs : xorAllArgs, rhsNegated ? xorAllArgs : rhsArgs);
		proof2 = rhsNegated ? mProofRules.xorElim(rhsArgs, xorAllArgs, lhsArgs)
				: mProofRules.xorIntro(rhsArgs, xorAllArgs, lhsArgs);
		if (rhsNegated) {
			proof1 = mProofRules.resolutionRule(rhsAtom, proof1, mProofRules.notElim(rhs));
			proof2 = mProofRules.resolutionRule(rhsAtom, mProofRules.notIntro(rhs), proof2);
		}

		final Term proof = mProofRules.resolutionRule(lhs,
				mProofRules.resolutionRule(rhs, mProofRules.iffIntro1(rewrite),
						proof1),
				mProofRules.resolutionRule(rhs, proof2, mProofRules.iffIntro2(rewrite)));
		return mProofRules.resolutionRule(xorAll, polarity ? proofXorAll : proof, polarity ? proof : proofXorAll);
	}

	private Term convertRewriteXorConst(final String rewriteRule, final Term rewrite, final Term lhs, final Term rhs) {
		// lhs: (xor true/false arg1) or (xor arg0 true/false)
		assert isApplication("xor", lhs);
		final boolean isTrue = rewriteRule == ":xorTrue";
		final Term[] xorArgs = ((ApplicationTerm) lhs).getParameters();
		final int constIdx = isApplication(isTrue ? "true" : "false", xorArgs[0]) ? 0 : 1;
		final Term[] constArg = new Term[] { xorArgs[constIdx] };
		final Term[] otherArg = new Term[] { xorArgs[1 - constIdx] };
		if (isTrue) {
			assert isApplication("true", xorArgs[constIdx]) && rhs == mSkript.term("not", xorArgs[1 - constIdx]);
			final Term proof = proveIff(rewrite,
					mProofRules.resolutionRule(xorArgs[1 - constIdx], mProofRules.notIntro(rhs),
							mProofRules.xorElim(otherArg, xorArgs, constArg)),
					mProofRules.resolutionRule(xorArgs[1 - constIdx],
							mProofRules.xorIntro(otherArg, xorArgs, constArg), mProofRules.notElim(rhs)));
			return mProofRules.resolutionRule(xorArgs[constIdx], mProofRules.trueIntro(), proof);
		} else {
			assert isApplication("false", xorArgs[constIdx]) && rhs == xorArgs[1 - constIdx];
			final Term proof = proveIff(rewrite,
					mProofRules.xorIntro(otherArg, constArg, xorArgs),
					mProofRules.xorIntro(xorArgs, constArg, otherArg));
			return mProofRules.resolutionRule(xorArgs[constIdx], proof, mProofRules.falseElim());
		}
	}

	private Term convertRewriteXorSame(final Term rewrite, final Term lhs, final Term rhs) {
		assert isApplication("xor", lhs);
		final Term[] lhsArgs = ((ApplicationTerm) lhs).getParameters();
		assert lhsArgs.length == 2 && lhsArgs[0] == lhsArgs[1] && isApplication("false", rhs);
		return proveIffFalse(rewrite, mProofRules.xorElim(lhsArgs, lhsArgs, lhsArgs));
	}

	private Term convertRewriteEqSimp(final String rewriteRule, final Term rewrite, final Term lhs, final Term rhs) {
		// lhs: (= ...), rhs: (= ...) or true, if all entries in rhs are the same.
		// duplicated entries in lhs should be removed in rhs.
		assert isApplication("=", lhs);
		final Theory theory = rewrite.getTheory();
		final Term[] lhsParams = ((ApplicationTerm) lhs).getParameters();
		final LinkedHashMap<Term, Integer> lhsTerms = new LinkedHashMap<>();
		for (int i = 0; i < lhsParams.length; i++) {
			lhsTerms.put(lhsParams[i], i);
		}
		if (lhsTerms.size() == 1) {
			assert rewriteRule.equals(":eqSame") && isApplication("true", rhs);
			Term proof = mProofRules.resolutionRule(rhs, mProofRules.trueIntro(),
					mProofRules.iffIntro2(rewrite));
			Term reflexivity = lhs;
			if (lhsParams.length > 2) {
				reflexivity = theory.term("=", lhsParams[0], lhsParams[0]);
				proof = mProofRules.resolutionRule(lhs, mProofRules.equalsIntro(lhs), proof);
			}
			proof = mProofRules.resolutionRule(reflexivity, mProofRules.refl(lhsParams[0]), proof);
			return proof;
		} else {
			assert rewriteRule.equals(":eqSimp");
			assert isApplication("=", rhs);
			final Term[] rhsParams = ((ApplicationTerm) rhs).getParameters();
			assert rhsParams.length == lhsTerms.size();

			final LinkedHashMap<Term, Integer> rhsTerms = new LinkedHashMap<>();
			for (int i = 0; i < rhsParams.length; i++) {
				rhsTerms.put(rhsParams[i], i);
			}

			Term proofLhsToRhs = mProofRules.equalsIntro(rhs);
			final HashSet<Term> seen = new HashSet<>();
			for (int i = 0; i < rhsParams.length - 1; i++) {
				final Term eq = theory.term("=", rhsParams[i], rhsParams[i + 1]);
				if (seen.add(eq)) {
					proofLhsToRhs = mProofRules.resolutionRule(eq,
							mProofRules.equalsElim(lhsTerms.get(rhsParams[i]), lhsTerms.get(rhsParams[i + 1]), lhs),
							proofLhsToRhs);
				}
			}
			seen.clear();
			Term proofRhsToLhs = mProofRules.equalsIntro(lhs);
			for (int i = 0; i < lhsParams.length - 1; i++) {
				final Term eq = theory.term("=", lhsParams[i], lhsParams[i + 1]);
				if (seen.add(eq)) {
					proofRhsToLhs = mProofRules.resolutionRule(eq,
							mProofRules.equalsElim(rhsTerms.get(lhsParams[i]), rhsTerms.get(lhsParams[i + 1]), rhs),
						proofRhsToLhs);
				}
			}
			return mProofRules.resolutionRule(rhs,
					mProofRules.resolutionRule(lhs, mProofRules.iffIntro1(rewrite), proofLhsToRhs),
					mProofRules.resolutionRule(lhs, proofRhsToLhs, mProofRules.iffIntro2(rewrite)));
		}
	}

	private Term convertRewriteEqBinary(final Term rewrite, final Term lhs, final Term rhs) {
		// eqBinary is like expand (chainable) combined with andToOr
		final Theory theory = rewrite.getTheory();
		assert isApplication("=", lhs);
		final Term[] lhsParams = ((ApplicationTerm) lhs).getParameters();
		assert lhsParams.length >= 3;
		assert isApplication("not", rhs);
		final Term rhsAtom = ((ApplicationTerm) rhs).getParameters()[0];
		assert isApplication("or", rhsAtom);
		final Term[] rhsParams = ((ApplicationTerm) rhsAtom).getParameters();
		assert lhsParams.length == rhsParams.length + 1;

		final Term proof1 = mProofRules.resolutionRule(rhs, mProofRules.iffIntro1(rewrite),
				mProofRules.notElim(rhs));
		Term proof2 = mProofRules.resolutionRule(rhs, mProofRules.notIntro(rhs), mProofRules.iffIntro2(rewrite));
		proof2 = mProofRules.resolutionRule(rhsAtom, proof2, mProofRules.orElim(rhsAtom));
		proof2 = mProofRules.resolutionRule(lhs, mProofRules.equalsIntro(lhs), proof2);
		// proof1: (= lhs rhs), lhs, ~rhsAtom
		// proof2: (= lhs rhs), ~(= lhs0 lhs1), ..., ~(= lhsn lhsn+1), rhsParam[0],...rhsParam[n]
		for (int i = 0; i < rhsParams.length; i++) {
			final Term eqi = theory.term("=", lhsParams[i], lhsParams[i + 1]);
			assert rhsParams[i] == theory.term("not", eqi);
			proof2 = mProofRules.resolutionRule(rhsParams[i], proof2, mProofRules.notElim(rhsParams[i]));
			proof2 = mProofRules.resolutionRule(eqi,
					mProofRules.resolutionRule(rhsParams[i], mProofRules.notIntro(rhsParams[i]),
					mProofRules.resolutionRule(rhsAtom, mProofRules.orIntro(i, rhsAtom),
									mProofRules.resolutionRule(lhs, proof1, mProofRules.equalsElim(i, i + 1, lhs)))),
					proof2);
			// proof2: (= lhs rhs), ~(= lhsi+1 lhsi+2), ..., ~(= lhsn lhsn+1), rhsParam[i+1],...rhsParam[n]
		}
		return proof2;
	}

	private Term convertRewriteDistinct(final String rewriteRule, final Term rewrite, final Term lhs, final Term rhs) {
		final Theory theory = rewrite.getTheory();
		assert isApplication("distinct", lhs);
		final Term[] args = ((ApplicationTerm) lhs).getParameters();
		switch (rewriteRule) {
		case ":distinctBool":
			assert args.length > 2 && args[0].getSort().getName() == "Bool" && isApplication("false", rhs);
			final Term eq01 = theory.term("=", args[0], args[1]);
			final Term eq02 = theory.term("=", args[0], args[2]);
			final Term eq12 = theory.term("=", args[1], args[2]);
			final Term proof01 = mProofRules.distinctElim(0, 1, lhs);
			final Term proof02 = mProofRules.distinctElim(0, 2, lhs);
			final Term proof12 = mProofRules.distinctElim(1, 2, lhs);
			Term proof =
					mProofRules.resolutionRule(args[0],
							mProofRules.resolutionRule(args[1], mProofRules.iffIntro1(eq01),
									mProofRules.resolutionRule(args[2], mProofRules.iffIntro1(eq02),
											mProofRules.iffIntro2(eq12))),
							mProofRules.resolutionRule(args[1], mProofRules.resolutionRule(args[2],
									mProofRules.iffIntro1(eq12), mProofRules.iffIntro2(eq02)),
									mProofRules.iffIntro2(eq01)));
			proof = mProofRules.resolutionRule(eq01,
					mProofRules.resolutionRule(eq02, mProofRules.resolutionRule(eq12, proof, proof12), proof02),
					proof01);
			proof = mProofRules.resolutionRule(lhs,
					mProofRules.resolutionRule(rhs, mProofRules.iffIntro1(rewrite), mProofRules.falseElim()),
					proof);
			return proof;

		case ":distinctSame": {
			// (distinct ... x ... x ...) = false
			assert isApplication("false", rhs);
			final HashMap<Term,Integer> seen = new HashMap<>();
			for (int i = 0; i < args.length; i++) {
				final Integer otherIdx = seen.put(args[i], i);
				if (otherIdx != null) {
					final Term eq = theory.term("=", args[i], args[i]);
					return mProofRules.resolutionRule(lhs,
							mProofRules.resolutionRule(rhs, mProofRules.iffIntro1(rewrite),
									mProofRules.falseElim()),
							mProofRules.resolutionRule(eq, mProofRules.refl(args[i]),
									mProofRules.distinctElim(otherIdx, i, lhs)));
				}
			}
			throw new AssertionError();
		}
		case ":distinctBinary": {
			final Term rhsAtom = negate(rhs);
			if (args.length == 2) {
				assert rhsAtom == mSkript.term("=", args[0], args[1]);
				final Term proof1 = mProofRules.resolutionRule(rhsAtom, mProofRules.distinctIntro(lhs),
						mProofRules.notElim(rhs));
				final Term proof2 = mProofRules.resolutionRule(rhsAtom, mProofRules.notIntro(rhs),
						mProofRules.distinctElim(0, 1, lhs));
				return mProofRules.resolutionRule(lhs,
						mProofRules.resolutionRule(rhs, mProofRules.iffIntro1(rewrite), proof1),
						mProofRules.resolutionRule(rhs, proof2, mProofRules.iffIntro2(rewrite)));
			}
			assert isApplication("or", rhsAtom);
			final Term[] rhsArgs = ((ApplicationTerm) rhsAtom).getParameters();
			Term proof1 = mProofRules.distinctIntro(lhs);
			Term proof2 = mProofRules.resolutionRule(rhsAtom, mProofRules.notIntro(rhs),
					mProofRules.orElim(rhsAtom));
			int offset = 0;
			for (int i = 0; i < args.length - 1; i++) {
				for (int j = i + 1; j < args.length; j++) {
					assert offset < rhsArgs.length && rhsArgs[offset] == mSkript.term("=", args[i], args[j]);
					proof1 = mProofRules.resolutionRule(rhsArgs[offset], proof1,
							mProofRules.orIntro(offset, rhsAtom));
					proof2 = mProofRules.resolutionRule(rhsArgs[offset], proof2, mProofRules.distinctElim(i, j, lhs));
					offset++;
				}
			}
			proof1 = mProofRules.resolutionRule(rhsAtom, proof1, mProofRules.notElim(rhs));
			assert offset == rhsArgs.length;
			return mProofRules.resolutionRule(lhs,
					mProofRules.resolutionRule(rhs, mProofRules.iffIntro1(rewrite), proof1),
					mProofRules.resolutionRule(rhs, proof2, mProofRules.iffIntro2(rewrite)));
		}
		}
		throw new AssertionError();
	}

	private Term convertRewriteOrSimp(final Term rewriteStmt, final Term lhs, final Term rhs) {
		// lhs: (or ...), rhs: (or ...)
		// duplicated entries in lhs and false should be removed in rhs.
		// if only one entry remains, or is omitted, if no entry remains, false is
		// returned.
		assert isApplication("or", lhs);
		final LinkedHashMap<Term, Integer> args = new LinkedHashMap<>();
		final Term[] lhsParams = ((ApplicationTerm) lhs).getParameters();
		Term falseTerm = null;
		for (int i = 0; i < lhsParams.length; i++) {
			if (isApplication("false", lhsParams[i])) {
				falseTerm = lhsParams[i];
			} else {
				args.put(lhsParams[i], i);
			}
		}
		Term proofRhs = mProofRules.orElim(lhs);
		if (falseTerm != null && rhs != falseTerm) {
			proofRhs = mProofRules.resolutionRule(falseTerm, proofRhs, mProofRules.falseElim());
		}
		Term proofLhs = null;
		if (isApplication("false", rhs)) {
			proofLhs = mProofRules.falseElim();
		} else if (isApplication("or", rhs)) {
			final Term[] rhsParams = ((ApplicationTerm) rhs).getParameters();
			for (int i = 0; i < rhsParams.length; i++) {
				proofRhs = mProofRules.resolutionRule(rhsParams[i], proofRhs, mProofRules.orIntro(i, rhs));
			}
			proofLhs = mProofRules.orElim(rhs);
		}
		for (final int i : args.values()) {
			if (proofLhs == null) {
				proofLhs = mProofRules.orIntro(i, lhs);
			} else {
				proofLhs = mProofRules.resolutionRule(lhsParams[i], proofLhs, mProofRules.orIntro(i, lhs));
			}
		}
		return proveIff(rewriteStmt, proofRhs, proofLhs);
	}

	private Term convertRewriteOrTaut(final Term rewrite, final Term lhs, final Term rhs) {
		assert isApplication("or", lhs) && isApplication("true", rhs);
		// case 1
		// lhs: (or ... true ...), rhs: true
		// case 2
		// lhs: (or ... p ... (not p) ...), rhs: true
		Term proof = mProofRules.iffIntro2(rewrite);
		final HashMap<Term,Integer> seen = new HashMap<>();
		final Term[] lhsParams = ((ApplicationTerm) lhs).getParameters();
		for (int i = 0; i < lhsParams.length; i++) {
			if (isApplication("true", lhsParams[i])) {
				proof = mProofRules.resolutionRule(lhs, mProofRules.orIntro(i, lhs), proof);
				break;
			}
			final Integer otherIdx = seen.get(negate(lhsParams[i]));
			if (otherIdx != null) {
				int posIdx, negIdx;
				if (isApplication("not", lhsParams[i])) {
					negIdx = i;
					posIdx = otherIdx;
				} else {
					negIdx = otherIdx;
					posIdx = i;
				}
				final Term orProof = mProofRules.resolutionRule(
						lhsParams[posIdx], mProofRules.resolutionRule(lhsParams[negIdx],
								mProofRules.notIntro(lhsParams[negIdx]), mProofRules.orIntro(negIdx, lhs)),
						mProofRules.orIntro(posIdx, lhs));
				proof = mProofRules.resolutionRule(lhs, orProof, proof);
				break;
			}
			seen.put(lhsParams[i], i);
		}
		return mProofRules.resolutionRule(rhs, mProofRules.trueIntro(), proof);
	}

	private Term convertRewriteCanonicalSum(final Term lhs, final Term rhs) {
		final Theory theory = lhs.getTheory();
		if (lhs instanceof ConstantTerm) {
			final Term expected = Polynomial.parseConstant(lhs).toTerm(lhs.getSort());
			return mProofRules.oracle(
					new ProofLiteral[] { new ProofLiteral(theory.term(SMTLIBConstants.EQUALS, lhs, expected), true) },
					new Annotation[] { ProofConstants.RW_CANONICAL_SUM });
		}

		final ApplicationTerm lhsApp = (ApplicationTerm) lhs;
		final Term[] lhsArgs = lhsApp.getParameters();
		switch (lhsApp.getFunction().getName()) {
		case "+":
			return mProofRules.polyAdd(lhs, rhs);
		case "*":
			return mProofRules.polyMul(lhs, rhs);
		case "to_real": {
			final Term expected = ProofRules.computePolyToReal(lhsArgs[0]);
			if (rhs == expected) {
				return mProofRules.toRealDef(lhs);
			} else {
				// difference can only be order of +
				return res(theory.term(SMTLIBConstants.EQUALS, lhs, expected),
						mProofRules.toRealDef(lhs),
						res(theory.term(SMTLIBConstants.EQUALS, expected, rhs),
								 mProofRules.polyAdd(expected, rhs),
								 mProofRules.trans(lhs, expected, rhs)));
			}
		}
		case "-": {
			final Term minusToPlus = ProofRules.computePolyMinus(lhs);
			if (minusToPlus == rhs) {
				return mProofRules.minusDef(lhs);
			}
			if (lhsArgs.length == 1) {
				final Term proof = res(theory.term(SMTLIBConstants.EQUALS, lhs, minusToPlus),
						mProofRules.minusDef(lhs), mProofRules.trans(lhs, minusToPlus, rhs));
				return res(theory.term(SMTLIBConstants.EQUALS, minusToPlus, rhs),
						mProofRules.polyMul(minusToPlus, rhs), proof);
			} else {
				final Term[] expectedArgs = new Term[lhsArgs.length];
				expectedArgs[0] = lhsArgs[0];
				for (int i = 1; i < lhsArgs.length; i++) {
					final SMTAffineTerm affineTerm = new SMTAffineTerm();
					affineTerm.add(Rational.MONE, lhsArgs[i]);
					expectedArgs[i] = affineTerm.toTerm(lhsArgs[i].getSort());
				}
				final Term expectedPlus = theory.term(SMTLIBConstants.PLUS, expectedArgs);
				Term proof;
				if (expectedPlus != rhs) {
					proof = res(theory.term(SMTLIBConstants.EQUALS, expectedPlus, rhs),
							mProofRules.polyAdd(expectedPlus, rhs),
							mProofRules.trans(lhs, minusToPlus, expectedPlus, rhs));
				} else {
					proof = mProofRules.trans(lhs, minusToPlus, expectedPlus);
				}
				proof = res(theory.term(SMTLIBConstants.EQUALS, lhs, minusToPlus), mProofRules.minusDef(lhs), proof);
				proof = res(theory.term(SMTLIBConstants.EQUALS, minusToPlus, expectedPlus),
						mProofRules.cong(minusToPlus, expectedPlus), proof);
				final HashSet<Term> seenEqs = new HashSet<>();
				final Term[] minusToPlusArgs = ((ApplicationTerm) minusToPlus).getParameters();
 				for (int i = 0; i < minusToPlusArgs.length; i++) {
					final Term eq = theory.term(SMTLIBConstants.EQUALS, minusToPlusArgs[i], expectedArgs[i]);
					if (seenEqs.add(eq)) {
						final Term proofEq = minusToPlusArgs[i] == expectedArgs[i]
								? mProofRules.refl(minusToPlusArgs[i])
										: mProofRules.polyMul(minusToPlusArgs[i], expectedArgs[i]);
						proof = res(eq, proofEq, proof);
					}
 				}
				return proof;
			}
		}
		case "/":
			return mProofRules.oracle(
					new ProofLiteral[] { new ProofLiteral(theory.term(SMTLIBConstants.EQUALS, lhs, rhs), true) },
					new Annotation[] { ProofConstants.RW_CANONICAL_SUM });
		default:
			throw new AssertionError();
		}
	}

	private Term convertRewriteToInt(final Term lhs, final Term rhs) {
		// (to_int constant) --> floor(constant)
		assert isApplication("to_int", lhs);
		final Term arg = ((ApplicationTerm) lhs).getParameters()[0];
		final Rational argConst = parseConstant(arg);
		final Rational rhsConst = parseConstant(rhs);
		assert argConst != null && rhsConst != null && rhsConst.equals(argConst.floor());

		// use trichotomy and toIntHigh/toIntLow and total-int
		final Theory theory = lhs.getTheory();
		final Term diffLhsRhs = theory.term(SMTLIBConstants.PLUS, lhs, rhsConst.negate().toTerm(rhs.getSort()));
		final Term lt = theory.term(SMTLIBConstants.LT, lhs, rhs);
		final Term gt = theory.term(SMTLIBConstants.LT, rhs, lhs);
		final Term leqDiffm1 = theory.term(SMTLIBConstants.LEQ, diffLhsRhs, Rational.MONE.toTerm(rhs.getSort()));
		final Term geqDiff0 = theory.term(SMTLIBConstants.LEQ, Rational.ZERO.toTerm(rhs.getSort()), diffLhsRhs);
		final Term leqDiff0 = theory.term(SMTLIBConstants.LEQ, diffLhsRhs, Rational.ZERO.toTerm(rhs.getSort()));
		final Term geqDiff1 = theory.term(SMTLIBConstants.LEQ, Rational.ONE.toTerm(rhs.getSort()), diffLhsRhs);
		Term proof = mProofRules.trichotomy(lhs, rhs);
		final Term one = Rational.ONE.toTerm(arg.getSort());
		final Term toIntLowLeq = theory.term(SMTLIBConstants.LEQ, theory.term(SMTLIBConstants.TO_REAL, lhs), arg);
		final Term toIntHighLt = theory.term(SMTLIBConstants.LT, arg,
				theory.term(SMTLIBConstants.PLUS, theory.term(SMTLIBConstants.TO_REAL, lhs), one));
		final BigInteger[] coeffs = new BigInteger[] { BigInteger.ONE, BigInteger.ONE };
		proof = res(gt, proof, mProofRules.farkas(new Term[] { gt, leqDiff0 }, coeffs));
		proof = res(leqDiff0, mProofRules.totalInt(diffLhsRhs, BigInteger.ZERO), proof);
		proof = res(geqDiff1, proof, mProofRules.farkas(new Term[] { toIntLowLeq, geqDiff1 }, coeffs));
		proof = res(lt, proof, mProofRules.farkas(new Term[] { lt, geqDiff0 }, coeffs));
		proof = res(geqDiff0, mProofRules.totalInt(diffLhsRhs, BigInteger.ONE.negate()), proof);
		proof = res(leqDiffm1, proof, mProofRules.farkas(new Term[] { toIntHighLt, leqDiffm1 }, coeffs));
		proof = res(toIntLowLeq, mProofRules.toIntLow(arg), proof);
		proof = res(toIntHighLt, mProofRules.toIntHigh(arg), proof);
		return proof;
	}

	private Term convertRewriteStoreOverStore(final Term lhs, final Term rhs) {
		// lhs: (store (store a i v) i w)
		// rhs: (store a i w)
		assert isApplication("store", lhs);
		final Term[] outerArgs = ((ApplicationTerm) lhs).getParameters();
		final Term innerStore = outerArgs[0];
		final Term index = outerArgs[1];
		final Term valueW = outerArgs[2];
		assert isApplication("store", innerStore);
		final Term[] innerArgs = ((ApplicationTerm) innerStore).getParameters();
		final Term array = innerArgs[0];
		final Term innerIndex = innerArgs[1];
		final Term proofEq = proveTrivialEquality(index, innerIndex);
		assert proofEq != null;
		assert rhs == mSkript.term("store", array, index, valueW);

		final Theory theory = lhs.getTheory();
		final Term diff = theory.term("@diff", lhs, rhs);
		final Term selectLhsDiff = theory.term(SMTLIBConstants.SELECT, lhs, diff);
		final Term selectInnerDiff = theory.term(SMTLIBConstants.SELECT, innerStore, diff);
		final Term selectArrayDiff = theory.term(SMTLIBConstants.SELECT, array, diff);
		final Term selectRhsDiff = theory.term(SMTLIBConstants.SELECT, rhs, diff);
		final Term selectLhsI = theory.term(SMTLIBConstants.SELECT, lhs, index);
		final Term selectRhsI = theory.term(SMTLIBConstants.SELECT, rhs, index);


		// show (select lhs diff) = (select rhs diff) lhs if (= i diff)
		Term proof1 = mProofRules.trans(selectLhsDiff, selectLhsI, valueW, selectRhsI, selectRhsDiff);
		proof1 = res(theory.term("=", selectLhsDiff, selectLhsI), mProofRules.cong(selectLhsDiff, selectLhsI), proof1);
		proof1 = res(theory.term("=", lhs, lhs), mProofRules.refl(lhs), proof1);
		proof1 = res(theory.term("=", diff, index), mProofRules.symm(diff, index), proof1);
		proof1 = res(theory.term("=", selectLhsI, valueW), mProofRules.selectStore1(innerStore, index, valueW), proof1);
		proof1 = res(theory.term("=", valueW, selectRhsI), mProofRules.symm(valueW, selectRhsI), proof1);
		proof1 = res(theory.term("=", selectRhsI, valueW), mProofRules.selectStore1(array, index, valueW), proof1);
		proof1 = res(theory.term("=", selectRhsI, selectRhsDiff), mProofRules.cong(selectRhsI, selectRhsDiff), proof1);
		proof1 = res(theory.term("=", rhs, rhs), mProofRules.refl(rhs), proof1);

		// now the case ~(= i diff)
		Term proof2 = mProofRules.trans(selectLhsDiff, selectInnerDiff, selectArrayDiff, selectRhsDiff);
		proof2 = res(theory.term("=", selectLhsDiff, selectInnerDiff),
				mProofRules.selectStore2(innerStore, index, valueW, diff), proof2);
		proof2 = res(theory.term("=", selectInnerDiff, selectArrayDiff),
				mProofRules.selectStore2(array, innerIndex, innerArgs[2], diff), proof2);
		if (innerIndex != index) {
			proof2 = res(theory.term("=", innerIndex, diff), proof2, mProofRules.trans(index, innerIndex, diff));
			proof2 = res(theory.term("=", index, innerIndex), proofEq, proof2);
		}
		proof2 = res(theory.term("=", selectArrayDiff, selectRhsDiff),
				mProofRules.symm(selectArrayDiff, selectRhsDiff), proof2);
		proof2 = res(theory.term("=", selectRhsDiff, selectArrayDiff),
				mProofRules.selectStore2(array, index, valueW, diff), proof2);

		Term proof = res(theory.term("=", index, diff), proof2, proof1);
		proof = res(theory.term("=", selectLhsDiff, selectRhsDiff), proof, mProofRules.extDiff(lhs, rhs));
		return proof;
	}

	private Term convertRewriteSelectOverStore(final Term lhs, final Term rhs) {
		// lhs: (select (store a i v) j) i-j is a constant
		// rhs: (select a j) if i-j !=0. v if i-j = 0
		final Theory theory = lhs.getTheory();
		assert isApplication("select", lhs);
		final Term[] selectArgs = ((ApplicationTerm) lhs).getParameters();
		final Term store = selectArgs[0];
		assert isApplication("store", store);
		final Term[] storeArgs = ((ApplicationTerm) store).getParameters();
		final Term array = storeArgs[0];
		final Term indexI = storeArgs[1];
		final Term value = storeArgs[2];
		final Term indexJ = selectArgs[1];
		final Term proofEqualJI = proveTrivialEquality(indexJ, indexI);
		if (proofEqualJI != null) {
			assert rhs == storeArgs[2];
			final Term selectStoreI = theory.term("select", store, indexI);
			Term proof = mProofRules.trans(lhs, selectStoreI, value);
			proof = res(theory.term("=", lhs, selectStoreI), mProofRules.cong(lhs,  selectStoreI), proof);
			proof = res(theory.term("=", store, store), mProofRules.refl(store), proof);
			proof = res(theory.term("=", indexJ, indexI), proofEqualJI, proof);
			proof = res(theory.term("=", selectStoreI, value), mProofRules.selectStore1(array, indexI, value), proof);
			return proof;
		} else {
			final Term proofNotEqual = proveTrivialDisequality(indexI, indexJ);
			assert proofNotEqual != null;
			return res(theory.term("=", indexI, indexJ), mProofRules.selectStore2(array, indexI, value, indexJ),
					proofNotEqual);
		}
	}

	private Term convertRewriteStore(final Term rewrite, final Term lhs, final Term rhs) {
		// lhs: (= (store a i v) a) (or symmetric)
		// rhs: (= (select a i) v)
		final Theory theory = lhs.getTheory();
		assert isApplication("=", lhs);
		final Term[] lhsArgs = ((ApplicationTerm) lhs).getParameters();
		final int storeIdx = isApplication("store", lhsArgs[0])
				&& ((ApplicationTerm) lhsArgs[0]).getParameters()[0] == lhsArgs[1] ? 0 : 1;
		final Term store = lhsArgs[storeIdx];
		final Term[] storeArgs = ((ApplicationTerm) store).getParameters();
		final Term array = storeArgs[0];
		final Term index = storeArgs[1];
		final Term value = storeArgs[2];
		assert isApplication("store", store) && array == lhsArgs[1 - storeIdx];

		final Term diff = theory.term("@diff", lhsArgs);
		final Term selectArrayDiff = theory.term(SMTLIBConstants.SELECT, array, diff);
		final Term selectStoreDiff = theory.term(SMTLIBConstants.SELECT, store, diff);
		final Term selectArrayI = theory.term(SMTLIBConstants.SELECT, array, index);
		final Term selectStoreI = theory.term(SMTLIBConstants.SELECT, store, index);


		// show (select a i) = v if array = store
		Term proofRhs = res(theory.term("=", selectArrayI, selectStoreI),
				res(theory.term("=", index, index), mProofRules.refl(index),
						mProofRules.cong(selectArrayI, selectStoreI)),
						mProofRules.trans(selectArrayI, selectStoreI, value));

		// show (select store diff) = (select array diff) lhs if (= i diff)
		Term proofLhs = mProofRules.trans(selectStoreDiff, selectStoreI, value, selectArrayI, selectArrayDiff);
		proofLhs = res(theory.term("=", selectStoreDiff, selectStoreI),
				mProofRules.cong(selectStoreDiff, selectStoreI), proofLhs);
		proofLhs = res(theory.term("=", diff, index), mProofRules.symm(diff, index), proofLhs);
		proofLhs = res(theory.term("=", store, store), mProofRules.refl(store), proofLhs);
		proofLhs = res(theory.term("=", value, selectArrayI), mProofRules.symm(value, selectArrayI), proofLhs);
		proofLhs = res(theory.term("=", selectArrayI, selectArrayDiff),
				mProofRules.cong(selectArrayI, selectArrayDiff), proofLhs);
		proofLhs = res(theory.term("=", array, array), mProofRules.refl(array), proofLhs);

		// show (select store diff) = (select array diff) lhs also if ~(= i diff)
		proofLhs = res(theory.term("=", index, diff), mProofRules.selectStore2(array, index, value, diff), proofLhs);

		// hence store = array.
		proofLhs = res(theory.term("=", selectStoreDiff, selectArrayDiff),
				proofLhs, mProofRules.extDiff(store, array));

		// swap store and array according to lhs.
		if (storeIdx == 0) {
			proofRhs = res(theory.term("=", array, store), mProofRules.symm(array, store), proofRhs);
		} else {
			proofLhs = res(theory.term("=", store, array), mProofRules.symm(store, array), proofRhs);
		}
		Term proof = proveIff(rewrite, proofRhs, proofLhs);
		proof = res(theory.term("=", selectStoreI, value), mProofRules.selectStore1(array, index, value), proof);
		return proof;
	}

	private Term convertRewriteToLeq0(final String rewriteRule, final Term lhs, final Term rhs) {
		boolean isNegated;
		switch (rewriteRule) {
		case ":leqToLeq0":
			assert isApplication("<=", lhs);
			isNegated = false;
			break;
		case ":ltToLeq0":
			assert isApplication("<", lhs);
			isNegated = true;
			break;
		case ":geqToLeq0":
			assert isApplication(">=", lhs);
			isNegated = false;
			break;
		case ":gtToLeq0":
			assert isApplication(">", lhs);
			isNegated = true;
			break;
		default:
			throw new AssertionError();
		}
		final Term rhsAtom = isNegated ? negate(rhs) : rhs;
		assert isApplication("<=", rhsAtom);

		return proveRewriteWithLeq(lhs, rhs, false);
	}

	Term convertRewriteForallExists(final Term lhs, final Term rhs) {
		// lhs: (forall (vs) F)
		// rhs: (not (exists (vs) (not F)))
		final Theory theory = lhs.getTheory();
		assert isApplication("not", rhs);
		final Term rhsArg = ((ApplicationTerm) rhs).getParameters()[0];
		final QuantifiedFormula forall = (QuantifiedFormula) lhs;
		final QuantifiedFormula exists = (QuantifiedFormula) rhsArg;
		assert forall.getQuantifier() == QuantifiedFormula.FORALL && exists.getQuantifier() == QuantifiedFormula.EXISTS;
		assert Arrays.equals(forall.getVariables(), exists.getVariables());
		final Term forallSubformula = forall.getSubformula();
		final Term existsSubformula = exists.getSubformula();
		assert isApplication("not", existsSubformula) && forallSubformula == ((ApplicationTerm) existsSubformula).getParameters()[0];

		final Term[] forallSkolem = mProofRules.getSkolemVars(forall.getVariables(), forallSubformula, true);
		final Term[] existsSkolem = mProofRules.getSkolemVars(exists.getVariables(), existsSubformula, false);
		final FormulaUnLet unletter = new FormulaUnLet();
		final Term existsLetted = unletter.unlet(theory.let(forall.getVariables(), existsSkolem, forallSubformula));
		final Term notExistsLetted = theory.term("not", existsLetted);
		final Term forallLetted = unletter.unlet(theory.let(forall.getVariables(), forallSkolem, forallSubformula));
		final Term notForallLetted = theory.term("not", forallLetted);
		final Term proofLtoR =
				mProofRules.resolutionRule(exists,
						mProofRules.notIntro(rhs),
						mProofRules.resolutionRule(notExistsLetted,
								mProofRules.existsElim(exists),
								mProofRules.resolutionRule(existsLetted, mProofRules.forallElim(existsSkolem, forall),
										mProofRules.notElim(notExistsLetted))));
		final Term proofRtoL =
				mProofRules.resolutionRule(exists,
						mProofRules.resolutionRule(notForallLetted,
								mProofRules.resolutionRule(forallLetted,
										mProofRules.notIntro(notForallLetted),
										mProofRules.forallIntro(forall)),
								mProofRules.existsIntro(forallSkolem, exists)),
						mProofRules.notElim(rhs));
		return proveIff(theory.term("=", lhs, rhs), proofLtoR, proofRtoL);
	}

	private Term convertRewriteIte(final String rewriteRule, final Term rewriteStmt, final Term ite, final Term rhs) {
		// lhs: (ite cond then else)
		assert isApplication("ite", ite);
		final Term[] args = ((ApplicationTerm) ite).getParameters();
		final Term cond = args[0];
		final Term t1 = args[1];
		final Term t2 = args[2];
		switch (rewriteRule) {
		case ":iteTrue":
			// (= (ite true t1 t2) t1)
			return mProofRules.resolutionRule(cond, mProofRules.trueIntro(), mProofRules.ite1(ite));
		case ":iteFalse":
			// (= (ite false t1 t2) t2)
			return mProofRules.resolutionRule(cond, mProofRules.ite2(ite), mProofRules.falseElim());
		case ":iteSame":
			// (= (ite cond t1 t1) t1)
			return mProofRules.resolutionRule(cond, mProofRules.ite2(ite), mProofRules.ite1(ite));
		case ":iteBool1": {
			// (= (ite cond true false) cond)
			assert isApplication("true", t1) && isApplication("false", t2) && rhs == cond;
			// show ~ite, cond by observing that ite2 is cond, (= ite false).
			final Term iteFalse = mSkript.term("=", ite, t2);
			Term proofRhs = mProofRules.resolutionRule(iteFalse, mProofRules.ite2(ite), mProofRules.iffElim2(iteFalse));
			proofRhs = mProofRules.resolutionRule(t2, proofRhs, mProofRules.falseElim());
			// show ite, ~cond by observing that ite1 is ~cond, (= ite true).
			final Term iteTrue = mSkript.term("=", ite, t1);
			Term proofLhs = mProofRules.resolutionRule(iteTrue, mProofRules.ite1(ite), mProofRules.iffElim1(iteTrue));
			proofLhs = mProofRules.resolutionRule(t1, mProofRules.trueIntro(), proofLhs);
			return proveIff(rewriteStmt, proofRhs, proofLhs);
		}
		case ":iteBool2": {
			// (= (ite cond false true) (not cond))
			assert isApplication("false", t1) && isApplication("true", t2) && rhs == mSkript.term("not", cond);
			// show ~ite, not cond by observing that ite1 is ~cond, (= ite false).
			final Term iteFalse = mSkript.term("=", ite, t1);
			Term proofRhs = mProofRules.resolutionRule(iteFalse, mProofRules.ite1(ite), mProofRules.iffElim2(iteFalse));
			proofRhs = mProofRules.resolutionRule(t1, proofRhs, mProofRules.falseElim());
			proofRhs = mProofRules.resolutionRule(cond, mProofRules.notIntro(rhs), proofRhs);
			// show ite, ~not cond by observing that ite2 is cond, (= ite true).
			final Term iteTrue = mSkript.term("=", ite, t2);
			Term proofLhs = mProofRules.resolutionRule(iteTrue, mProofRules.ite2(ite), mProofRules.iffElim1(iteTrue));
			proofLhs = mProofRules.resolutionRule(t2, mProofRules.trueIntro(), proofLhs);
			proofLhs = mProofRules.resolutionRule(cond, proofLhs, mProofRules.notElim(rhs));
			return proveIff(rewriteStmt, proofRhs, proofLhs);
		}
		case ":iteBool3": {
			// (= (ite cond true t2) (or cond t2))
			assert isApplication("true", t1) && rhs == mSkript.term("or", cond, t2);
			final Term iteTrue = mSkript.term("=", ite, t1);
			final Term iteT2 = mSkript.term("=", ite, t2);
			// show ~ite, (or cond t2) by case distinction over cond, t2
			final Term proofRhs = mProofRules
					.resolutionRule(cond,
							mProofRules.resolutionRule(t2,
									mProofRules.resolutionRule(iteT2, mProofRules.ite2(ite),
											mProofRules.iffElim2(iteT2)),
									mProofRules.orIntro(1, rhs)),
							mProofRules.orIntro(0, rhs));
			// show ite, ~(or cond t2) by case distinction over cond, t2
			Term proofLhs = mProofRules.resolutionRule(cond,
					mProofRules.resolutionRule(t2, mProofRules.orElim(rhs),
							mProofRules.resolutionRule(iteT2, mProofRules.ite2(ite), mProofRules.iffElim1(iteT2))),
					mProofRules.resolutionRule(iteTrue, mProofRules.ite1(ite), mProofRules.iffElim1(iteTrue)));
			proofLhs = mProofRules.resolutionRule(t1, mProofRules.trueIntro(), proofLhs);
			return proveIff(rewriteStmt, proofRhs, proofLhs);
		}
		case ":iteBool4": {
			// (= (ite cond false t2) (not (or cond (not t2))))
			assert isApplication("false", t1)
					&& rhs == mSkript.term("not", mSkript.term("or", cond, mSkript.term("not", t2)));
			final Term notRhs = ((ApplicationTerm) rhs).getParameters()[0];
			final Term notT2 = ((ApplicationTerm) notRhs).getParameters()[1];
			final Term iteFalse = mSkript.term("=", ite, t1);
			final Term iteT2 = mSkript.term("=", ite, t2);
			// show ~ite, (not (or cond (not t2))) by case distinction over cond, t2
			Term proofRhs = mProofRules.resolutionRule(cond,
					mProofRules.resolutionRule(notT2, mProofRules.orElim(notRhs),
							mProofRules.resolutionRule(t2,
									mProofRules.resolutionRule(iteT2, mProofRules.ite2(ite),
											mProofRules.iffElim2(iteT2)),
									mProofRules.notElim(notT2))),
					mProofRules.resolutionRule(iteFalse, mProofRules.ite1(ite), mProofRules.iffElim2(iteFalse)));
			proofRhs = mProofRules.resolutionRule(t1, proofRhs, mProofRules.falseElim());
			proofRhs = mProofRules.resolutionRule(notRhs, mProofRules.notIntro(rhs), proofRhs);
			// show ite, ~(not (or cond (not t2)))) by case distinction over cond, t2
			Term proofLhs = mProofRules.resolutionRule(cond,
					mProofRules.resolutionRule(t2,
							mProofRules.resolutionRule(notT2, mProofRules.notIntro(notT2),
									mProofRules.orIntro(1, notRhs)),
							mProofRules.resolutionRule(iteT2, mProofRules.ite2(ite), mProofRules.iffElim1(iteT2))),
					mProofRules.orIntro(0, notRhs));
			proofLhs = mProofRules.resolutionRule(notRhs, proofLhs, mProofRules.notElim(rhs));
			return proveIff(rewriteStmt, proofRhs, proofLhs);
		}
		case ":iteBool5": {
			// (= (ite cond t1 true) (or (not cond) t1))
			final Term notCond = mSkript.term("not", cond);
			assert isApplication("true", t2) && rhs == mSkript.term("or", notCond, t1);
			final Term iteT1 = mSkript.term("=", ite, t1);
			final Term iteTrue = mSkript.term("=", ite, t2);
			// show ~ite, (or (not cond) t1) by case distinction over cond, t1
			final Term proofRhs = mProofRules.resolutionRule(cond,
					mProofRules.resolutionRule(notCond, mProofRules.notIntro(notCond), mProofRules.orIntro(0, rhs)),
					mProofRules.resolutionRule(t1,
							mProofRules.resolutionRule(iteT1, mProofRules.ite1(ite), mProofRules.iffElim2(iteT1)),
							mProofRules.orIntro(1, rhs)));
			// show ite, ~(or (not cond) t1) by case distinction over cond, t1
			Term proofLhs = mProofRules.resolutionRule(cond,
					mProofRules.resolutionRule(iteTrue, mProofRules.ite2(ite), mProofRules.iffElim1(iteTrue)),
					mProofRules.resolutionRule(t1,
							mProofRules.resolutionRule(notCond, mProofRules.orElim(rhs),
									mProofRules.notElim(notCond)),
							mProofRules.resolutionRule(iteT1, mProofRules.ite1(ite), mProofRules.iffElim1(iteT1))));
			proofLhs = mProofRules.resolutionRule(t2, mProofRules.trueIntro(), proofLhs);
			return proveIff(rewriteStmt, proofRhs, proofLhs);
		}
		case ":iteBool6":
			// (= (ite cond t1 false) (not (or (not cond) (not t1))))
			assert isApplication("false", t2) && rhs == mSkript.term("not",
					mSkript.term("or", mSkript.term("not", cond), mSkript.term("not", t1)));
			final Term notRhs = ((ApplicationTerm) rhs).getParameters()[0];
			final Term notT1 = ((ApplicationTerm) notRhs).getParameters()[1];
			final Term notCond = ((ApplicationTerm) notRhs).getParameters()[0];
			final Term iteT1 = mSkript.term("=", ite, t1);
			final Term iteFalse = mSkript.term("=", ite, t2);
			// show ~ite, (not (or (not cond) (not t1))) by case distinction over cond, t1
			Term proofRhs =
					mProofRules.resolutionRule(cond, mProofRules.resolutionRule(iteFalse, mProofRules.ite2(ite), mProofRules.iffElim2(iteFalse)),
					mProofRules.resolutionRule(notCond,
									mProofRules.resolutionRule(notT1, mProofRules.orElim(notRhs),
							mProofRules.resolutionRule(t1,
									mProofRules.resolutionRule(iteT1, mProofRules.ite1(ite),
											mProofRules.iffElim2(iteT1)),
									mProofRules.notElim(notT1))),
									mProofRules.notElim(notCond)));
			proofRhs = mProofRules.resolutionRule(t2, proofRhs, mProofRules.falseElim());
			proofRhs = mProofRules.resolutionRule(notRhs, mProofRules.notIntro(rhs), proofRhs);
			// show ite, ~(not (or (not cond) (not t1)))) by case distinction over cond, t1
			Term proofLhs = mProofRules.resolutionRule(notCond,
					mProofRules.resolutionRule(cond, mProofRules.notIntro(notCond),
							mProofRules.resolutionRule(t1,
									mProofRules.resolutionRule(notT1, mProofRules.notIntro(notT1),
											mProofRules.orIntro(1, notRhs)),
									mProofRules.resolutionRule(iteT1, mProofRules.ite1(ite),
											mProofRules.iffElim1(iteT1)))),
					mProofRules.orIntro(0, notRhs));
			proofLhs = mProofRules.resolutionRule(notRhs, proofLhs, mProofRules.notElim(rhs));
			return proveIff(rewriteStmt, proofRhs, proofLhs);
		}
		throw new AssertionError();
	}

	private Term convertRewriteConstDiff(final Term rewriteStmt, final Term lhs, final Term rhs) {
		// lhs: (= ... 5 ... 7 ...), rhs: false
		assert isApplication("=", lhs) && isApplication("false", rhs);
		final Term[] lhsParams = ((ApplicationTerm) lhs).getParameters();
		assert lhsParams[0].getSort().isNumericSort();
		int lastConstantIdx = -1;
		Rational lastConstant = null;
		for (int i = 0; i < lhsParams.length; i++) {
			final Rational value = parseConstant(lhsParams[i]);
			if (value != null) {
				if (lastConstantIdx < 0) {
					lastConstantIdx = i;
					lastConstant = value;
				} else if (!lastConstant.equals(value)) {
					Term proof = proveTrivialDisequality(lhsParams[lastConstantIdx], lhsParams[i]);
					if (lhsParams.length > 2) {
						proof = mProofRules.resolutionRule(
								lhs.getTheory().term("=", lhsParams[lastConstantIdx], lhsParams[i]),
								mProofRules.equalsElim(lastConstantIdx, i, lhs), proof);
					}
					proof = proveIffFalse(rewriteStmt, proof);
					return proof;
				}
			}
		}
		throw new AssertionError();
	}

	private Term convertRewrite(final Term[] newParams) {
		final AnnotatedTerm annotTerm = (AnnotatedTerm) newParams[0];
		final String rewriteRule = annotTerm.getAnnotations()[0].getKey();
		final Term rewriteStmt = annotTerm.getSubterm();
		assert rewriteRule == ":removeForall"
				? isApplication(SMTLIBConstants.IMPLIES, rewriteStmt)
			: isApplication(SMTLIBConstants.EQUALS, rewriteStmt);
		final Term[] stmtParams = ((ApplicationTerm) rewriteStmt).getParameters();
		Term subProof;

		switch (rewriteRule) {
		case ":expand":
		case ":expandDef":
			subProof = mProofRules.expand(stmtParams[0]);
			break;
		case ":intern":
			subProof = convertRewriteIntern(stmtParams[0], stmtParams[1]);
			break;
		case ":notSimp":
			subProof = convertRewriteNot(rewriteStmt, stmtParams[0], stmtParams[1]);
			break;
		case ":trueNotFalse":
			subProof = convertRewriteTrueNotFalse(stmtParams[0], stmtParams[1]);
			break;
		case ":eqTrue":
		case ":eqFalse":
			subProof = convertRewriteEqTrueFalse(rewriteRule, stmtParams[0], stmtParams[1]);
			break;
		case ":eqSimp":
		case ":eqSame":
			subProof = convertRewriteEqSimp(rewriteRule, rewriteStmt, stmtParams[0], stmtParams[1]);
			break;
		case ":eqBinary":
			subProof = convertRewriteEqBinary(rewriteStmt, stmtParams[0], stmtParams[1]);
			break;
		case ":eqToXor":
		case ":distinctToXor":
			subProof = convertRewriteToXor(rewriteRule, rewriteStmt, stmtParams[0], stmtParams[1]);
			break;
		case ":xorTrue":
		case ":xorFalse":
			subProof = convertRewriteXorConst(rewriteRule, rewriteStmt, stmtParams[0], stmtParams[1]);
			break;
		case ":xorNot":
			subProof = convertRewriteXorNot(rewriteStmt, stmtParams[0], stmtParams[1]);
			break;
		case ":xorSame":
			subProof = convertRewriteXorSame(rewriteStmt, stmtParams[0], stmtParams[1]);
			break;
		case ":orSimp":
			subProof = convertRewriteOrSimp(rewriteStmt, stmtParams[0], stmtParams[1]);
			break;
		case ":orTaut":
			subProof = convertRewriteOrTaut(rewriteStmt, stmtParams[0], stmtParams[1]);
			break;
		case ":distinctBool":
		case ":distinctSame":
		case ":distinctBinary":
			subProof = convertRewriteDistinct(rewriteRule, rewriteStmt, stmtParams[0], stmtParams[1]);
			break;
		case ":leqTrue":
		case ":leqFalse":
			subProof = convertRewriteLeq(rewriteRule, rewriteStmt, stmtParams[0], stmtParams[1]);
			break;
		case ":leqToLeq0":
		case ":ltToLeq0":
		case ":geqToLeq0":
		case ":gtToLeq0":
			subProof = convertRewriteToLeq0(rewriteRule, stmtParams[0], stmtParams[1]);
			break;
		case ":forallExists":
			subProof = convertRewriteForallExists(stmtParams[0], stmtParams[1]);
			break;
		case ":iteTrue":
		case ":iteFalse":
		case ":iteSame":
		case ":iteBool1":
		case ":iteBool2":
		case ":iteBool3":
		case ":iteBool4":
		case ":iteBool5":
		case ":iteBool6":
			subProof = convertRewriteIte(rewriteRule, rewriteStmt, stmtParams[0], stmtParams[1]);
			break;
		case ":constDiff":
			subProof = convertRewriteConstDiff(rewriteStmt, stmtParams[0], stmtParams[1]);
			break;
		case ":strip":
			subProof = mProofRules.delAnnot(stmtParams[0]);
			break;
		case ":canonicalSum":
			subProof = convertRewriteCanonicalSum(stmtParams[0], stmtParams[1]);
			break;
		case ":toInt":
			subProof = convertRewriteToInt(stmtParams[0], stmtParams[1]);
			break;
		case ":storeOverStore":
			subProof = convertRewriteStoreOverStore(stmtParams[0], stmtParams[1]);
			break;
		case ":selectOverStore":
			subProof = convertRewriteSelectOverStore(stmtParams[0], stmtParams[1]);
			break;
		case ":storeRewrite":
			subProof = convertRewriteStore(rewriteStmt, stmtParams[0], stmtParams[1]);
			break;
		case ":divisible":
		case ":div1":
		case ":div-1":
		case ":divConst":
		case ":modulo1":
		case ":modulo-1":
		case ":moduloConst":
		case ":modulo":
		default:
			// throw new AssertionError("Unknown Rewrite Rule: " + annotTerm);
			subProof = mProofRules.oracle(termToProofLiterals(rewriteStmt), annotTerm.getAnnotations());
		}
		assert checkProof(subProof, termToProofLiterals(rewriteStmt));
		return annotateProved(rewriteStmt, subProof);
	}

	/**
	 * Convert a Farkas lemma.
	 *
	 * @param clause       the clause to convert
	 * @param coefficients the argument of the :LA annotation, which is the list of
	 *                     Farkas coefficients.
	 */
	private Term convertLALemma(final Term[] clause, final Term[] coefficients) {
		assert clause.length == coefficients.length;
		final Theory theory = mSkript.getTheory();
		final BigInteger[] coeffs = new BigInteger[coefficients.length];
		final Term[] atoms = new Term[clause.length];
		final Term[] quotedAtoms = new Term[clause.length];
		final BitSet polarities = new BitSet();
		final Term[] realAtoms = new Term[clause.length];
		final Term[] realAtomProofs = new Term[clause.length];

		for (int i = 0; i < clause.length; i++) {
			final Rational coeff = parseConstant(coefficients[i]);
			assert coeff.isIntegral() && coeff != Rational.ZERO;
			coeffs[i] = coeff.numerator().abs();

			final Term lit = clause[i];
			final boolean isNegated = isApplication("not", lit);
			final Term quotedAtom = isNegated ? negate(lit) : lit;
			final Term atom = unquote(quotedAtom);
			final Term[] atomParams = ((ApplicationTerm) atom).getParameters();
			Term realAtom;
			Term realAtomProof;

			if (isApplication("=", atom)) {
				assert isNegated;
				if (coeff.signum() > 0) {
					realAtom = theory.term("<=", atomParams[0], atomParams[1]);
					realAtomProof = mProofRules.eqLeq(atomParams[0], atomParams[1]);
				} else {
					realAtom = theory.term("<=", atomParams[1], atomParams[0]);
					realAtomProof = mProofRules.resolutionRule(theory.term("=", atomParams[1], atomParams[0]),
							mProofRules.symm(atomParams[1], atomParams[0]),
							mProofRules.eqLeq(atomParams[1], atomParams[0]));
				}
			} else if (isNegated) {
				assert coeff.signum() > 0;
				realAtom = atom;
				realAtomProof = null;
			} else {
				assert coeff.signum() < 0;
				if (isApplication("<=", atom)) {
					final Sort sort = atomParams[0].getSort();
					if (sort.getName().equals(SMTLIBConstants.INT)) {
						assert isZero(atomParams[1]);
						realAtom = theory.term("<=", Rational.ONE.toTerm(sort), atomParams[0]);
						realAtomProof = mProofRules.totalInt(atomParams[0], BigInteger.ZERO);
					} else {
						realAtom = theory.term("<", atomParams[1], atomParams[0]);
						realAtomProof = mProofRules.total(atomParams[0],  atomParams[1]);
					}
				} else {
					realAtom = theory.term("<=", atomParams[1], atomParams[0]);
					realAtomProof = mProofRules.total(atomParams[1],  atomParams[0]);
				}
			}
			realAtoms[i] = realAtom;
			realAtomProofs[i] = realAtomProof;
			atoms[i] = atom;
			quotedAtoms[i] = quotedAtom;
			polarities.set(i, !isNegated);
		}
		Term proof = mProofRules.farkas(realAtoms, coeffs);
		for (int i = 0; i < atoms.length; i++) {
			if (realAtomProofs[i] != null) {
				proof = mProofRules.resolutionRule(realAtoms[i], realAtomProofs[i], proof);
			}
			proof = removeQuoted(proof, quotedAtoms[i], atoms[i], polarities.get(i));
		}
		return proof;
	}

	/**
	 * Convert a trichotomy lemma to a proof.
	 *
	 * @param clause
	 *            the clause to check.
	 */
	private Term convertTrichotomy(final Term[] clause) {
		assert clause.length == 3;
		final Theory theory = clause[0].getTheory();
		Term quotedEq = null, eq = null;
		Term quotedLt = null, lt = null;
		Term quotedGt = null, gt = null;
		for (final Term lit : clause) {
			final boolean isNegated = isApplication("not", lit);
			final Term quotedAtom = isNegated ? ((ApplicationTerm) lit).getParameters()[0] : lit;
			final Term atom = unquote(quotedAtom);
			assert isZero(((ApplicationTerm) atom).getParameters()[1]);

			if (isApplication("=", atom)) {
				assert !isNegated && eq == null;
				quotedEq = quotedAtom;
				eq = atom;
			} else if (isApplication("<=", atom) || isApplication("<", atom)) {
				if (isNegated) {
					assert gt == null;
					quotedGt = quotedAtom;
					gt = atom;
				} else {
					assert lt == null;
					quotedLt = quotedAtom;
					lt = atom;
				}
			} else {
				throw new AssertionError();
			}
		}
		final Term[] sides = ((ApplicationTerm) eq).getParameters();
		Term proof = mProofRules.trichotomy(sides[0], sides[1]);
		// gt term needs to be negated
		final Term realGt = theory.term("<", sides[1], sides[0]);
		proof = mProofRules.resolutionRule(realGt, proof,
				mProofRules.farkas(new Term[] { realGt, gt }, new BigInteger[] { BigInteger.ONE, BigInteger.ONE }));
		// lt may need to be converted to <=
		if (isApplication("<=", lt)) {
			final Term[] ltSides = ((ApplicationTerm) lt).getParameters();
			assert isZero(ltSides[1]);
			final Term one = Rational.ONE.toTerm(ltSides[0].getSort());
			// the literal in the new trichotomoy clause
			final Term realLt = theory.term("<", sides[0], sides[1]);
			// the other literal in the ltInt clause that we need to show with farkas.
			final Term realLeq = theory.term("<=", one, ltSides[0]);
			proof = mProofRules.resolutionRule(realLt, proof,
					mProofRules.resolutionRule(realLeq, mProofRules.totalInt(ltSides[0], BigInteger.ZERO),
							mProofRules.farkas(new Term[] { realLeq, realLt },
									new BigInteger[] { BigInteger.ONE, BigInteger.ONE })));
		}
		proof = removeQuoted(proof, quotedGt, gt, false);
		proof = removeQuoted(proof, quotedLt, lt, true);
		proof = removeQuoted(proof, quotedEq, eq, true);
		return proof;
	}

	/**
	 * Convert an EQ lemma to minimal proof.
	 *
	 * @param clause the clause to check
	 * @return the proof.
	 */
	private Term convertEQLemma(final Term[] clause) {
		assert clause.length == 2;
		Term quotedNegAtom;
		Term quotedPosAtom;

		if (isApplication("not", clause[0])) {
			quotedNegAtom = negate(clause[0]);
			quotedPosAtom = clause[1];
		} else {
			assert isApplication("not", clause[1]);
			quotedNegAtom = negate(clause[1]);
			quotedPosAtom = clause[0];
		}
		final Term negAtom = unquote(quotedNegAtom);
		final Term posAtom = unquote(quotedPosAtom);

		assert isApplication("=", negAtom) && isApplication("=", posAtom);
		final Term[] negAtomArgs = ((ApplicationTerm) negAtom).getParameters();
		final Term[] posAtomArgs = ((ApplicationTerm) posAtom).getParameters();
		final SMTAffineTerm negDiff = new SMTAffineTerm(negAtomArgs[0]);
		negDiff.add(Rational.MONE, negAtomArgs[1]);
		final SMTAffineTerm posDiff = new SMTAffineTerm(posAtomArgs[0]);
		posDiff.add(Rational.MONE, posAtomArgs[1]);
		Rational multiplier = posDiff.getGcd().div(negDiff.getGcd());
		negDiff.mul(multiplier);
		if (!negDiff.equals(posDiff)) {
			negDiff.negate();
			multiplier = multiplier.negate();
		}
		assert negDiff.equals(posDiff);
		Term proof = proveEqWithMultiplier(negAtomArgs, posAtomArgs, multiplier);
		proof = removeQuoted(proof, quotedNegAtom, negAtom, false);
		proof = removeQuoted(proof, quotedPosAtom, posAtom, true);
		return proof;
	}

	/**
	 *  Collect literals in a CC or array lemma clause
	 *
	 *  @param clause the clause.
	 *  @param equalities  HashMap to store equalities (negated in the clause).
	 *  @param disequalities HashMap to store disequalities (positive in the clause).
	 */
	private void collectEqualities(final Term[] clause, final HashMap<SymmetricPair<Term>, Term> equalities,
			final HashMap<SymmetricPair<Term>, Term> disequalities) {
		for (final Term literal : clause) {
			final boolean negated = isApplication("not", literal);
			final Term quotedAtom = negated ? ((ApplicationTerm) literal).getParameters()[0] : literal;
			final Term atom = unquote(quotedAtom);
			assert isApplication("=", atom);
			final Term[] sides = ((ApplicationTerm) atom).getParameters();
			assert sides.length == 2;
			if (negated) {
				// negated atom in clause -> equality in conflict
				equalities.put(new SymmetricPair<>(sides[0], sides[1]), quotedAtom);
			} else {
				disequalities.put(new SymmetricPair<>(sides[0], sides[1]), quotedAtom);
			}
		}
	}

	/**
	 * Convert a CC lemma to a minimal proof.
	 *
	 * @param clause       the clause to check
	 * @param ccAnnotation the argument of the :CC annotation.
	 */
	private Term convertCCLemma(final Term[] clause, final Object[] ccAnnotation) {
		assert ccAnnotation.length >= 3 && ccAnnotation[0] instanceof Term && ccAnnotation[1] == ":subpath"
				&& ccAnnotation[2] instanceof Term[];
		final int startSubpathAnnot = 1;

		// The goal equality
		final Term goalEquality = unquote((Term) ccAnnotation[0]);
		final Theory theory = goalEquality.getTheory();

		/* collect literals and search for the disequality */
		final HashMap<SymmetricPair<Term>, Term> allEqualities = new HashMap<>();
		final HashMap<SymmetricPair<Term>, Term> allDisequalities = new HashMap<>();
		collectEqualities(clause, allEqualities, allDisequalities);
		assert allDisequalities.size() <= 1;

		final Term[] mainPath = (Term[]) ccAnnotation[startSubpathAnnot + 1];
		assert mainPath.length >= 2 : "Main path too short in CC lemma";
		assert isApplication("=", goalEquality) : "Goal equality is not an equality in CC lemma";
		final Term[] sides = ((ApplicationTerm) goalEquality).getParameters();
		assert sides.length == 2 : "Expected binary equality in CC lemma";
		assert new SymmetricPair<>(mainPath[0], mainPath[mainPath.length - 1])
				.equals(new SymmetricPair<>(sides[0], sides[1])) : "Did not explain main equality " + goalEquality;

		Term proof;
		final HashSet<Term> neededEqualities = new HashSet<>();
		final Term mainPathEquality = theory.term("=", mainPath[0], mainPath[mainPath.length - 1]);
		if (mainPath.length == 2) {
			// This must be a congruence lemma
			assert mainPath[0] instanceof ApplicationTerm && mainPath[1] instanceof ApplicationTerm;
			final ApplicationTerm lhs = (ApplicationTerm) mainPath[0];
			final ApplicationTerm rhs = (ApplicationTerm) mainPath[1];
			proof = mProofRules.cong(lhs, rhs);

			// check that functions are the same and have the same number of parameters
			assert lhs.getFunction() == rhs.getFunction() && lhs.getParameters().length == rhs.getParameters().length;
			// check if each parameter is identical or equal
			final Term[] lhsParams = lhs.getParameters();
			final Term[] rhsParams = rhs.getParameters();
			assert lhsParams.length == rhsParams.length;
			for (int i = 0; i < lhsParams.length; i++) {
				neededEqualities.add(theory.term(SMTLIBConstants.EQUALS, lhsParams[i], rhsParams[i]));
			}
		} else {
			// This is a transitivity lemma
			proof = mProofRules.trans(mainPath);
			for (int i = 0; i < mainPath.length - 1; i++) {
				neededEqualities.add(theory.term(SMTLIBConstants.EQUALS, mainPath[i], mainPath[i + 1]));
			}
		}
		final Set<Term> neededDisequalities = Collections.singleton(mainPathEquality);
		proof = resolveNeededEqualities(proof, allEqualities, allDisequalities, neededEqualities, neededDisequalities);
		return proof;
	}

	/**
	 * Checks whether {@code term1} is {@code (store term2 idx val)} or {@code term2} is {@code (store term1 idx val)}.
	 *
	 * @param term0
	 *            the first array term.
	 * @param term1
	 *            the second array term
	 * @return 0 if term0 is a store over term1, 1 if vice versa. -1 if neither.
	 */
	private int checkStoreIndex(final Term term0, final Term term1) {
		if (isApplication("store", term0)) {
			final Term[] storeArgs = ((ApplicationTerm) term0).getParameters();
			if (storeArgs[0] == term1) {
				return 0;
			}
		}
		if (isApplication("store", term1)) {
			final Term[] storeArgs = ((ApplicationTerm) term1).getParameters();
			if (storeArgs[0] == term0) {
				return 1;
			}
		}
		return -1;
	}


	/**
	 * Check if each step in an array path is valid. This means, for each pair of consecutive terms, either there is a
	 * strong path between the two, or there exists a select path explaining element equality of array terms at the weak
	 * path index, or it is a weak store step, or a congruence. This reports errors using reportError.
	 *
	 * @param weakIdx
	 *            the weak path index or null for subpaths.
	 * @param path
	 *            the path to check.
	 * @param equalities
	 *            the equality literals from the clause.
	 * @param disequalities
	 *            the index disequality literals from the clause.
	 * @param weakPaths
	 *            the weak paths (given by their weak index) needed for the main path in array lemmas, null if path is
	 *            not the main path.
	 */
	Term proveSelectOverPath(final Term weakIdx, final Term[] path,
			final Set<SymmetricPair<Term>> equalities, final Set<SymmetricPair<Term>> disequalities,
			final Set<Term> neededEqualities, final Set<Term> neededDisequalities) {
		// note that a read-const-weakeq path can have length 1
		assert path.length >= 1;
		final Theory theory = path[0].getTheory();
		final Term[] selectChain = new Term[path.length];
		final Term[] proofSelectEq = new Term[path.length - 1];
		for (int i = 0; i < path.length; i++) {
			selectChain[i] = theory.term(SMTLIBConstants.SELECT, path[i], weakIdx);
		}
		for (int i = 0; i < path.length - 1; i++) {
			final SymmetricPair<Term> pair = new SymmetricPair<>(path[i], path[i + 1]);
			/* check for strong path first */
			if (equalities.contains(pair)) {
				proofSelectEq[i] = mProofRules.cong(selectChain[i], selectChain[i + 1]);
				neededEqualities.add(theory.term(SMTLIBConstants.EQUALS, path[i], path[i + 1]));
				neededEqualities.add(theory.term(SMTLIBConstants.EQUALS, weakIdx, weakIdx));
				continue;
			}
			/* check for weak store step */
			final int storePos = checkStoreIndex(path[i], path[i+1]);
			if (storePos >= 0) {
				// this is a step from a to (store a storeIndex v). Check if storeIndex is okay.
				final Term storeTerm = path[i + storePos];
				final Term storeIdx = ((ApplicationTerm) storeTerm).getParameters()[1];
				if (disequalities.contains(new SymmetricPair<>(weakIdx, storeIdx))
						|| proveTrivialDisequality(weakIdx, storeIdx) != null) {
					final Term storeVal = ((ApplicationTerm) storeTerm).getParameters()[2];
					neededDisequalities.add(theory.term(SMTLIBConstants.EQUALS, storeIdx, weakIdx));
					Term proof = mProofRules.selectStore2(path[i + 1 - storePos], storeIdx, storeVal, weakIdx);
					if (storePos == 1) {
						proof = res(theory.term(SMTLIBConstants.EQUALS, selectChain[i + 1], selectChain[i]),
								proof, mProofRules.symm(selectChain[i], selectChain[i + 1]));
					}
					proofSelectEq[i] = proof;
					continue;
				}
			}
			/* TODO check for select edge (only for weakeq-ext) */
			throw new AssertionError();
		}
		if (selectChain.length == 1) {
			return mProofRules.refl(selectChain[0]);
		}
		Term proof = selectChain.length > 2 ? mProofRules.trans(selectChain) : null;
		for (int i = 0; i < path.length - 1; i++) {
			proof = res(theory.term(SMTLIBConstants.EQUALS, selectChain[i], selectChain[i + 1]),
					proofSelectEq[i], proof);
		}
		return proof;
	}

	/**
	 * Convert an array lemma of type :read-const-weakeq to a simplified proof.
	 *
	 * @param type
	 *            the lemma type
	 * @param clause
	 *            the clause to check
	 * @param ccAnnotation
	 *            the argument of the lemma annotation.
	 */
	private Term convertArraySelectConstWeakEqLemma(final Term[] clause, final Object[] ccAnnotation) {
		assert ccAnnotation.length >= 3;
		final Theory theory = clause[0].getTheory();
		/*
		 * weakPaths maps from a symmetric pair to the set of weak indices such that a weak path was proven for this
		 * pair. strongPaths contains the sets of all proven strong paths.
		 */
		final HashMap<SymmetricPair<Term>, Term> allEqualities = new HashMap<>();
		/* indexDiseqs contains all index equalities in the clause */
		final HashMap<SymmetricPair<Term>, Term> allDisequalities = new HashMap<>();
		collectEqualities(clause, allEqualities, allDisequalities);

		final HashSet<Term> neededEqualities = new HashSet<>();
		final HashSet<Term> neededDisequalities = new HashSet<>();

		final Term goalEquality = unquote((Term) ccAnnotation[0]);
		assert isApplication("=", goalEquality);
		final Term[] goalTerms = ((ApplicationTerm) goalEquality).getParameters();
		assert goalTerms.length == 2;

		/*
		 * Check the paths in reverse order. Collect proven paths in a hash set, so that they can be used later.
		 */
		assert ccAnnotation.length == 3;
		assert ccAnnotation[1] == ":weakpath";
		final Object[] weakItems = (Object[]) ccAnnotation[2];
		assert weakItems.length == 2;
		final Term mainIdx = (Term) weakItems[0];
		final Term[] mainPath = (Term[]) weakItems[1];

		Term proof = proveSelectOverPath(mainIdx, mainPath, allEqualities.keySet(), allDisequalities.keySet(),
				neededEqualities, neededDisequalities);
		final Term firstTerm = theory.term("select", mainPath[0], mainIdx);
		final Term lastTerm = theory.term("select", mainPath[mainPath.length - 1], mainIdx);
		assert isApplication("const", mainPath[mainPath.length - 1]);
		final Term constParam = ((ApplicationTerm) mainPath[mainPath.length - 1]).getParameters()[0];
		final int goalOrder = goalTerms[1] == constParam ? 0 : 1;
		assert goalTerms[goalOrder] == mSkript.term("select", mainPath[0], mainIdx);
		assert goalTerms[1 - goalOrder] == constParam;
		proof = res(theory.term("=", firstTerm, lastTerm), proof, mProofRules.trans(firstTerm, lastTerm, constParam));
		proof = res(theory.term("=", lastTerm, constParam), mProofRules.constArray(constParam, mainIdx), proof);
		neededDisequalities.add(theory.term("=", firstTerm, constParam));
		return resolveNeededEqualities(proof, allEqualities, allDisequalities, neededEqualities, neededDisequalities);
	}

	/**
	 * Convert an array lemma of type :read-over-weakeq to a simplified proof.
	 *
	 * @param type
	 *            the lemma type
	 * @param clause
	 *            the clause to check
	 * @param ccAnnotation
	 *            the argument of the lemma annotation.
	 */
	private Term convertArraySelectWeakEqLemma(final Term[] clause, final Object[] ccAnnotation) {
		assert ccAnnotation.length >= 3;
		final Theory theory = clause[0].getTheory();
		/*
		 * weakPaths maps from a symmetric pair to the set of weak indices such that a weak path was proven for this
		 * pair. strongPaths contains the sets of all proven strong paths.
		 */
		final HashMap<SymmetricPair<Term>, Term> allEqualities = new HashMap<>();
		/* indexDiseqs contains all index equalities in the clause */
		final HashMap<SymmetricPair<Term>, Term> allDisequalities = new HashMap<>();
		collectEqualities(clause, allEqualities, allDisequalities);

		final HashSet<Term> neededEqualities = new HashSet<>();
		final HashSet<Term> neededDisequalities = new HashSet<>();

		final Term goalEquality = unquote((Term) ccAnnotation[0]);
		assert isApplication("=", goalEquality);
		final Term[] goalTerms = ((ApplicationTerm) goalEquality).getParameters();
		assert goalTerms.length == 2;

		/*
		 * Check the paths in reverse order. Collect proven paths in a hash set, so that they can be used later.
		 */
		assert ccAnnotation.length == 3;
		assert ccAnnotation[1] == ":weakpath";
		final Object[] weakItems = (Object[]) ccAnnotation[2];
		assert weakItems.length == 2;
		final Term mainIdx = (Term) weakItems[0];
		final Term[] mainPath = (Term[]) weakItems[1];

		Term proof = proveSelectOverPath(mainIdx, mainPath, allEqualities.keySet(), allDisequalities.keySet(),
				neededEqualities, neededDisequalities);
		assert isApplication("select", goalTerms[0]) && isApplication("select", goalTerms[1]);
		final int goalOrder = ((ApplicationTerm) goalTerms[0]).getParameters()[0] == mainPath[0] ? 0 : 1;
		final Term goal1 = goalTerms[goalOrder];
		final Term goal2 = goalTerms[1 - goalOrder];
		final Term firstTerm = theory.term("select", mainPath[0], mainIdx);
		final Term lastTerm = theory.term("select", mainPath[mainPath.length - 1], mainIdx);
		if (goal1 != firstTerm) {
			assert mainPath[0] == ((ApplicationTerm) goal1).getParameters()[0];
			final Term goalIdx = ((ApplicationTerm) goal1).getParameters()[1];
			proof = res(theory.term("=", firstTerm, lastTerm), proof, mProofRules.trans(goal1, firstTerm, lastTerm));
			proof = res(theory.term("=", goal1, firstTerm), mProofRules.cong(goal1, firstTerm), proof);
			neededEqualities.add(theory.term("=", goalIdx, mainIdx));
			neededEqualities.add(theory.term("=", mainPath[0], mainPath[0]));
		}
		if (goal2 != lastTerm) {
			assert mainPath[mainPath.length - 1] == ((ApplicationTerm) goal2).getParameters()[0];
			final Term goalIdx = ((ApplicationTerm) goal2).getParameters()[1];
			proof = res(theory.term("=", goal1, lastTerm), proof, mProofRules.trans(goal1, lastTerm, goal2));
			proof = res(theory.term("=", lastTerm, goal2), mProofRules.cong(lastTerm, goal2), proof);
			neededEqualities.add(theory.term("=", mainIdx, goalIdx));
			neededEqualities.add(theory.term("=", mainPath[mainPath.length - 1], mainPath[mainPath.length - 1]));
		}
		neededDisequalities.add(theory.term("=", goal1, goal2));
		return resolveNeededEqualities(proof, allEqualities, allDisequalities, neededEqualities, neededDisequalities);
	}

	/**
	 * Convert an instantiation lemma to a minimal proof.
	 *
	 * @param clause       the clause to convert
	 * @param instAnnotation the argument of the :inst annotation.
	 */
	private Term convertInstLemma(final Term[] clause, final Object[] quantAnnotation) {
		// the first literal in the lemma is a negated universally quantified literal.
		assert isApplication("not", clause[0]);
		final Term quotedForall = ((ApplicationTerm) clause[0]).getParameters()[0];
		final Term firstAtom = unquote(quotedForall);
		assert firstAtom instanceof QuantifiedFormula
				&& ((QuantifiedFormula) firstAtom).getQuantifier() == QuantifiedFormula.FORALL;

		// Check that the annotation of the lemma is well-formed.
		assert quantAnnotation.length == 5
				&& quantAnnotation[0] == ":subs" && (quantAnnotation[2] == ":conflict"
						|| quantAnnotation[2] == ":e-matching" || quantAnnotation[2] == ":enumeration")
				&& quantAnnotation[3] == ":subproof";
		final Term[] subst = (Term[]) quantAnnotation[1];
		final AnnotatedTerm annotSubproof = (AnnotatedTerm) quantAnnotation[4];
		final Term provedEq = provedTerm(annotSubproof);
		final Term subproof = stripAnnotation(annotSubproof);
		assert isApplication("=", provedEq);
		final Term[] provedEqSides = ((ApplicationTerm) provedEq).getParameters();

		final QuantifiedFormula forall = (QuantifiedFormula) firstAtom;
		final AnnotatedTerm substitute = substituteInQuantInst(subst, forall);
		assert provedTerm(substitute) == provedEqSides[0];
		final Term quotedEq = mSkript.term(SMTLIBConstants.EQUALS, quotedForall, forall);
		Term proof = mProofRules.resolutionRule(quotedEq, mProofRules.delAnnot(quotedForall),
				mProofRules.resolutionRule(forall, mProofRules.iffElim2(quotedEq), stripAnnotation(substitute)));
		proof = mProofRules.resolutionRule(provedEqSides[0], proof, mProofRules.iffElim2(provedEq));
		proof = mProofRules.resolutionRule(provedEq, subproof, proof);
		Term[] result = new Term[] { provedEqSides[1] };
		if (isApplication("false", provedEqSides[1])) {
			result = new Term[0];
			proof = mProofRules.resolutionRule(provedEqSides[1], proof, mProofRules.falseElim());
		} else if (isApplication("or", provedEqSides[1])) {
			result = ((ApplicationTerm) provedEqSides[1]).getParameters();
			proof = mProofRules.resolutionRule(provedEqSides[1], proof, mProofRules.orElim(provedEqSides[1]));
		}
		for (int i = 0; i < result.length; i++) {
			proof = removeNot(proof, result[i], true);
		}
		return proof;
	}

	private Term convertLemma(final Term[] newParams) {
		/*
		 * The argument of the @lemma application is a single clause annotated with the lemma type, which has as object
		 * all the necessary annotation. For example (@lemma (! (or (not (= a b)) (not (= b c)) (= a c)) :CC ((= a c)
		 * :path (a b c))))
		 */
		assert newParams.length == 1;
		final AnnotatedTerm annTerm = (AnnotatedTerm) newParams[0];
		final String lemmaType = annTerm.getAnnotations()[0].getKey();
		final Object lemmaAnnotation = annTerm.getAnnotations()[0].getValue();
		final Term lemma = annTerm.getSubterm();
		final Term[] clause = termToClause(lemma);
		Term subProof;

		switch (lemmaType) {
		case ":CC":
			subProof = convertCCLemma(clause, (Object[]) lemmaAnnotation);
			break;
		case ":read-over-weakeq":
			subProof = convertArraySelectWeakEqLemma(clause, (Object[]) lemmaAnnotation);
			break;
		case ":read-const-weakeq":
			subProof = convertArraySelectConstWeakEqLemma(clause, (Object[]) lemmaAnnotation);
			break;
		case ":EQ":
			subProof = convertEQLemma(clause);
			break;
		case ":LA":
			subProof = convertLALemma(clause, (Term[]) lemmaAnnotation);
			break;
		case ":trichotomy":
			subProof = convertTrichotomy(clause);
			break;
		case ":inst":
			subProof = convertInstLemma(clause, (Object[]) lemmaAnnotation);
			break;
		default: {
			subProof = mProofRules.oracle(termToProofLiterals(lemma), annTerm.getAnnotations());
		}
		}
		assert checkProof(subProof, termToProofLiterals(lemma));
		return subProof;
	}

	private Term convertExists(final Term[] newParams) {
		final Theory theory = mSkript.getTheory();
		final AnnotatedTerm annotatedTerm = (AnnotatedTerm) newParams[0];
		final Annotation varAnnot = annotatedTerm.getAnnotations()[0];
		assert annotatedTerm.getAnnotations().length == 1 && varAnnot.getKey() == ":vars"
				&& (varAnnot.getValue() instanceof TermVariable[]);
		final TermVariable[] vars = (TermVariable[]) varAnnot.getValue();

		final Term subProof = annotatedTerm.getSubterm();
		/* Check that subproof is an equality */
		final ApplicationTerm subEquality = (ApplicationTerm) provedTerm((AnnotatedTerm) subProof);
		assert isApplication("=", subEquality);

		Term proof = subproof((AnnotatedTerm) subProof);

		/* compute the proven equality (= (exists (...) lhs) (exists (...) rhs)) */
		final FormulaUnLet unletter = new FormulaUnLet();
		final Term lhs = subEquality.getParameters()[0];
		final Term rhs = subEquality.getParameters()[1];

		final Term[] skolemLhs = mProofRules.getSkolemVars(vars, lhs, false);
		final Term[] skolemRhs = mProofRules.getSkolemVars(vars, rhs, false);
		final Term letLhsEq = unletter.unlet(theory.let(vars, skolemLhs, subEquality));
		final Term letLhsLhs = unletter.unlet(theory.let(vars, skolemLhs, lhs));
		final Term letLhsRhs = unletter.unlet(theory.let(vars, skolemLhs, rhs));
		final Term letLhsProof = unletter.unlet(theory.let(vars, skolemLhs, proof));
		final QuantifiedFormula exLhs = (QuantifiedFormula) theory.exists(vars, lhs);
		final Term letRhsEq = unletter.unlet(theory.let(vars, skolemRhs, subEquality));
		final Term letRhsRhs = unletter.unlet(theory.let(vars, skolemRhs, rhs));
		final Term letRhsLhs = unletter.unlet(theory.let(vars, skolemRhs, lhs));
		final Term letRhsProof = unletter.unlet(theory.let(vars, skolemRhs, proof));
		final QuantifiedFormula exRhs = (QuantifiedFormula) theory.exists(vars, rhs);
		final Term newEquality = theory.term("=", exLhs, exRhs);

		final Term proof1 = mProofRules.resolutionRule(letRhsRhs, mProofRules.existsElim(exRhs),
				mProofRules.resolutionRule(letRhsLhs,
						mProofRules.resolutionRule(letRhsEq, letRhsProof, mProofRules.iffElim1(letRhsEq)),
						mProofRules.existsIntro(skolemRhs, exLhs)));
		final Term proof2 = mProofRules.resolutionRule(letLhsLhs, mProofRules.existsElim(exLhs),
				mProofRules.resolutionRule(letLhsRhs,
						mProofRules.resolutionRule(letLhsEq, letLhsProof, mProofRules.iffElim2(letLhsEq)),
						mProofRules.existsIntro(skolemLhs, exRhs)));
		proof = mProofRules.resolutionRule(exLhs,
				mProofRules.resolutionRule(exRhs, mProofRules.iffIntro1(newEquality), proof1),
				mProofRules.resolutionRule(exRhs, proof2, mProofRules.iffIntro2(newEquality)));
		return annotateProved(newEquality, proof);
	}

	private Term convertAllIntro(final Term[] newParams) {
		final AnnotatedTerm annotatedTerm = (AnnotatedTerm) newParams[0];
		final Annotation varAnnot = annotatedTerm.getAnnotations()[0];
		if (annotatedTerm.getAnnotations().length != 1 || varAnnot.getKey() != ":vars"
				|| !(varAnnot.getValue() instanceof TermVariable[])) {
			throw new AssertionError("@allIntro with malformed annotation");
		}
		// TODO this is madness; should we remember the proved clause instead?
		Term proof = annotatedTerm.getSubterm();
		final ProofLiteral[] lits = new MinimalProofChecker(mSkript, mLogger).getProvedClause(proof);
		final Term[] litsAsTerms = new Term[lits.length];
		for (int i = 0; i < lits.length; i++) {
			final Term term = lits[i].getAtom();
			if (lits[i].getPolarity()) {
				litsAsTerms[i] = term;
			} else {
				litsAsTerms[i] = mSkript.term(SMTLIBConstants.NOT, term);
				proof = mProofRules.resolutionRule(term, mProofRules.notIntro(litsAsTerms[i]), proof);
			}
		}
		Term provedClause;
		if (litsAsTerms.length == 1) {
			provedClause = litsAsTerms[0];
		} else {
			provedClause = mSkript.term(SMTLIBConstants.OR, litsAsTerms);
			for (int i = 0; i < lits.length; i++) {
				proof = mProofRules.resolutionRule(litsAsTerms[i], proof, mProofRules.orIntro(i, litsAsTerms[i]));
			}
		}
		final TermVariable[] vars = (TermVariable[]) varAnnot.getValue();
		final Term[] skolemTerms = mProofRules.getSkolemVars(vars, provedClause, true);
		proof = mSkript.let(vars, skolemTerms, proof);
		final Term lettedClause = mSkript.let(vars, skolemTerms, provedClause);
		final FormulaUnLet unletter = new FormulaUnLet();
		proof = unletter.unlet(proof);
		/* compute the resulting quantified term (forall (...) origTerm) */
		final Term forallClause = mSkript.quantifier(Script.FORALL, vars, provedClause);
		proof = mProofRules.resolutionRule(unletter.unlet(lettedClause), proof,
				mProofRules.forallIntro((QuantifiedFormula) forallClause));
		/* add quoted annotation */
		final Term quotedForallClause = mSkript.annotate(forallClause, new Annotation[] { new Annotation(":quoted", null) });
		final Term quotedEq = mSkript.term("=", quotedForallClause, forallClause);
		proof = mProofRules.resolutionRule(forallClause, proof,
				mProofRules.resolutionRule(quotedEq, mProofRules.delAnnot(quotedForallClause),
						mProofRules.iffElim1(quotedEq)));
		return proof;
	}

	@Override
	public void convertApplicationTerm(final ApplicationTerm old, final Term[] newParams) {
		assert old.getSort().getName() == ProofConstants.SORT_PROOF;
		switch (old.getFunction().getName()) {
		case ProofConstants.FN_RES: {
			/* convert super-resolution into simple resolution */
			setResult(convertResolution(newParams));
			return;
		}
		case ProofConstants.FN_CLAUSE: {
			setResult(convertClause(newParams));
			return;
		}
		case ProofConstants.FN_MP: {
			setResult(convertMP(newParams));
			return;
		}
		case ProofConstants.FN_ASSERTED:
		case ProofConstants.FN_ASSUMPTION: {
			setResult(convertAsserted(mProofRules.asserted(newParams[0])));
			return;
		}
		case ProofConstants.FN_TAUTOLOGY: {
			setResult(convertTautology(newParams[0]));
			return;
		}
		case ProofConstants.FN_REFL: {
			final Term t = newParams[0];
			setResult(annotateProved(t.getTheory().term(SMTLIBConstants.EQUALS, t, t), mProofRules.refl(t)));
			return;
		}
		case ProofConstants.FN_TRANS: {
			setResult(convertTrans(newParams));
			return;
		}
		case ProofConstants.FN_CONG: {
			setResult(convertCong(newParams));
			return;
		}
		case ProofConstants.FN_EXISTS: {
			setResult(convertExists(newParams));
			return;
		}
		case ProofConstants.FN_REWRITE: {
			setResult(convertRewrite(newParams));
			return;
		}
		case ProofConstants.FN_LEMMA: {
			setResult(convertLemma(newParams));
			return;
		}
		case ProofConstants.FN_ALLINTRO: {
			setResult(convertAllIntro(newParams));
			return;
		}
		default:
			throw new AssertionError("Cannot translate proof rule: " + old.getFunction());
		}
	}

	@Override
	public void convert(final Term term) {
		if (term.getSort().getName() != ProofConstants.SORT_PROOF) {
			// don't convert subterms that are not proofs
			if (!(term instanceof AnnotatedTerm) || ((AnnotatedTerm) term).getAnnotations()[0].getKey() != ":inst") {
				// but check that it is not an :inst annotation, that must be converted
				setResult(term);
				return;
			}
		}
		super.convert(term);
	}


	/* === Auxiliary functions === */
	Term unquote(final Term quotedTerm) {
		if (quotedTerm instanceof AnnotatedTerm) {
			final AnnotatedTerm annTerm = (AnnotatedTerm) quotedTerm;
			final Annotation[] annots = annTerm.getAnnotations();
			if (annots.length == 1) {
				final String annot = annots[0].getKey();
				if (annot == ":quoted" || annot == ":quotedCC" || annot == ":quotedLA"
						|| annot == ":quotedQuant") {
					final Term result = annTerm.getSubterm();
					return result;
				}
			}
		}
		throw new AssertionError("Expected quoted literal, but got " + quotedTerm);
	}

	Term unquoteExpand(final Term quotedTerm) {
		final ApplicationTerm auxTerm = (ApplicationTerm) ((ApplicationTerm) unquote(quotedTerm)).getParameters()[0];
		final LambdaTerm lambda = mAuxDefs.get(auxTerm.getFunction());
		return new FormulaUnLet()
				.unlet(mSkript.let(lambda.getVariables(), auxTerm.getParameters(), lambda.getSubterm()));
	}

	/**
	 * Negate a term, avoiding double negation. If formula is (not x) it returns x, otherwise it returns (not formula).
	 *
	 * @param formula
	 *            the formula to negate.
	 * @return the negated formula.
	 */
	Term negate(final Term formula) {
		if (isApplication("not", formula)) {
			return ((ApplicationTerm) formula).getParameters()[0];
		}
		return formula.getTheory().term("not", formula);
	}

	/**
	 * Parses a constant term. It handles Rationals given as ConstantTerm or parsed as div terms.
	 *
	 * @param term
	 *            the term to parse.
	 * @returns the parsed constant, null if parse error occured.
	 */
	Rational parseConstant(Term term) {
		term = SMTAffineTerm.parseConstant(term);
		if (term instanceof ConstantTerm && term.getSort().isNumericSort()) {
			return SMTAffineTerm.convertConstant((ConstantTerm) term);
		}
		return null;
	}

	/**
	 * Checks if a term is an application of an internal function symbol.
	 *
	 * @param funcSym
	 *            the expected function symbol.
	 * @param term
	 *            the term to check.
	 * @return true if term is an application of funcSym.
	 */
	boolean isApplication(final String funcSym, final Term term) {
		if (term instanceof ApplicationTerm) {
			final ApplicationTerm appTerm = (ApplicationTerm) term;
			final FunctionSymbol func = appTerm.getFunction();
			if (func.isIntern() && func.getName().equals(funcSym)) {
				return true;
			}
		}
		return false;
	}

	/**
	 * Checks if a term is an annotation term with a single annotation. Usually the annotation has no value, there are
	 * some exceptions that are checked.
	 *
	 * @param term
	 *            the term to check.
	 * @return the annotation or null if it is not a correct annotation.
	 */
	private Annotation getSingleAnnotation(final Term term) {
		if (term instanceof AnnotatedTerm) {
			final Annotation[] annots = ((AnnotatedTerm) term).getAnnotations();
			if (annots.length == 1) {
				final Annotation singleAnnot = annots[0];
				if (singleAnnot.getKey() == ":subst" || singleAnnot.getKey() == ":skolem"
						|| singleAnnot.getKey() == ":removeForall") {
					if (singleAnnot.getValue() instanceof Term[]) {
						return singleAnnot;
					}
				} else if (singleAnnot.getValue() == null) {
					return singleAnnot;
				}
			}
		}
		return null;
	}

	/**
	 * Checks if a term is zero, either Int or Real.
	 *
	 * @param zero
	 *            the term to check.
	 * @return true if zero is 0.
	 */
	boolean isZero(final Term zero) {
		return zero == Rational.ZERO.toTerm(zero.getSort());
	}

	/**
	 * Substitute terms in forallElim and remove all :quotedQuant.
	 *
	 * @param subst substitution
	 * @param qf    universal quantifier
	 * @return subsituted formula annotated with proof that qf implies substituted
	 *         formula.
	 */
	private AnnotatedTerm substituteInQuantInst(final Term[] subst, final QuantifiedFormula qf) {
		final TermVariable[] universalVars = qf.getVariables();
		final Map<TermVariable, Term> sigma = new HashMap<>();

		for (int i = 0; i < subst.length; i++) {
			if (subst[i] != universalVars[i]) {
				sigma.put(universalVars[i], subst[i]);
			}
		}

		final FormulaUnLet unletter = new FormulaUnLet();
		unletter.addSubstitutions(sigma);
		final Term subFormula = qf.getSubformula();
		Term[] lits;
		if (isApplication("or", subFormula)) {
			lits = ((ApplicationTerm) subFormula).getParameters();
		} else {
			lits = new Term[] { subFormula };
		}
		final Term[] substLitLhs = new Term[lits.length];
		final Term[] substLitRhs = new Term[lits.length];
		final Term[] substLitEqProofs = new Term[lits.length];
		boolean changed = false;
		for (int i = 0; i < lits.length; i++) {
			substLitLhs[i] = unletter.unlet(lits[i]);
			if (Collections.disjoint(Arrays.asList(lits[i].getFreeVars()), sigma.keySet())) {
				substLitRhs[i] = substLitLhs[i];
				substLitEqProofs[i] = mProofRules.refl(substLitLhs[i]);
			} else {
				final boolean isNeg = isApplication("not", substLitLhs[i]);
				final Term quotedAtom = isNeg ? negate(substLitLhs[i]) : substLitLhs[i];
				final Term atom = unquote(quotedAtom);
				Term litProof = mProofRules.delAnnot(quotedAtom);
				substLitRhs[i] = isNeg ? negate(atom) : atom;
				if (isNeg) {
					litProof = mProofRules.resolutionRule(mSkript.term(SMTLIBConstants.EQUALS, quotedAtom, atom),
							litProof, mProofRules.cong(substLitLhs[i], substLitRhs[i]));
				}
				substLitEqProofs[i] = litProof;
				changed = true;
			}
		}
		final Term rhs = lits.length == 1 ? substLitRhs[0] : mSkript.term(SMTLIBConstants.OR, substLitRhs);
		Term proof = mProofRules.forallElim(subst, qf);
		if (changed) {
			Term eqProof;
			final Term lhs;
			if (lits.length == 1) {
				lhs = substLitLhs[0];
				eqProof = substLitEqProofs[0];
			} else {
				lhs = mSkript.term(SMTLIBConstants.OR, substLitLhs);
				eqProof = mProofRules.cong(lhs, rhs);
				final HashSet<Term> seen = new HashSet<>();
				for (int i = 0; i < lits.length; i++) {
					if (seen.add(substLitEqProofs[i])) {
						eqProof = mProofRules.resolutionRule(
								mSkript.term(SMTLIBConstants.EQUALS, substLitLhs[i], substLitRhs[i]),
								substLitEqProofs[i], eqProof);
					}
				}
			}
			final Term eq = mSkript.term(SMTLIBConstants.EQUALS, lhs, rhs);
			proof = mProofRules.resolutionRule(lhs, proof,
					mProofRules.resolutionRule(eq, eqProof, mProofRules.iffElim2(eq)));
		}
		return (AnnotatedTerm) annotateProved(rhs, proof);
	}

	/**
	 * Prove that first and second are equal (modulo order of operands for +).
	 *
	 * @param first  the left-hand side of the equality
	 * @param second the right-hand side of the equality
	 * @return the proof for `(= first second)` or null if this is not a trivial disequality.
	 */
	private Term proveTrivialEquality(final Term first, final Term second) {
		if (first == second) {
			return mProofRules.refl(first);
		}
		if (!first.getSort().isNumericSort()) {
			return null;
		}
		final SMTAffineTerm diff = new SMTAffineTerm(second);
		diff.negate();
		diff.add(new SMTAffineTerm(first));
		if (diff.isConstant() && diff.getConstant().equals(Rational.ZERO)) {
			final Theory theory = first.getTheory();
			final Term ltTerm = theory.term(SMTLIBConstants.LT, first, second);
			final Term gtTerm = theory.term(SMTLIBConstants.LT, second, first);
			final BigInteger[] one = new BigInteger[] { BigInteger.ONE };
			return res(ltTerm, res(gtTerm, mProofRules.trichotomy(first, second),
					mProofRules.farkas(new Term[] { ltTerm }, one)),
					mProofRules.farkas(new Term[] { gtTerm }, one));
		} else {
			return null;
		}
	}

	/**
	 * Prove that the disequality between two terms is trivial. There are two cases,
	 * (1) the difference between the terms is constant and nonzero, e.g.
	 * {@code (= x (+ x 1))}, or (2) the difference contains only integer variables
	 * and the constant divided by the gcd of the factors is non-integral, e.g.,
	 * {@code (= (+ x (* 2 y)) (+ x (* 2 z) 1))}.
	 *
	 * @param first  the left-hand side of the equality
	 * @param second the right-hand side of the equality
	 * @return the proof for `~(= first second)` or null if this is not a trivial disequality.
	 */
	private Term proveTrivialDisequality(final Term first, final Term second) {
		final Theory theory = first.getTheory();
		final SMTAffineTerm diff = new SMTAffineTerm(first);
		diff.add(Rational.MONE, second);
		if (diff.isConstant()) {
			if (diff.getConstant().signum() > 0) {
				final Term leqLhs = theory.term(SMTLIBConstants.LEQ, first, second);
				return mProofRules.resolutionRule(leqLhs, mProofRules.eqLeq(first, second),
						mProofRules.farkas(new Term[] { leqLhs }, new BigInteger[] { BigInteger.ONE }));
			} else if (diff.getConstant().signum() < 0) {
				final Term leqLhs = theory.term(SMTLIBConstants.LEQ, second, first);
				final Term eqSwapped = theory.term(SMTLIBConstants.EQUALS, second, first);
				return mProofRules.resolutionRule(eqSwapped, mProofRules.symm(second, first),
						mProofRules.resolutionRule(leqLhs, mProofRules.eqLeq(second, first),
								mProofRules.farkas(new Term[] { leqLhs }, new BigInteger[] { BigInteger.ONE })));
			} else {
				return null;
			}
		} else {
			final Rational gcd = diff.getGcd();
			diff.div(gcd);
			final Rational bound = diff.getConstant().negate();
			if (!diff.isAllIntSummands() || bound.isIntegral()) {
				return null;
			}
			final Sort intSort = theory.getSort(SMTLIBConstants.INT);
			diff.add(bound);
			final Term intVar = diff.toTerm(intSort);
			final Term floorBound = bound.floor().toTerm(intSort);
			final Term ceilBound = bound.ceil().toTerm(intSort);
			assert ceilBound != floorBound;
			// show (ceil(bound) <= intVar) || (intVar <= floor(bound)
			final Term geqCeil = theory.term(SMTLIBConstants.LEQ, ceilBound, intVar);
			final Term leqFloor = theory.term(SMTLIBConstants.LEQ, intVar, floorBound);
			final Term proofIntCase = mProofRules.totalInt(intVar, bound.floor().numerator());
			// show inequality in both cases
			final Term leqLhs = theory.term(SMTLIBConstants.LEQ, first, second);
			final Term geqLhs = theory.term(SMTLIBConstants.LEQ, second, first);
			final Term eqSwapped = theory.term(SMTLIBConstants.EQUALS, second, first);
			final Term caseCeil = mProofRules.resolutionRule(leqLhs, mProofRules.eqLeq(first, second), mProofRules
					.farkas(new Term[] { leqLhs, geqCeil }, new BigInteger[] { gcd.denominator(), gcd.numerator() }));
			final Term caseFloor = mProofRules.resolutionRule(eqSwapped, mProofRules.symm(second, first),
					mProofRules.resolutionRule(geqLhs, mProofRules.eqLeq(second, first), mProofRules.farkas(
							new Term[] { geqLhs, leqFloor }, new BigInteger[] { gcd.denominator(), gcd.numerator() })));
			return mProofRules.resolutionRule(leqFloor, mProofRules.resolutionRule(geqCeil, proofIntCase, caseCeil),
					caseFloor);
		}
	}

	private Term proveAbsConstant(final Rational rat, final Sort sort) {
		final Theory theory = sort.getTheory();
		final Term x = rat.toTerm(sort);
		final Term absx = theory.term(SMTLIBConstants.ABS, x);
		final Term zero = Rational.ZERO.toTerm(sort);
		final Term geqXZero = theory.term(">=", x, zero);
		final Term absxDef = theory.term("ite", geqXZero, x, theory.term("-", x));
		Term proof = mProofRules.trans(absx, absxDef, rat.abs().toTerm(sort));
		proof = res(theory.term(SMTLIBConstants.EQUALS, absx, absxDef), mProofRules.expand(absx), proof);
		final Term geqToLeq = theory.term("=", geqXZero, theory.term("<=", zero, x));
		if (rat.signum() >= 0) {
			proof = res(theory.term(SMTLIBConstants.EQUALS, absxDef, x),
					mProofRules.ite1(absxDef), proof);
			proof = res(geqXZero, mProofRules.iffElim1(geqToLeq), proof);
			proof = res(theory.term(SMTLIBConstants.LEQ, zero, x),
					mProofRules.total(zero, x), proof);
			final Term ltTerm = theory.term(SMTLIBConstants.LT, x, zero);
			proof = res(ltTerm, proof,
					mProofRules.farkas(new Term[] { ltTerm }, new BigInteger[] { BigInteger.ONE }));
		} else {
			final Term minusX = theory.term("-", x);
			proof = res(theory.term(SMTLIBConstants.EQUALS, absxDef, rat.abs().toTerm(sort)),
					mProofRules.trans(absxDef, minusX, rat.abs().toTerm(sort)), proof);
			proof = res(theory.term(SMTLIBConstants.EQUALS, absxDef, theory.term("-", x)),
					mProofRules.ite2(absxDef), proof);
			proof = res(geqXZero, mProofRules.iffElim2(geqToLeq), proof);
			final Term leqTerm = theory.term(SMTLIBConstants.LEQ, zero, x);
			proof = res(leqTerm, proof,
					mProofRules.farkas(new Term[] { leqTerm }, new BigInteger[] { BigInteger.ONE }));
			final Term eqMinusX = theory.term(SMTLIBConstants.EQUALS, theory.term("-", x), rat.abs().toTerm(sort));
			proof = res(eqMinusX,
					mProofRules.oracle(new ProofLiteral[] { new ProofLiteral(eqMinusX, true)},
							new Annotation[] { ProofConstants.RW_CANONICAL_SUM }), proof);
		}
		proof = res(geqToLeq, mProofRules.geqDef(geqXZero), proof);
		return proof;
	}

	/**
	 * Prove the needed equalities and disequalities from their unquoted counterpart.  It also handles symmetric
	 * cases and trivial equalities/disequalities.
	 *
	 * @param proof  the proof that is modified to remove the equalities/disequalities
	 * @param allEqualities a hash map from symmetric pair to quoted equality as it appears (negated) in the clause.
	 * @param allDisequalities a hash map from symmetric pair to quoted equality as it appears (positive) in the clause.
	 * @param neededEqualities a set of needed equalities (occurring negative in the proved clause)
	 * @param neededDisequalities a set of needed disequalities (occurring positive in the proved clause).
	 * @return the modified proof.
	 */
	private Term resolveNeededEqualities(Term proof, final Map<SymmetricPair<Term>, Term> allEqualities,
			final Map<SymmetricPair<Term>, Term> allDisequalities, final Set<Term> neededEqualities,
			final Set<Term> neededDisequalities) {
		for (final Term eq : neededEqualities) {
			assert isApplication("=", eq);
			final Term[] eqParam = ((ApplicationTerm) eq).getParameters();
			final Term quotedEq = allEqualities.get(new SymmetricPair<>(eqParam[0], eqParam[1]));
			if (quotedEq != null) {
				final Term unquoteEq = unquote(quotedEq);
				if (unquoteEq != eq) {
					// need symmetry
					proof = res(eq, mProofRules.symm(eqParam[0], eqParam[1]), proof);
				}
			} else {
				final Term proofEq = proveTrivialEquality(eqParam[0], eqParam[1]);
				assert proofEq != null;
				proof = res(eq, proofEq, proof);
			}
		}
		for (final Term eq : neededDisequalities) {
			assert isApplication("=", eq);
			final Term[] eqParam = ((ApplicationTerm) eq).getParameters();
			final Term quotedEq = allDisequalities.get(new SymmetricPair<>(eqParam[0], eqParam[1]));
			if (quotedEq != null) {
				final Term unquoteEq = unquote(quotedEq);
				if (unquoteEq != eq) {
					// need symmetry
					proof = res(eq, proof, mProofRules.symm(eqParam[1], eqParam[0]));
				}
			} else {
				final Term proofEq = proveTrivialDisequality(eqParam[0], eqParam[1]);
				assert proofEq != null;
				proof = res(eq, proof, proofEq);
			}
		}
		for (final Term quotedEq : allEqualities.values()) {
			proof = removeQuoted(proof, quotedEq, unquote(quotedEq), false);
		}
		for (final Term quotedEq : allDisequalities.values()) {
			proof = removeQuoted(proof, quotedEq, unquote(quotedEq), true);
		}
		return proof;
	}

	/**
	 * Convert a clause term into an Array of terms, one entry for each disjunct.
	 * This also handles singleton and empty clause correctly.
	 *
	 * @param clauseTerm The term representing a clause.
	 * @return The disjuncts of the clause.
	 */
	private Term[] termToClause(final Term clauseTerm) {
		assert clauseTerm != null && clauseTerm.getSort().getName() == "Bool";
		if (isApplication("or", clauseTerm)) {
			return ((ApplicationTerm) clauseTerm).getParameters();
		} else if (isApplication("false", clauseTerm)) {
			return new Term[0];
		} else {
			/* in all other cases, this is a singleton clause. */
			return new Term[] { clauseTerm };
		}
	}

	/**
	 * Convert a clause term into an Array of proof literals, one entry for each
	 * disjunct. This also removes double negations.
	 *
	 * @param clauseTerm The term representing a clause.
	 * @return The disjuncts of the clause.
	 */
	private ProofLiteral[] termToProofLiterals(final Term clauseTerm) {
		final Term[] clauseLits = termToClause(clauseTerm);
		final ProofLiteral[] proofLits = new ProofLiteral[clauseLits.length];
		for (int i = 0; i < proofLits.length; i++) {
			Term lit = clauseLits[i];
			boolean polarity = true;
			while (isApplication("not", lit)) {
				lit = ((ApplicationTerm) lit).getParameters()[0];
				polarity = !polarity;
			}
			proofLits[i] = new ProofLiteral(lit, polarity);
		}
		return proofLits;
	}

	/**
	 * Prove an equality of the form `(= lhs true)`.
	 *
	 * @param equality      an equality of the form `(= lhs true)`.
	 * @param proofLeftTrue a proof for lhs, or `lhs, ~true`.
	 * @return a proof for the equality.
	 */
	private Term proveIffTrue(final Term equality, final Term proofLeftTrue) {
		assert isApplication("=", equality);
		final Term[] sides = ((ApplicationTerm) equality).getParameters();
		assert isApplication("true", sides[1]);
		return mProofRules.resolutionRule(sides[1], mProofRules.trueIntro(),
				mProofRules.resolutionRule(sides[0], proofLeftTrue, mProofRules.iffIntro2(equality)));
	}

	/**
	 * Prove an equality of the form `(= lhs false)`.
	 *
	 * @param equality      an equality of the form `(= lhs false)`.
	 * @param proofLeftTrue a proof for `~lhs` or `false, ~lhs`.
	 * @return a proof for the equality.
	 */
	private Term proveIffFalse(final Term equality, final Term proofLeftFalse) {
		assert isApplication("=", equality);
		final Term[] sides = ((ApplicationTerm) equality).getParameters();
		assert isApplication("false", sides[1]);
		return mProofRules.resolutionRule(sides[1],
				mProofRules.resolutionRule(sides[0], mProofRules.iffIntro1(equality), proofLeftFalse),
				mProofRules.falseElim());
	}

	private Term proveIff(final Term equality, final Term proofLeftToRight, final Term proofRightToLeft) {
		assert isApplication("=", equality);
		final Term[] sides = ((ApplicationTerm) equality).getParameters();
		assert sides.length == 2;
		if (isApplication("true", sides[1])) {
			// simpler proof for common case
			return proveIffTrue(equality, proofRightToLeft);
		} else if (isApplication("false", sides[1])) {
			return proveIffFalse(equality, proofLeftToRight);
		} else {
			return mProofRules.resolutionRule(sides[1],
					mProofRules.resolutionRule(sides[0], mProofRules.iffIntro1(equality), proofLeftToRight),
					mProofRules.resolutionRule(sides[0], proofRightToLeft, mProofRules.iffIntro2(equality)));
		}
	}

	/**
	 * Resolution rule which handles null proofs (for not resolving).
	 *
	 * @param pivot    The pivot literal.
	 * @param proofPos The proof proving `+ pivot`.
	 * @param proofNeg The proof proving `- pivot`.
	 * @return the combined proof.
	 */
	private Term res(final Term pivot, final Term proofPos, final Term proofNeg) {
		return proofPos == null ? proofNeg
				: proofNeg == null ? proofPos : mProofRules.resolutionRule(pivot, proofPos, proofNeg);
	}

	private Term proveAuxExpand(final Term quotedAtom, final Term expanded) {
		// prove the equality (= quotedAtom mainAtom)
		// where quotedAtom is (! (= auxTerm true) :quotedQuant)
		// and mainAtom is the expanded form of auxTerm.
		final ApplicationTerm auxTerm = (ApplicationTerm) ((ApplicationTerm) unquote(quotedAtom)).getParameters()[0];
		final Term unquotedAtom = ((AnnotatedTerm) quotedAtom).getSubterm();
		final Term trueTerm = mSkript.term(SMTLIBConstants.TRUE);
		final Term firstEq = mSkript.term(SMTLIBConstants.EQUALS, quotedAtom, unquotedAtom);
		final Term secondEq = mSkript.term(SMTLIBConstants.EQUALS, unquotedAtom, auxTerm);
		final Term thirdEq = mSkript.term(SMTLIBConstants.EQUALS, auxTerm, expanded);

		return mProofRules.resolutionRule(firstEq, mProofRules.delAnnot(quotedAtom),
				mProofRules.resolutionRule(secondEq,
						mProofRules.resolutionRule(trueTerm, mProofRules.trueIntro(),
								proveIff(secondEq, mProofRules.iffElim1(unquotedAtom),
										mProofRules.iffIntro2(unquotedAtom))),
						mProofRules.resolutionRule(thirdEq, mProofRules.expand(auxTerm),
								mProofRules.trans(quotedAtom, unquotedAtom, auxTerm, expanded))));
	}

	/**
	 * Proof a linear equality rhs from a linear equality lhs. This proves
	 *
	 * <pre>
	 * (=&gt; (= lhs[0] lhs[1]) (= rhs[0] rhs[1])
	 * </pre>
	 *
	 * where (lhs[0] - lhs[1]) * multiplier == (rhs[0] - rhs[1]).
	 *
	 * @param lhs        the terms that are known to be equal
	 * @param rhs        the terms that should be proved to be equal.
	 * @param multiplier the factor that makes the sides equal.
	 * @return the proof.
	 */
	private Term proveEqWithMultiplier(final Term[] lhs, final Term[] rhs, final Rational multiplier) {
		final Theory theory = lhs[0].getTheory();
		final Term leqLhs1 = theory.term(SMTLIBConstants.LEQ, lhs[0], lhs[1]);
		final Term leqLhs2 = theory.term(SMTLIBConstants.LEQ, lhs[1], lhs[0]);
		final Term lhsProof1 = mProofRules.eqLeq(lhs[0], lhs[1]);
		final Term lhsProof2 = mProofRules.resolutionRule(theory.term("=", lhs[1], lhs[0]),
				mProofRules.symm(lhs[1], lhs[0]), mProofRules.eqLeq(lhs[1], lhs[0]));
		final Term ltRhs1 = theory.term(SMTLIBConstants.LT, rhs[0], rhs[1]);
		final Term ltRhs2 = theory.term(SMTLIBConstants.LT, rhs[1], rhs[0]);
		final Term leqSwapped1 = multiplier.signum() < 0 ? leqLhs1 : leqLhs2;
		final Term leqSwapped2 = multiplier.signum() < 0 ? leqLhs2 : leqLhs1;
		final Term proofSwapped1 = multiplier.signum() < 0 ? lhsProof1 : lhsProof2;
		final Term proofSwapped2 = multiplier.signum() < 0 ? lhsProof2 : lhsProof1;
		final BigInteger[] coeffs = new BigInteger[] { multiplier.numerator().abs(), multiplier.denominator() };
		final Term farkas1 = mProofRules.farkas(new Term[] { leqSwapped1, ltRhs1 }, coeffs);
		final Term farkas2 = mProofRules.farkas(new Term[] { leqSwapped2, ltRhs2 }, coeffs);

		final Term proof1 = mProofRules.resolutionRule(leqSwapped1, proofSwapped1, farkas1);
		final Term proof2 = mProofRules.resolutionRule(leqSwapped2, proofSwapped2, farkas2);

		return mProofRules.resolutionRule(ltRhs1,
				mProofRules.resolutionRule(ltRhs2, mProofRules.trichotomy(rhs[0], rhs[1]), proof2),
				proof1);
	}

	private Term proveRewriteWithLinEq(final Term lhs, final Term rhs) {
		final Theory theory = lhs.getTheory();
		assert isApplication("=", lhs) && isApplication("=", rhs);

		final Term[] lhsParams = ((ApplicationTerm) lhs).getParameters();
		final Term[] rhsParams = ((ApplicationTerm) rhs).getParameters();
		final SMTAffineTerm lhsAffine = new SMTAffineTerm(lhsParams[0]);
		lhsAffine.add(Rational.MONE, lhsParams[1]);
		final SMTAffineTerm rhsAffine = new SMTAffineTerm(rhsParams[0]);
		rhsAffine.add(Rational.MONE, rhsParams[1]);
		// we cannot compute gcd on constants so check for this and bail out
		assert !lhsAffine.isConstant() && !rhsAffine.isConstant() : "A trivial equality was created";
		Rational multiplier = lhsAffine.getGcd().div(rhsAffine.getGcd());
		rhsAffine.mul(multiplier);
		final boolean swapSides = !lhsAffine.equals(rhsAffine);
		if (swapSides) {
			rhsAffine.negate();
			multiplier = multiplier.negate();
		}
		assert lhsAffine.equals(rhsAffine);
		return proveIff(theory.term(SMTLIBConstants.EQUALS, lhs, rhs),
				proveEqWithMultiplier(lhsParams, rhsParams, multiplier.inverse()),
				proveEqWithMultiplier(rhsParams, lhsParams, multiplier));
	}

	private Term proveRewriteWithLeq(final Term lhs, final Term rhs, final boolean normalizeGCD) {
		final Theory theory = lhs.getTheory();

		final boolean isGreater = isApplication(">", lhs) || isApplication(">=", lhs);
		final boolean rhsIsNegated = isApplication("not", rhs);
		final Term quotedRhsAtom = rhsIsNegated ? negate(rhs) : rhs;
		final boolean rhsIsQuoted = quotedRhsAtom instanceof AnnotatedTerm;
		final Term rhsAtom = rhsIsQuoted ? unquote(quotedRhsAtom) : quotedRhsAtom;
		Term[] lhsParam = ((ApplicationTerm) lhs).getParameters();
		final Term[] rhsAtomParam = ((ApplicationTerm) rhsAtom).getParameters();
		final boolean isStrictLhs = isApplication("<", lhs) || isApplication(">", lhs);
		final boolean isStrictRhsAtom = isApplication("<", rhsAtom);

		if (isGreater) {
			lhsParam = new Term[] { lhsParam[1], lhsParam[0] };
		}
		final Term posLhs = theory.term(isStrictLhs ? "<" : "<=", lhsParam[0], lhsParam[1]);
		final Term negLhs = theory.term(isStrictLhs ? "<=" : "<", lhsParam[1], lhsParam[0]);

		Rational gcd = Rational.ONE;
		boolean needsIntReasoning = false;
		if (normalizeGCD) {
			final SMTAffineTerm lhsAffine = new SMTAffineTerm(lhsParam[0]);
			lhsAffine.add(Rational.MONE, lhsParam[1]);
			gcd = lhsAffine.getGcd();

			// Round constant up for integers: (<= (x + 1.25) 0) --> (<= (x + 2) 0)
			if (lhsParam[0].getSort().getName().equals(SMTLIBConstants.INT)) {
				needsIntReasoning = !lhsAffine.getConstant().div(gcd).isIntegral() || rhsIsNegated;
			}
		}

		Term negRhsAtom;
		Term rhsTotality;
		if (needsIntReasoning) {
			assert isZero(rhsAtomParam[1]);
			assert !isStrictLhs && !isStrictRhsAtom;
			final Term one = Rational.ONE.toTerm(rhsAtomParam[1].getSort());
			negRhsAtom = theory.term("<=", one, rhsAtomParam[0]);
			rhsTotality = mProofRules.totalInt(rhsAtomParam[0], BigInteger.ZERO);
		} else {
			negRhsAtom = theory.term(isStrictRhsAtom ? "<=" : "<", rhsAtomParam[1], rhsAtomParam[0]);
			rhsTotality = mProofRules.total(rhsAtomParam[isStrictRhsAtom ? 1 : 0],
					rhsAtomParam[isStrictRhsAtom ? 0 : 1]);
		}
		Term proofToRhsAtom = mProofRules.farkas(new Term[] { rhsIsNegated ? negLhs : posLhs, negRhsAtom },
				new BigInteger[] { gcd.denominator(), gcd.numerator() } );
		proofToRhsAtom = mProofRules.resolutionRule(negRhsAtom, rhsTotality, proofToRhsAtom);
		Term proofFromRhsAtom = mProofRules.farkas(new Term[] { rhsIsNegated ? posLhs : negLhs, rhsAtom },
				new BigInteger[] { gcd.denominator(), gcd.numerator() } );
		Term unquoteEq = null;
		if (rhsIsQuoted) {
			unquoteEq = theory.term(SMTLIBConstants.EQUALS, quotedRhsAtom, rhsAtom);
			proofFromRhsAtom = mProofRules.resolutionRule(rhsAtom, mProofRules.iffElim2(unquoteEq), proofFromRhsAtom);
			proofToRhsAtom = mProofRules.resolutionRule(rhsAtom, proofToRhsAtom, mProofRules.iffElim1(unquoteEq));
		}
		Term proofLhsToRhs = rhsIsNegated
				? mProofRules.resolutionRule(quotedRhsAtom, mProofRules.notIntro(rhs), proofFromRhsAtom)
				: proofToRhsAtom;
		Term proofRhsToLhs = rhsIsNegated
				? mProofRules.resolutionRule(quotedRhsAtom, proofToRhsAtom, mProofRules.notElim(rhs))
				: proofFromRhsAtom;
		proofRhsToLhs = mProofRules.resolutionRule(negLhs,
				mProofRules.total(lhsParam[isStrictLhs ? 1 : 0], lhsParam[isStrictLhs ? 0 : 1]), proofRhsToLhs);
		Term greaterEq = null;
		if (isGreater) {
			greaterEq = theory.term("=", lhs, posLhs);
			proofLhsToRhs = mProofRules.resolutionRule(posLhs, mProofRules.iffElim2(greaterEq), proofLhsToRhs);
			proofRhsToLhs = mProofRules.resolutionRule(posLhs, proofRhsToLhs, mProofRules.iffElim1(greaterEq));

		}
		Term proof = proveIff(theory.term("=", lhs, rhs), proofLhsToRhs, proofRhsToLhs);
		if (rhsIsQuoted) {
			proof = mProofRules.resolutionRule(unquoteEq, mProofRules.delAnnot(quotedRhsAtom), proof);
		}
		if (isGreater) {
			proof = mProofRules.resolutionRule(greaterEq,
					isStrictLhs ? mProofRules.gtDef(lhs) : mProofRules.geqDef(lhs), proof);
		}
		return proof;
	}

	public Term transformProof(Term proof) {
		final CollectSkolemAux collector = new CollectSkolemAux();
		collector.transform(proof);
		mAuxDefs = collector.getAuxDef();
		proof = new RewriteSkolem(collector.getSkolems()).transform(proof);
		proof = super.transform(proof);
		return proof;
	}

	class CollectSkolemAux extends TermTransformer {
		private final HashMap<Term, Term> mSkolemFunctions = new HashMap<>();
		private final HashMap<FunctionSymbol, LambdaTerm> mQuantDefinedTerms = new HashMap<>();

		public HashMap<Term, Term> getSkolems() {
			return mSkolemFunctions;
		}

		public HashMap<FunctionSymbol, LambdaTerm> getAuxDef() {
			return mQuantDefinedTerms;
		}

		@Override
		public void convert(final Term term) {
			if (term.getSort().getName() != ProofConstants.SORT_PROOF) {
				setResult(term);
				return;
			}
			if (term instanceof ApplicationTerm) {
				final ApplicationTerm appTerm = (ApplicationTerm) term;
				if (appTerm.getFunction().getName().equals(ProofConstants.FN_REWRITE)) {
					final AnnotatedTerm annotTerm = (AnnotatedTerm) appTerm.getParameters()[0];
					switch (annotTerm.getAnnotations()[0].getKey()) {
					case ":intern":
						collectAuxFromIntern(annotTerm);
						break;
					}
					setResult(term);
					return;
				} else if (appTerm.getFunction().getName().equals(ProofConstants.FN_TAUTOLOGY)) {
					final AnnotatedTerm annotTerm = (AnnotatedTerm) appTerm.getParameters()[0];
					switch (annotTerm.getAnnotations()[0].getKey()) {
					case ":exists-":
						collectExistsElim(annotTerm);
						break;
						/*
					case ":or+":
					case ":or-":
					case ":and+":
					case ":and-":
					case ":=>+":
					case ":=>-":
					case ":excludedMiddle1":
					case ":excludedMiddle2": {
						assert isApplication(SMTLIBConstants.OR, annotTerm.getSubterm());
						final Term firstLit = ((ApplicationTerm) annotTerm.getSubterm()).getParameters()[0];
						if (firstLit instanceof AnnotatedTerm) {
							final AnnotatedTerm quotedTerm = (AnnotatedTerm) firstLit;
							if (quotedTerm.getAnnotations()[0].getKey().equals(":quotedQuant")
									&& quotedTerm.getAnnotations()[0].getValue() != null) {
								collectAuxTerm(quotedTerm);
							}
						}
						break;
					}
					*/
					}
					setResult(term);
					return;
				}
			}
			super.convert(term);
		}

		private void collectAuxFromIntern(final AnnotatedTerm annTerm) {
			final Term rewrite = annTerm.getSubterm();
			assert isApplication(SMTLIBConstants.EQUALS, rewrite);
			final Term rhs = ((ApplicationTerm) rewrite).getParameters()[1];
			if (rhs instanceof AnnotatedTerm) {
				collectAuxTerm((AnnotatedTerm) rhs);
			}
		}

		private void collectAuxTerm(final AnnotatedTerm annTerm) {
			final Annotation[] annots = annTerm.getAnnotations();
			if (annots.length == 1) {
				final String annot = annots[0].getKey();
				// Check for Quant AUX literals
				if (annot == ":quotedQuant" && annots[0].getValue() instanceof Term) {
					final Term subterm = annTerm.getSubterm();
					if (isApplication("=", subterm)) {
						final ApplicationTerm auxApp = (ApplicationTerm) subterm;
						if (isApplication("true", auxApp.getParameters()[1])) {
							final Term lhs = auxApp.getParameters()[0];
							if (lhs instanceof ApplicationTerm
									&& ((ApplicationTerm) lhs).getFunction().getName().startsWith("@AUX")) {
								// the definition of the quantAuxLit can be found in the annotation
								validateAuxDef(lhs, (Term) annots[0].getValue());
								return;
							}
						}
					}
					throw new AssertionError("Malformed quantified AUX literal");
				}
			}
		}

		private void collectExistsElim(final AnnotatedTerm annotTerm) {
			final Term[] clause = ((ApplicationTerm) annotTerm.getSubterm()).getParameters();
			final Term[] skolemFuns = (Term[]) annotTerm.getAnnotations()[0].getValue();
			// clause[0]: not (exists ((x...)) F
			// clause[1]: (let ((x skolem...)) F)
			assert clause.length == 2 && isApplication("not", clause[0]);
			final Term existsAtom = ((ApplicationTerm) clause[0]).getParameters()[0];
			final QuantifiedFormula qf = (QuantifiedFormula) existsAtom;
			assert qf.getQuantifier() == QuantifiedFormula.EXISTS;

			final TermVariable[] existentialVars = qf.getVariables();
			assert existentialVars.length == skolemFuns.length;
			final Term[] skolemTerms = mProofRules.getSkolemVars(existentialVars, qf.getSubformula(), false);

			for (int i = 0; i < existentialVars.length; i++) {
				validateSkolemDef(skolemFuns[i], skolemTerms[i]);
			}
		}

		/**
		 * Check that an existentially quantified variable has a unique Skolem function.
		 *
		 * @param skolemApp    the application term {@code (skolem_xyz vars)}. The
		 *                     function symbol should be unique and the parameters
		 *                     should equal the free variables of the existentially
		 *                     quantified formula.
		 * @param var          the variable for which the skolemApp was introduced.
		 * @param quantformula the existentially quantified formula.
		 * @return true iff this usage of skolemApp matches the previous uses (is only
		 *         used for this quantformula with this variable) and that the arguments
		 *         are the free variables of quantformula.
		 */
		private void validateSkolemDef(final Term skolemApp, final Term skolemTerm) {
			final Term previous = mSkolemFunctions.put(skolemApp, new FormulaUnLet().unlet(skolemTerm));
			assert previous == null || previous == skolemTerm;
		}

		/**
		 * Check that an {@literal @}AUX term has the same definition as previously seen.
		 */
		private void validateAuxDef(final Term auxTerm, final Term defTerm) {
			assert auxTerm instanceof ApplicationTerm
					&& ((ApplicationTerm) auxTerm).getFunction().getName().startsWith("@AUX");
			final ApplicationTerm auxApp = (ApplicationTerm) auxTerm;
			final Term[] params = auxApp.getParameters();
			final TermVariable[] vars = new TermVariable[params.length];
			for (int i = 0; i < params.length; i++) {
				if (!(params[i] instanceof TermVariable)) {
					return;
				}
				vars[i] = (TermVariable) params[i];
			}
			final LambdaTerm lambdaTerm = (LambdaTerm) defTerm.getTheory().lambda(vars, defTerm);
			final Term old = mQuantDefinedTerms.put(auxApp.getFunction(), lambdaTerm);
			assert old == null || old == lambdaTerm;
		}

	}

	static Annotation[] ANNOT_QUANT = new Annotation[] { new Annotation(":quotedQuant", null) };
	class RewriteSkolem extends TermTransformer {
		private final HashMap<Term, Term> mSkolems;

		public RewriteSkolem(final HashMap<Term, Term> skolems) {
			mSkolems = skolems;
		}

		@Override
		public void convert(Term term) {
			final Term skolemDef = mSkolems.get(term);
			if (skolemDef != null) {
				term = skolemDef;
			}
			if (term instanceof AnnotatedTerm
					&& ((AnnotatedTerm) term).getAnnotations()[0].getKey().equals(":quotedQuant")
					&& ((AnnotatedTerm) term).getAnnotations()[0].getValue() instanceof Term) {
				term = ((AnnotatedTerm) term).getSubterm();
				term = term.getTheory().annotatedTerm(ANNOT_QUANT, term);
			}
			super.convert(term);
		}
	}
}
