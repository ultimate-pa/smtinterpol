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
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.Map;

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

	private boolean checkProof(final Term proof, final Term[] expectedLits) {
		final MinimalProofChecker checker = new MinimalProofChecker(mSkript, new DefaultLogger());
		final ProofLiteral[] actual = checker.getProvedClause(mAuxDefs, proof);
		final HashSet<ProofLiteral> expectedSet = new HashSet<>();
		for (Term expected : expectedLits) {
			boolean polarity = true;
			while (isApplication(SMTLIBConstants.NOT, expected)) {
				expected = negate(expected);
				polarity = !polarity;
			}
			expectedSet.add(new ProofLiteral(expected, polarity));
		}
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
		final TermVariable[] universalVars = qf.getVariables();
		final Map<TermVariable, Term> sigma = new HashMap<>();
		assert universalVars.length == subst.length;

		for (int i = 0; i < subst.length; i++) {
			if (subst[i] != universalVars[i]) {
				sigma.put(universalVars[i], subst[i]);
			}
		}

		Term proof = mProofRules.forallElim(subst, qf);
		// peculiarity of proof format: remove quotes if subsitution changes something.
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
				Term atom = unquote(quotedAtom);
				Term litProof = mProofRules.delAnnot(quotedAtom);
				if (!isApplication(SMTLIBConstants.EQUALS, atom)) {
					// convert back to (= atom true)
					final Term trueTerm = mSkript.term(SMTLIBConstants.TRUE);
					final Term atomEqTrue = mSkript.term(SMTLIBConstants.EQUALS, atom, trueTerm);
					final Term atomEqAtomEqTrue = mSkript.term(SMTLIBConstants.EQUALS, atom, atomEqTrue);
					litProof = mProofRules.resolutionRule(mSkript.term(SMTLIBConstants.EQUALS, quotedAtom, atom), litProof,
							mProofRules.resolutionRule(atomEqAtomEqTrue,
									proveIff(atomEqAtomEqTrue, mProofRules.iffIntro2(atomEqTrue),
											mProofRules.iffElim1(atomEqTrue)),
									mProofRules.trans(quotedAtom, atom, atomEqTrue)));
					litProof = mProofRules.resolutionRule(trueTerm, mProofRules.trueIntro(), litProof);
					atom = atomEqTrue;
				}
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
		proof = removeNot(proof, rhs, true);
		final Term quotedEq = mSkript.term(SMTLIBConstants.EQUALS, quotedForall, forall);
		proof = mProofRules.resolutionRule(quotedEq, mProofRules.delAnnot(quotedForall),
				mProofRules.resolutionRule(forall, mProofRules.iffElim2(quotedEq), proof));
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
		Term result = unletter.unlet(mSkript.let(universalVars, subst, qf.getSubformula()));
		while (isApplication("not", result)) {
			proof = mProofRules.resolutionRule(result, mProofRules.notIntro(result), proof);
			result = negate(result);
			if (isApplication("not", result)) {
				proof = mProofRules.resolutionRule(result, proof, mProofRules.notElim(result));
				result = negate(result);
			}
		}
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

	private Term convertIte1Helper(final Term iteAtom, final Term iteTrueCase, final boolean polarity) {
		final Term iteTrueCaseEq = iteAtom.getTheory().term("=", iteAtom, iteTrueCase);
		final Term proof = mProofRules.resolutionRule(iteTrueCaseEq, mProofRules.ite1(iteAtom),
				polarity ? mProofRules.iffElim1(iteTrueCaseEq) : mProofRules.iffElim2(iteTrueCaseEq));
		return removeNot(proof, iteTrueCase, !polarity);
	}

	private Term convertIte2Helper(final Term iteAtom, final Term iteFalseCase, final boolean polarity) {
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
			return removeNot(convertIte1Helper(iteAtom, iteParams[1], true), iteParams[0], false);
		case ":ite+2":
			// iteAtom, cond, ~else
			return removeNot(convertIte2Helper(iteAtom, iteParams[2], true), iteParams[0], true);
		case ":ite+red":
			// iteAtom, ~then, ~else
			return mProofRules.resolutionRule(iteParams[0],
					convertIte2Helper(iteAtom, iteParams[2], true), convertIte1Helper(iteAtom, iteParams[1], true));
		case ":ite-1":
			// ~iteAtom, ~cond, then
			return removeNot(convertIte1Helper(iteAtom, iteParams[1], false), iteParams[0], false);
		case ":ite-2":
			// ~iteAtom, cond, else
			return removeNot(convertIte2Helper(iteAtom, iteParams[2], false), iteParams[0], true);
		case ":ite-red": {
			// ~iteAtom, then, else
			return mProofRules.resolutionRule(iteParams[0],
					convertIte2Helper(iteAtom, iteParams[2], false), convertIte1Helper(iteAtom, iteParams[1], false));
		}
		}
		throw new AssertionError();
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
		default: {
			proof = mProofRules.asserted(clause);
			if (isApplication("or", clause)) {
				proof = mProofRules.resolutionRule(clause, proof, mProofRules.orElim(clause));
			}
			for (final Term lit : clauseLits) {
				proof = removeNot(proof, lit, true);
			}
			break;
		}
		}
		assert checkProof(proof, clauseLits);
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
		if (rhs == lhs) {
			return mProofRules.refl(lhs);
		}

		// x can be rewritten to (= x true) or to (not (= x false))
		if (lhs instanceof TermVariable) {
			boolean isNegRewrite = false;
			Term quotedAtom = rhs;
			if (isApplication("not", rhs)) {
				isNegRewrite = true;
				quotedAtom = negate(rhs);
			}
			final Term unquotedAtom = unquote(quotedAtom);
			assert isApplication("=", unquotedAtom);
			final ApplicationTerm rhsApp = (ApplicationTerm) unquotedAtom;
			assert isApplication(isNegRewrite ? "false" : "true", rhsApp.getParameters()[1])
					&& lhs == rhsApp.getParameters()[0];
			final Term rhsLit = isNegRewrite ? theory.term("not", rhsApp) : rhsApp;
			final Term lhsEqRhsLit = theory.term("=", lhs, rhsLit);
			Term proofLhsEqRhsLit;
			Term proofUnquote = mProofRules.resolutionRule(theory.term("=", quotedAtom, unquotedAtom),
					mProofRules.delAnnot(quotedAtom), mProofRules.symm(unquotedAtom, quotedAtom));
			if (isNegRewrite) {
				final Term falseTerm = rhsApp.getParameters()[1];
				proofLhsEqRhsLit = proveIff(lhsEqRhsLit,
						mProofRules.resolutionRule(rhsApp, mProofRules.notIntro(rhsLit), mProofRules.iffElim2(rhsApp)),
						mProofRules.resolutionRule(rhsApp, mProofRules.iffIntro1(rhsApp), mProofRules.notElim(rhsLit)));
				proofLhsEqRhsLit = mProofRules.resolutionRule(falseTerm, proofLhsEqRhsLit, mProofRules.falseElim());
				proofUnquote = mProofRules.resolutionRule(theory.term("=", unquotedAtom, quotedAtom), proofUnquote,
						mProofRules.cong(rhsLit, rhs));
			} else {
				final Term trueTerm = rhsApp.getParameters()[1];
				proofLhsEqRhsLit = proveIff(lhsEqRhsLit, mProofRules.iffIntro2(rhsApp), mProofRules.iffElim1(rhsApp));
				proofLhsEqRhsLit = mProofRules.resolutionRule(trueTerm, mProofRules.trueIntro(), proofLhsEqRhsLit);
			}
			return mProofRules.resolutionRule(theory.term("=", lhs, rhsLit), proofLhsEqRhsLit,
					mProofRules.resolutionRule(theory.term("=", rhsLit, rhs), proofUnquote,
							mProofRules.trans(lhs, rhsLit, rhs)));
		}

		if (rhs instanceof AnnotatedTerm) {
			/* second case: boolean functions are created as equalities */
			final Term unquoteRhs = unquote(rhs);

			/* Check for auxiliary literals */
			if (lhs == unquoteRhs) {
				return mProofRules.resolutionRule(theory.term("=", rhs, lhs), mProofRules.delAnnot(rhs),
						mProofRules.symm(lhs, rhs));
			}

			if (isApplication("=", unquoteRhs)) {
				final Term[] rhsArgs = ((ApplicationTerm) unquoteRhs).getParameters();
				if (rhsArgs.length == 2 && isApplication("true", rhsArgs[1])) {
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

		if (isApplication("=", lhs)) {
			/* compute affine term for lhs */
			final Term[] lhsParams = ((ApplicationTerm) lhs).getParameters();
			assert lhsParams.length == 2;
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

			/* first check if rhs and lhs are the same or only swapped parameters */
			if (lhs == unquoteRhs) {
				return proof2;
			} else if (lhsParams[1] == rhsParams[0] && lhsParams[0] == rhsParams[1]) {
				final Term equality1 = theory.term("=", lhs, unquoteRhs);
				final Term proof1 =
						mProofRules.resolutionRule(lhs,
								mProofRules.resolutionRule(unquoteRhs, mProofRules.iffIntro1(equality1),
										mProofRules.symm(lhsParams[0], lhsParams[1])),
								mProofRules.resolutionRule(unquoteRhs, mProofRules.symm(rhsParams[0], rhsParams[1]),
										mProofRules.iffIntro2(equality1)));
				return mProofRules.resolutionRule(equality1, proof1,
						mProofRules.resolutionRule(equality2, proof2, mProofRules.trans(lhs, unquoteRhs, rhs)));
			}

			// Now it must be an LA equality that got normalized in a different way.
			assert lhsParams[0].getSort().isNumericSort();

			/* check that they represent the same equality */
			// Note that an LA equality can sometimes be rewritten to an already existing CC
			// equality, so
			// we cannot assume the rhs is normalized

			final SMTAffineTerm lhsAffine = new SMTAffineTerm(lhsParams[0]);
			lhsAffine.add(Rational.MONE, lhsParams[1]);
			final SMTAffineTerm rhsAffine = new SMTAffineTerm(rhsParams[0]);
			rhsAffine.add(Rational.MONE, rhsParams[1]);
			// we cannot compute gcd on constants so check for this and bail out
			assert !lhsAffine.isConstant() && !rhsAffine.isConstant() : "A trivial equality was created";
			lhsAffine.div(lhsAffine.getGcd());
			rhsAffine.div(rhsAffine.getGcd());
			if (lhsAffine.equals(rhsAffine)) {
				// TODO
				return mProofRules.asserted(theory.term("=", lhs, rhs));
			} else {
				rhsAffine.negate();
				assert lhsAffine.equals(rhsAffine);
				// TODO
				return mProofRules.asserted(theory.term("=", lhs, rhs));
			}
		}
		throw new AssertionError();
	}

	private Term convertRewriteNot(final Term rewrite, final Term lhs, final Term rhs) {
		// lhs: (not lhsAtom)
		assert isApplication("not", lhs);
		final Theory t = rewrite.getTheory();
		final Term lhsAtom = ((ApplicationTerm) lhs).getParameters()[0];
		if (isApplication("false", lhsAtom)) {
			assert isApplication("true", rhs);
			return mProofRules.resolutionRule(rhs, mProofRules.trueIntro(), mProofRules.resolutionRule(lhsAtom,
					mProofRules.resolutionRule(lhs, mProofRules.notIntro(lhs), mProofRules.iffIntro2(rewrite)),
					mProofRules.falseElim()));
		}
		if (isApplication("true", lhsAtom)) {
			assert isApplication("false", rhs);
			return mProofRules.resolutionRule(lhsAtom, mProofRules.trueIntro(), mProofRules.resolutionRule(rhs,
					mProofRules.resolutionRule(lhs, mProofRules.iffIntro1(rewrite), mProofRules.notElim(lhs)),
					mProofRules.falseElim()));
		}
		if (isApplication("not", lhsAtom)) {
			assert rhs == ((ApplicationTerm) lhsAtom).getParameters()[0];
			return mProofRules.resolutionRule(rhs,
					mProofRules.resolutionRule(lhsAtom, mProofRules.notIntro(lhsAtom),
							mProofRules.resolutionRule(lhs, mProofRules.iffIntro1(rewrite),
									mProofRules.notElim(lhs))),
					mProofRules.resolutionRule(lhsAtom, mProofRules.resolutionRule(lhs, mProofRules.notIntro(lhs),
							mProofRules.iffIntro2(rewrite)), mProofRules.notElim(lhsAtom)));
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


		final Term goal = theo.term(SMTLIBConstants.EQUALS, lhs, rhs);
		Term clause = mProofRules.iffIntro2(goal);
		// clause: (= lhs rhs), ~lhs, ~rhs
		Term auxClause = mProofRules.iffIntro1(goal);
		// auxClause: (= lhs rhs), lhs, rhs

		if (args.size() > 1 || !trueCase) {
			assert isApplication(SMTLIBConstants.NOT, rhs);
			clause = mProofRules.resolutionRule(rhs, mProofRules.notIntro(rhs), clause);
			auxClause = mProofRules.resolutionRule(rhs, auxClause, mProofRules.notElim(rhs));
		}
		if (args.size() > 1) {
			final Term orTerm = ((ApplicationTerm) rhs).getParameters()[0];
			assert isApplication(SMTLIBConstants.OR, orTerm);
			clause = mProofRules.resolutionRule(orTerm, clause, mProofRules.orElim(orTerm));
		}
		// clause: (= lhs rhs), ~lhs, (not? l1), ..., (not? ln)
		clause = mProofRules.resolutionRule(lhs, mProofRules.equalsIntro(lhs), clause);
		for (int i = 0; i < params.length - 1; i++) {
			final Term equality = theo.term(SMTLIBConstants.EQUALS, params[i], params[i+1]);
			final Term iffIntro = trueCase ? mProofRules.iffIntro2(equality) : mProofRules.iffIntro1(equality);
			clause = mProofRules.resolutionRule(equality, iffIntro, clause);
		}
		// clause: (= lhs rhs), ~? l1,... ~?ln, (not? l1), ... (not? ln), ~true/false

		// introduce all distinct arguments
		int orPos = 0;
		for (final int pos : args) {
			final Term arg = params[pos];
			final Term argTrueFalse = theo.term(SMTLIBConstants.EQUALS, arg, params[trueFalseIdx]);
			final Term notArg = theo.term(SMTLIBConstants.NOT, arg);

			// replace (not li) by ~li, if trueCase and args.size() > 1
			if (args.size() > 1 && trueCase) {
				clause = mProofRules.resolutionRule(notArg, clause, mProofRules.notElim(notArg));
			}

			Term subclause = mProofRules.resolutionRule(lhs, auxClause,
					mProofRules.equalsElim(pos, trueFalseIdx, lhs));
			if (args.size() > 1) {
				final Term orTerm = ((ApplicationTerm) rhs).getParameters()[0];
				subclause = mProofRules.resolutionRule(orTerm, mProofRules.orIntro(orPos++, orTerm), subclause);
			}
			// subclause: (= lhs rhs), (= p1 true/false), ~(not? p1)
			subclause = mProofRules.resolutionRule(argTrueFalse, subclause,
					trueCase ? mProofRules.iffElim1(argTrueFalse) : mProofRules.iffElim2(argTrueFalse));
			// subclause: (= lhs rhs), ~? p1, ~(not? p1)
			if (trueCase) {
				subclause = mProofRules.resolutionRule(notArg, mProofRules.notIntro(notArg), subclause);
			}
			// subclause: (= lhs rhs), ~? p1
			clause = mProofRules.resolutionRule(arg, trueCase ? subclause : clause, trueCase ? clause : subclause);
		}
		clause = mProofRules.resolutionRule(params[trueFalseIdx], trueCase ? mProofRules.trueIntro() : clause,
				trueCase ? clause : mProofRules.falseElim());
		return clause;
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

	private Term convertRewriteOrTaut(final Term rewrite, final Term lhs, final Term rhs) {
		assert isApplication("or", lhs) && isApplication("true", rhs);
		final Theory theory = rewrite.getTheory();
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
			}
			seen.put(lhsParams[i], i);
		}
		return mProofRules.resolutionRule(rhs, mProofRules.trueIntro(), proof);
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
		case ":xorNot":
			subProof = convertRewriteXorNot(rewriteStmt, stmtParams[0], stmtParams[1]);
			break;
		case ":orTaut":
			subProof = convertRewriteOrTaut(rewriteStmt, stmtParams[0], stmtParams[1]);
			break;
		case ":distinctBool":
		case ":distinctSame":
		case ":distinctBinary":
			subProof = convertRewriteDistinct(rewriteRule, rewriteStmt, stmtParams[0], stmtParams[1]);
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
		case ":constDiff":
		case ":xorTrue":
		case ":xorFalse":
		case ":xorSame":
		case ":orSimp":
		case ":iteTrue":
		case ":iteFalse":
		case ":iteSame":
		case ":iteBool1":
		case ":iteBool2":
		case ":iteBool3":
		case ":iteBool4":
		case ":iteBool5":
		case ":iteBool6":
		case ":andToOr":
		case ":impToOr":
		case ":strip":
		case ":canonicalSum":
		case ":leqTrue":
		case ":leqFalse":
		case ":divisible":
		case ":div1":
		case ":div-1":
		case ":divConst":
		case ":modulo1":
		case ":modulo-1":
		case ":moduloConst":
		case ":modulo":
		case ":toInt":
		case ":storeOverStore":
		case ":selectOverStore":
		case ":flatten":
		case ":storeRewrite":
		case ":skolem":
		case ":removeForall":
		default:
			// throw new AssertionError("Unknown Rewrite Rule: " + annotTerm);
			subProof = mProofRules.asserted(rewriteStmt);
		}
		assert checkProof(subProof, new Term[] { rewriteStmt });
		return annotateProved(rewriteStmt, subProof);
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
		Term disEq = null;
		for (final Term literal : clause) {
			if (isApplication("not", literal)) {
				final Term quotedAtom = ((ApplicationTerm) literal).getParameters()[0];
				final Term atom = unquote(quotedAtom);
				assert isApplication("=", atom);
				final Term[] sides = ((ApplicationTerm) atom).getParameters();
				assert sides.length == 2;
				allEqualities.put(new SymmetricPair<>(sides[0], sides[1]), quotedAtom);
			} else {
				assert unquote(literal) == goalEquality && disEq == null;
				disEq = literal;
			}
		}

		final Term[] mainPath = (Term[]) ccAnnotation[startSubpathAnnot + 1];
		assert mainPath.length >= 2 : "Main path too short in CC lemma";
		assert isApplication("=", goalEquality) : "Goal equality is not an equality in CC lemma";
		final Term[] sides = ((ApplicationTerm) goalEquality).getParameters();
		assert sides.length == 2 : "Expected binary equality in CC lemma";
		assert new SymmetricPair<>(mainPath[0], mainPath[mainPath.length - 1])
				.equals(new SymmetricPair<>(sides[0], sides[1])) : "Did not explain main equality " + goalEquality;

		Term proof;
		Term[] expectedLhs;
		Term[] expectedRhs;
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
			expectedLhs = lhs.getParameters();
			expectedRhs = rhs.getParameters();
		} else {
			// This is a transitivity lemma
			proof = mProofRules.trans(mainPath);
			expectedLhs = new Term[mainPath.length - 1];
			expectedRhs = new Term[mainPath.length - 1];
			System.arraycopy(mainPath, 0, expectedLhs, 0, expectedLhs.length);
			System.arraycopy(mainPath, 1, expectedRhs, 0, expectedRhs.length);
		}

		final LinkedHashMap<Term, Term> subProofs = new LinkedHashMap<>();
		for (int i = 0; i < expectedLhs.length; i++) {
			final Term eq = theory.term("=", expectedLhs[i], expectedRhs[i]);
			if (subProofs.containsKey(eq)) {
				/* equality was already proved */
				continue;
			}
			final Term literal = allEqualities.get(new SymmetricPair<>(expectedLhs[i], expectedRhs[i]));
			if (literal == null) {
				assert expectedLhs[i] == expectedRhs[i];
				subProofs.put(eq, mProofRules.refl(expectedLhs[i]));
			} else {
				final Term unquoteLiteral = unquote(literal);
				if (unquoteLiteral != eq) {
					// symmetric case
					subProofs.put(eq, mProofRules.symm(expectedLhs[i], expectedRhs[i]));
				}
				if (subProofs.containsKey(unquoteLiteral)) {
					// move proof to the end
					subProofs.put(unquoteLiteral, subProofs.remove(unquoteLiteral));
				} else {
					final Term unquotingEq = theory.term("=", literal, unquoteLiteral);
					subProofs.put(unquoteLiteral, mProofRules.resolutionRule(unquotingEq,
							mProofRules.delAnnot(literal), mProofRules.iffElim2(unquotingEq)));
				}
			}
		}
		for (final Map.Entry<Term, Term> subproof : subProofs.entrySet()) {
			proof = mProofRules.resolutionRule(subproof.getKey(), subproof.getValue(), proof);
		}
		if (disEq == null) {
			proof = mProofRules.resolutionRule(mainPathEquality, proof,
					proveTrivialDisequality(mainPath[0], mainPath[mainPath.length - 1]));
		} else {
			final Term unquoteLiteral = unquote(disEq);
			if (unquoteLiteral != mainPathEquality) {
				// symmetric case
				proof = mProofRules.resolutionRule(mainPathEquality, proof,
						mProofRules.symm(mainPath[mainPath.length - 1], mainPath[0]));
			}
			final Term unquotingEq = theory.term("=", disEq, unquoteLiteral);
			proof = mProofRules.resolutionRule(unquoteLiteral, proof, mProofRules.resolutionRule(unquotingEq,
					mProofRules.delAnnot(disEq), mProofRules.iffElim1(unquotingEq)));
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

		switch (lemmaType) {
		case ":CC":
			return convertCCLemma(clause, (Object[]) lemmaAnnotation);
		default: {
			Term subProof = mProofRules.asserted(lemma);
			if (clause.length > 1) {
				subProof = mProofRules.resolutionRule(lemma, subProof, mProofRules.orElim(lemma));
			}
			for (final Term lit : clause) {
				subProof = removeNot(subProof, lit, true);
			}
			return subProof;
		}
		}
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
			setResult(term);
			return;
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
	 * Proof that the disequality between two terms is trivial. There are two cases,
	 * (1) the difference between the terms is constant and nonzero, e.g.
	 * {@code (= x (+ x 1))}, or (2) the difference contains only integer variables
	 * and the constant divided by the gcd of the factors is non-integral, e.g.,
	 * {@code (= (+ x (* 2 y)) (+ x (* 2 z) 1))}.
	 *
	 * @param first  the left-hand side of the equality
	 * @param second the right-hand side of the equality
	 * @return true if the equality is trivially not satisfied.
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
			} else {
				assert diff.getConstant().signum() < 0;
				final Term leqLhs = theory.term(SMTLIBConstants.LEQ, second, first);
				final Term eqSwapped = theory.term(SMTLIBConstants.EQUALS, second, first);
				return mProofRules.resolutionRule(eqSwapped, mProofRules.symm(second, first),
						mProofRules.resolutionRule(leqLhs, mProofRules.eqLeq(second, first),
								mProofRules.farkas(new Term[] { leqLhs }, new BigInteger[] { BigInteger.ONE })));
			}
		} else {
			final Rational gcd = diff.getGcd();
			diff.div(gcd);
			final Rational bound = diff.getConstant().negate();
			assert diff.isAllIntSummands() && !bound.isIntegral();
			final Sort intSort = theory.getSort(SMTLIBConstants.INT);
			diff.add(bound);
			final Term intVar = diff.toTerm(intSort);
			final Term floorBound = bound.floor().toTerm(intSort);
			final Term ceilBound = bound.ceil().toTerm(intSort);
			assert ceilBound != floorBound;
			// show (ceil(bound) <= intVar) || (intVar <= floor(bound)
			final Term geqCeil = theory.term(SMTLIBConstants.LEQ, ceilBound, intVar);
			final Term leqFloor = theory.term(SMTLIBConstants.LEQ, intVar, floorBound);
			final Term proofIntCase = mProofRules.resolutionRule(theory.term(SMTLIBConstants.LT, intVar, ceilBound),
					mProofRules.totality(ceilBound, intVar), mProofRules.ltInt(intVar, ceilBound));
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

	private Term proveIff(final Term equality, final Term proofLeftToRight, final Term proofRightToLeft) {
		final Term[] sides = ((ApplicationTerm) equality).getParameters();
		assert sides.length == 2;
		return mProofRules.resolutionRule(sides[1],
				mProofRules.resolutionRule(sides[0], mProofRules.iffIntro1(equality), proofLeftToRight),
				mProofRules.resolutionRule(sides[0], proofRightToLeft, mProofRules.iffIntro2(equality)));
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
		Term one;
		if (needsIntReasoning) {
			assert isZero(lhsParam[1]) && isZero(rhsAtomParam[1]);
			assert !isStrictLhs && !isStrictRhsAtom;
			one = Rational.ONE.toTerm(lhsParam[1].getSort());

			negRhsAtom = theory.term("<=", one, rhsAtomParam[0]);
			rhsTotality = mProofRules.totality(one, rhsAtomParam[0]);
		} else {
			one = null;
			negRhsAtom = theory.term(isStrictRhsAtom ? "<=" : "<", rhsAtomParam[1], rhsAtomParam[0]);
			rhsTotality = mProofRules.totality(rhsAtomParam[isStrictRhsAtom ? 1 : 0],
					rhsAtomParam[isStrictRhsAtom ? 0 : 1]);
		}
		Term proofToRhsAtom = mProofRules.farkas(new Term[] { rhsIsNegated ? negLhs : posLhs, negRhsAtom },
				new BigInteger[] { gcd.denominator(), gcd.numerator() } );
		proofToRhsAtom = mProofRules.resolutionRule(negRhsAtom, rhsTotality, proofToRhsAtom);
		Term proofFromRhsAtom = mProofRules.farkas(new Term[] { rhsIsNegated ? posLhs : negLhs, rhsAtom },
				new BigInteger[] { gcd.denominator(), gcd.numerator() } );
		if (needsIntReasoning) {
			proofToRhsAtom = mProofRules.resolutionRule(
					theory.term("<", rhsAtomParam[0], one), proofToRhsAtom,
					mProofRules.ltInt(rhsAtomParam[0], one));
		}
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
				mProofRules.totality(lhsParam[isStrictLhs ? 1 : 0], lhsParam[isStrictLhs ? 0 : 1]), proofRhsToLhs);
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
