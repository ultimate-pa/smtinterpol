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

import java.util.ArrayList;
import java.util.HashSet;
import java.util.LinkedHashSet;

import de.uni_freiburg.informatik.ultimate.logic.AnnotatedTerm;
import de.uni_freiburg.informatik.ultimate.logic.Annotation;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.ConstantTerm;
import de.uni_freiburg.informatik.ultimate.logic.FunctionSymbol;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.SMTLIBConstants;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermTransformer;
import de.uni_freiburg.informatik.ultimate.logic.Theory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.LogProxy;
import de.uni_freiburg.informatik.ultimate.smtinterpol.convert.SMTAffineTerm;

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
	 * The logger where errors are reported.
	 */
	LogProxy mLogger;

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

		setupSimpleRules();
	}

	private void setupSimpleRules() {
		ProofRules.setupTheory(mSkript.getTheory());
	}

	private Term annotateProved(final Term provedTerm, final Term proof) {
		return proof.getTheory().annotatedTerm(new Annotation[] { new Annotation(ANNOT_PROVED, provedTerm) }, proof);
	}

	private Term provedTerm(final AnnotatedTerm annotatedTerm) {
		assert annotatedTerm.getAnnotations()[0].getKey() == ANNOT_PROVED;
		return (Term) annotatedTerm.getAnnotations()[0].getValue();
	}

	private Term subproof(final AnnotatedTerm annotatedTerm) {
		assert annotatedTerm.getAnnotations()[0].getKey() == ANNOT_PROVED;
		return annotatedTerm.getSubterm();
	}

	private Term convertResolution(final Term[] newParams) {
		Term accum = newParams[0];
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
			final Term subproof = pivotPlusProof.getSubterm();

			if (negated) {
				// term occurs negated in subproof, positive in accum
				accum = ProofRules.resolutionRule(pivot, accum, subproof);
			} else {
				accum = ProofRules.resolutionRule(pivot, subproof, accum);
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
			proof = ProofRules.resolutionRule(candidateTerm, positive ? proof : ProofRules.notIntro(candidateTerm),
					positive ? ProofRules.notElim(candidateTerm) : proof);
			candidateTerm = ((ApplicationTerm) candidateTerm).getParameters()[0];
			positive = !positive;
		}
		return proof;
	}

	private Term convertAsserted(final Term assertedProof) {
		assert ProofRules.isProofRule(ProofRules.ASSUME, assertedProof);
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
				proofs.add(removeNot(ProofRules.ite2(iteTerm), iteParams[0], true));
				iteTerm = iteParams[2];
			} else {
				assert isApplication("not", clause[i]);
				assert ((ApplicationTerm) clause[i]).getParameters()[0] == iteParams[0];
				proofs.add(removeNot(ProofRules.ite1(iteTerm), iteParams[0], false));
				iteTerm = iteParams[1];
			}
		}
		assert iteTerm == goal;
		if (proofs.size() > 1) {
			final Theory t = goal.getTheory();
			// build transitivity proof
			intermediates.add(goal);
			Term proof = ProofRules.trans(intermediates.toArray(new Term[intermediates.size()]));
			for (int i = 0; i < proofs.size(); i++) {
				final Term eqTerm = t.term("=", intermediates.get(i), intermediates.get(i + 1));
				proof = ProofRules.resolutionRule(eqTerm, proofs.get(i), proof);
			}
			return proof;
		} else {
			assert proofs.size() == 1;
			return proofs.get(0);
		}
	}

	private Term convertTautology(final Term taut) {
		final AnnotatedTerm annotTerm = (AnnotatedTerm) taut;
		final Term clause = annotTerm.getSubterm();
		assert annotTerm.getAnnotations().length == 1;
		final Annotation annot = annotTerm.getAnnotations()[0];
		switch (annot.getKey()) {
		case ":true+":
			assert isApplication("true", clause);
			return ProofRules.trueIntro(taut.getTheory());
		case ":false-":
			assert isApplication("not", clause)
					&& isApplication("false", ((ApplicationTerm) clause).getParameters()[0]);
			return ProofRules.falseElim(taut.getTheory());
		case ":or+": {
			assert isApplication("or", clause);
			final Term[] clauseLits = ((ApplicationTerm) clause).getParameters();
			assert clauseLits.length == 2;
			final Term orTerm = clauseLits[0];
			assert isApplication("or", orTerm);
			assert isApplication("not", clauseLits[1]);
			final Term subArg = ((ApplicationTerm) clauseLits[1]).getParameters()[0];
			final Term[] orParams = ((ApplicationTerm) orTerm).getParameters();
			for (int i = 0; i < orParams.length; i++) {
				if (orParams[i] == subArg) {
					return removeNot(ProofRules.orIntro(i, orTerm), subArg, false);
				}
			}
			throw new AssertionError("Malformed tautology: " + taut);
		}
		case ":or-": {
			assert isApplication("or", clause);
			final Term[] clauseLits = ((ApplicationTerm) clause).getParameters();
			assert isApplication("not", clauseLits[0]);
			final Term orTerm = ((ApplicationTerm) clauseLits[0]).getParameters()[0];
			assert isApplication("or", orTerm);
			final Term[] orParams = ((ApplicationTerm) orTerm).getParameters();
			assert clauseLits.length == orParams.length + 1;
			Term proof = ProofRules.orElim(orTerm);
			for (int i = 0; i < orParams.length; i++) {
				assert orParams[i] == clauseLits[i + 1];
				proof = removeNot(proof, orParams[i], true);
			}
			return proof;
		}
		case ":and+": {
			assert isApplication("or", clause);
			final Term[] clauseLits = ((ApplicationTerm) clause).getParameters();
			final Term andTerm = clauseLits[0];
			assert isApplication("and", andTerm);
			final Term[] andParams = ((ApplicationTerm) andTerm).getParameters();
			assert clauseLits.length == andParams.length + 1;
			Term proof = ProofRules.andIntro(andTerm);
			for (int i = 0; i < andParams.length; i++) {
				assert isApplication("not", clauseLits[i + 1]);
				assert andParams[i] == ((ApplicationTerm) clauseLits[i + 1]).getParameters()[0];
				proof = removeNot(proof, andParams[i], false);
			}
			return proof;
		}
		case ":and-": {
			assert isApplication("or", clause);
			final Term[] clauseLits = ((ApplicationTerm) clause).getParameters();
			assert clauseLits.length == 2;
			assert isApplication("not", clauseLits[0]);
			final Term andTerm = ((ApplicationTerm) clauseLits[0]).getParameters()[0];
			assert isApplication("and", andTerm);
			final Term subArg = clauseLits[1];
			final Term[] andParams = ((ApplicationTerm) andTerm).getParameters();
			for (int i = 0; i < andParams.length; i++) {
				if (andParams[i] == subArg) {
					return removeNot(ProofRules.andElim(i, andTerm), subArg, true);
				}
			}
			throw new AssertionError("Malformed tautology: " + taut);
		}
		case ":=>+": {
			assert isApplication("or", clause);
			final Term[] clauseLits = ((ApplicationTerm) clause).getParameters();
			assert clauseLits.length == 2;
			final Term impTerm = clauseLits[0];
			assert isApplication("=>", impTerm);
			final Term[] impParams = ((ApplicationTerm) impTerm).getParameters();
			Term subArg = clauseLits[1];
			for (int i = 0; i < impParams.length - 1; i++) {
				if (impParams[i] == subArg) {
					return removeNot(ProofRules.impIntro(i, impTerm), subArg, true);
				}
			}
			assert isApplication("not", subArg);
			subArg = ((ApplicationTerm) subArg).getParameters()[0];
			if (impParams[impParams.length - 1] == subArg) {
				return removeNot(ProofRules.impIntro(impParams.length - 1, impTerm), subArg, false);
			}
			throw new AssertionError("Malformed tautology: " + taut);
		}
		case ":=>-": {
			assert isApplication("or", clause);
			final Term[] clauseLits = ((ApplicationTerm) clause).getParameters();
			assert isApplication("not", clauseLits[0]);
			final Term impTerm = ((ApplicationTerm) clauseLits[0]).getParameters()[0];
			assert isApplication("=>", impTerm);
			final Term[] impParams = ((ApplicationTerm) impTerm).getParameters();
			assert clauseLits.length == impParams.length + 1;
			Term proof = ProofRules.impElim(impTerm);
			for (int i = 0; i < impParams.length; i++) {
				if (i < impParams.length - 1) {
					assert isApplication("not", clauseLits[i + 1]);
					assert impParams[i] == ((ApplicationTerm) clauseLits[i + 1]).getParameters()[0];
					proof = removeNot(proof, impParams[i], false);
				} else {
					assert impParams[i] == clauseLits[i + 1];
					proof = removeNot(proof, impParams[i], true);
				}
			}
			return proof;
		}
		case ":=+1": {
			assert isApplication("or", clause);
			final Term[] clauseLits = ((ApplicationTerm) clause).getParameters();
			assert clauseLits.length == 3;
			final Term eqTerm = clauseLits[0];
			assert isApplication("=", eqTerm);
			final Term[] eqParams = ((ApplicationTerm) eqTerm).getParameters();
			assert eqParams.length == 2;
			Term proof = ProofRules.iffIntro1(eqTerm);
			assert eqParams[0] == clauseLits[1];
			proof = removeNot(proof, eqParams[0], true);
			assert eqParams[1] == clauseLits[2];
			proof = removeNot(proof, eqParams[1], true);
			return proof;
		}
		case ":=+2": {
			assert isApplication("or", clause);
			final Term[] clauseLits = ((ApplicationTerm) clause).getParameters();
			assert clauseLits.length == 3;
			final Term eqTerm = clauseLits[0];
			assert isApplication("=", eqTerm);
			final Term[] eqParams = ((ApplicationTerm) eqTerm).getParameters();
			assert eqParams.length == 2;
			Term proof = ProofRules.iffIntro2(eqTerm);
			assert isApplication("not", clauseLits[1]);
			assert eqParams[0] == ((ApplicationTerm) clauseLits[1]).getParameters()[0];
			proof = removeNot(proof, eqParams[0], false);
			assert isApplication("not", clauseLits[2]);
			assert eqParams[1] == ((ApplicationTerm) clauseLits[2]).getParameters()[0];
			proof = removeNot(proof, eqParams[0], false);
			return proof;
		}
		case ":=-1": {
			assert isApplication("or", clause);
			final Term[] clauseLits = ((ApplicationTerm) clause).getParameters();
			assert clauseLits.length == 3;
			assert isApplication("not", clauseLits[0]);
			final Term eqTerm = ((ApplicationTerm) clauseLits[0]).getParameters()[0];
			assert isApplication("=", eqTerm);
			final Term[] eqParams = ((ApplicationTerm) eqTerm).getParameters();
			assert eqParams.length == 2;
			Term proof = ProofRules.iffElim2(eqTerm);
			assert eqParams[0] == clauseLits[1];
			proof = removeNot(proof, eqParams[0], true);
			assert isApplication("not", clauseLits[2]);
			assert eqParams[1] == ((ApplicationTerm) clauseLits[2]).getParameters()[0];
			proof = removeNot(proof, eqParams[1], false);
			return proof;
		}
		case ":=-2": {
			assert isApplication("or", clause);
			final Term[] clauseLits = ((ApplicationTerm) clause).getParameters();
			assert clauseLits.length == 3;
			assert isApplication("not", clauseLits[0]);
			final Term eqTerm = ((ApplicationTerm) clauseLits[0]).getParameters()[0];
			assert isApplication("=", eqTerm);
			final Term[] eqParams = ((ApplicationTerm) eqTerm).getParameters();
			assert eqParams.length == 2;
			Term proof = ProofRules.iffElim2(eqTerm);
			assert isApplication("not", clauseLits[1]);
			assert eqParams[0] == ((ApplicationTerm) clauseLits[1]).getParameters()[0];
			proof = removeNot(proof, eqParams[0], false);
			assert eqParams[1] == clauseLits[2];
			proof = removeNot(proof, eqParams[1], true);
			return proof;
		}
		case ":termITE": {
			assert isApplication("or", clause);
			final Term[] clauseLits = ((ApplicationTerm) clause).getParameters();
			return convertTermITE(clauseLits);
		}
		default:
			throw new AssertionError("Unknown tautology: " + taut);
		}
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
		final Term lhsTerm = ((ApplicationTerm) implicationTerm).getParameters()[0];

		final Term impElim = isEquality ? ProofRules.iffElim2(implicationTerm) : ProofRules.impElim(implicationTerm);
		final Term impClause = ProofRules.resolutionRule(implicationTerm, annotImp.getSubterm(), impElim);
		return ProofRules.resolutionRule(lhsTerm, newParams[0], impClause);
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
		Term clause = ProofRules.trans(intermediateTerms);
		for (int i = 0; i < newParams.length; i++) {
			final ApplicationTerm provedEq = (ApplicationTerm) provedTerm((AnnotatedTerm) newParams[i]);
			final Term subproof = subproof((AnnotatedTerm) newParams[i]);
			clause = ProofRules.resolutionRule(provedEq, subproof, clause);
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
			newLitProof[i] = ProofRules.refl(oldFuncParams[i]);
		}
		assert pos == newParams.length;

		final Term newFunc = t.term(oldFunc.getFunction(), newFuncParams);
		final Term congEquality = t.term(SMTLIBConstants.EQUALS, oldFunc, newFunc);
		Term proof = ProofRules.cong(oldFunc, newFunc);
		final HashSet<Term> eliminated = new HashSet<>();
		for (int i = 0; i < newFuncParams.length; i++) {
			if (!eliminated.contains(newLit[i])) {
				proof = ProofRules.resolutionRule(newLit[i], newLitProof[i], proof);
				eliminated.add(newLit[i]);
			}
		}
		// build transitivity with left equality, unless it is a reflexivity
		if (leftEquality.getParameters()[0] != leftEquality.getParameters()[1]) {
			Term transProof = ProofRules.trans(leftEquality.getParameters()[0], oldFunc, newFunc);
			transProof = ProofRules.resolutionRule(leftEquality, subproof((AnnotatedTerm) newParams[0]), transProof);
			proof = ProofRules.resolutionRule(congEquality, transProof, proof);
		}
		return annotateProved(t.term(SMTLIBConstants.EQUALS, leftEquality.getParameters()[0], newFunc), proof);
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
		clause = ProofRules.resolutionRule(trueEqFalse, ProofRules.equalsElim(trueIdx, falseIdx, lhs),
				ProofRules.iffElim2(trueEqFalse));
		clause = ProofRules.resolutionRule(lhs, ProofRules.iffIntro1(t.term(SMTLIBConstants.EQUALS, lhs, rhs)), clause);
		clause = ProofRules.resolutionRule(lhsParams[falseIdx],
				ProofRules.resolutionRule(lhsParams[trueIdx], ProofRules.trueIntro(t), clause),
				ProofRules.falseElim(t));
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
		Term clause = ProofRules.iffIntro2(goal);
		// clause: (= lhs rhs), ~lhs, ~rhs
		Term auxClause = ProofRules.iffIntro1(goal);
		// auxClause: (= lhs rhs), lhs, rhs

		if (args.size() > 1 || !trueCase) {
			assert isApplication(SMTLIBConstants.NOT, rhs);
			clause = ProofRules.resolutionRule(rhs, ProofRules.notIntro(rhs), clause);
			auxClause = ProofRules.resolutionRule(rhs, clause, ProofRules.notElim(rhs));
		}
		if (args.size() > 1) {
			final Term orTerm = ((ApplicationTerm) rhs).getParameters()[0];
			assert isApplication(SMTLIBConstants.OR, orTerm);
			clause = ProofRules.resolutionRule(orTerm, clause, ProofRules.orElim(orTerm));
		}
		// clause: (= lhs rhs), ~lhs, (not? l1), ..., (not? ln)
		clause = ProofRules.resolutionRule(lhs, ProofRules.equalsIntro(lhs), clause);
		for (int i = 0; i < params.length - 1; i++) {
			final Term equality = theo.term(SMTLIBConstants.EQUALS, params[i], params[i+1]);
			final Term iffIntro = trueCase ? ProofRules.iffIntro2(equality) : ProofRules.iffIntro1(equality);
			clause = ProofRules.resolutionRule(equality, iffIntro, clause);
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
				clause = ProofRules.resolutionRule(notArg, clause, ProofRules.notElim(notArg));
			}

			Term subclause = ProofRules.resolutionRule(lhs, auxClause, ProofRules.equalsElim(pos, trueFalseIdx, lhs));
			if (args.size() > 1) {
				final Term orTerm = ((ApplicationTerm) rhs).getParameters()[0];
				subclause = ProofRules.resolutionRule(orTerm, ProofRules.orIntro(orPos++, orTerm), subclause);
			}
			// subclause: (= lhs rhs), (= p1 true/false), ~(not? p1)
			subclause = ProofRules.resolutionRule(argTrueFalse, subclause,
					trueCase ? ProofRules.iffElim1(argTrueFalse) : ProofRules.iffElim2(argTrueFalse));
			// subclause: (= lhs rhs), ~? p1, ~(not? p1)
			if (trueCase) {
				subclause = ProofRules.resolutionRule(notArg, ProofRules.notIntro(notArg), subclause);
			}
			// subclause: (= lhs rhs), ~? p1
			clause = ProofRules.resolutionRule(arg, trueCase ? subclause : clause, trueCase ? clause : subclause);
		}
		return clause;
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
			subProof = ProofRules.expand(stmtParams[0]);
			break;
		case ":trueNotFalse":
			subProof = convertRewriteTrueNotFalse(stmtParams[0], stmtParams[1]);
			break;
		case ":eqTrue":
		case ":eqFalse":
			subProof = convertRewriteEqTrueFalse(rewriteRule, stmtParams[0], stmtParams[1]);
			break;
		case ":constDiff":
		case ":eqSimp":
		case ":eqSame":
		case ":eqBinary":
		case ":distinctBool":
		case ":distinctSame":
		case ":distinctBinary":
		case ":xorTrue":
		case ":xorFalse":
		case ":xorNot":
		case ":xorSame":
		case ":notSimp":
		case ":orSimp":
		case ":orTaut":
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
		case ":eqToXor":
		case ":distinctToXor":
		case ":impToOr":
		case ":strip":
		case ":canonicalSum":
		case ":leqToLeq0":
		case ":ltToLeq0":
		case ":geqToLeq0":
		case ":gtToLeq0":
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
		case ":intern":
		case ":forallExists":
		case ":skolem":
		case ":removeForall":
		default:
			// throw new AssertionError("Unknown Rewrite Rule: " + annotTerm);
			subProof = ProofRules.asserted(rewriteStmt);
		}
		return annotateProved(rewriteStmt, subProof);
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
		default: {
			// throw new AssertionError("Unknown Lemma: " + annotTerm);
			Term subProof = ProofRules.asserted(lemma);
			if (clause.length > 1) {
				subProof = ProofRules.resolutionRule(lemma, subProof, ProofRules.orElim(lemma));
			}
			return subProof;
		}
		}
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
			setResult(convertAsserted(ProofRules.asserted(newParams[0])));
			return;
		}
		case ProofConstants.FN_TAUTOLOGY: {
			setResult(convertTautology(newParams[0]));
			return;
		}
		case ProofConstants.FN_REFL: {
			final Term t = newParams[0];
			setResult(annotateProved(t.getTheory().term(SMTLIBConstants.EQUALS, t, t), ProofRules.refl(t)));
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
		case ProofConstants.FN_REWRITE: {
			setResult(convertRewrite(newParams));
			return;
		}
		case ProofConstants.FN_LEMMA: {
			setResult(convertLemma(newParams));
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
		return unquote(quotedTerm, false);
	}

	Term unquote(final Term quotedTerm, final boolean replaceQuantAux) {
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
}
