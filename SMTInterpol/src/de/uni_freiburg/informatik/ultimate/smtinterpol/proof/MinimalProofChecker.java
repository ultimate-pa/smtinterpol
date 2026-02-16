/*
 * Copyright (C) 2021 University of Freiburg
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
import java.util.Arrays;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedHashSet;
import java.util.Map;
import java.util.Set;
import java.util.Stack;

import de.uni_freiburg.informatik.ultimate.logic.AnnotatedTerm;
import de.uni_freiburg.informatik.ultimate.logic.Annotation;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.ConstantTerm;
import de.uni_freiburg.informatik.ultimate.logic.DataType;
import de.uni_freiburg.informatik.ultimate.logic.DataType.Constructor;
import de.uni_freiburg.informatik.ultimate.logic.FormulaLet;
import de.uni_freiburg.informatik.ultimate.logic.FormulaUnLet;
import de.uni_freiburg.informatik.ultimate.logic.FunctionSymbol;
import de.uni_freiburg.informatik.ultimate.logic.LambdaTerm;
import de.uni_freiburg.informatik.ultimate.logic.Logics;
import de.uni_freiburg.informatik.ultimate.logic.MatchTerm;
import de.uni_freiburg.informatik.ultimate.logic.NonRecursive;
import de.uni_freiburg.informatik.ultimate.logic.QuantifiedFormula;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.SMTLIBConstants;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.logic.Theory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.LogProxy;
import de.uni_freiburg.informatik.ultimate.smtinterpol.option.SMTInterpolConstants;

/**
 * This proof checker checks compliance of SMTInterpol proofs with the minimal
 * proof format.
 *
 * @author Jochen Hoenicke
 */
public class MinimalProofChecker extends NonRecursive {

	/*
	 * The proof checker uses a non-recursive iteration through the proof tree. The
	 * main type in a proof tree is the sort {@literal @}Proof. Each term of this
	 * sort proves a formula and the main task of this code is to compute the proven
	 * formula. The whole proof term should prove the formula false.
	 *
	 * The main idea of this non-recursive algorithm is to push a proof walker for
	 * the {@literal @}Proof terms on the todo stack, which will push the proved
	 * clause of type ProofLiteral[] onto the result stack mStackResults. To handle
	 * functions like res, define-fun, etc. that take a {@literal @}Proof term as
	 * input, first a XYWalker for the function XY is pushed on the todo stack and
	 * then the ProofWalker for the {@literal @}Proof terms are pushed. The Walker
	 * will then call the corresponding walkXY function which checks the proved
	 * arguments, computes the final proved formula and pushes that on the result
	 * stack.
	 *
	 * Simple functions that don't take {@literal @}Proof arguments are handled
	 * directly by calling the walkXY function.
	 */

	/**
	 * The set of all asserted terms (collected from the script by calling
	 * getAssertions()). This is used to check the {@literal @}asserted rules.
	 */
	private Set<Term> mAssertions;

	/**
	 * The SMT script (mainly used to create terms).
	 */
	private final Script mSkript;
	/**
	 * The logger where errors are reported.
	 */
	private final LogProxy mLogger;

	/**
	 * The proof cache. It maps each converted proof to the clause it proves.
	 */
	private HashMap<Term, ProofLiteral[]> mCacheConv;

	/**
	 * Map from auxiliary function symbol to its definition. The auxiliary functions
	 * are functions defined in the proof term with define-fun.
	 */
	private final HashMap<FunctionSymbol, Term> mFunctionDefinitions;

	/**
	 * Map from function name to the expander class for the expand axiom.
	 */
	private final HashMap<String, Expander> mInternalFunctionExpander;

	/**
	 * The result stack. This contains the terms proved by the proof terms.
	 */
	private final Stack<ProofLiteral[]> mStackResults = new Stack<>();

	int mNumOracles, mNumAxioms, mNumResolutions, mNumAssertions, mNumDefineFun;

	/**
	 * Create a proof checker.
	 *
	 * @param script An SMT2 script.
	 * @param logger The logger where errors are reported.
	 */
	public MinimalProofChecker(final Script script, final LogProxy logger) {
		mSkript = script;
		mLogger = logger;
		mFunctionDefinitions = new HashMap<>();
		mInternalFunctionExpander = new HashMap<>();
		addTheoryDefinitions();
	}

	/**
	 * Check a proof for consistency. This reports errors on the logger.
	 *
	 * @param proof the proof to check.
	 * @return true, if no errors were found.
	 */
	public boolean check(final Term proof) {
		mNumOracles = mNumResolutions = mNumAxioms = mNumAssertions = mNumDefineFun = 0;

		final FormulaUnLet unletter = new FormulaUnLet();
		final Term[] assertions = mSkript.getAssertions();
		mAssertions = new HashSet<>(assertions.length);
		for (final Term ass : assertions) {
			mAssertions.add(unletter.transform(ass));
		}

		final ProofLiteral[] result = getProvedClause(unletter.unlet(proof));
		if (result != null && result.length > 0) {
			reportError("The proof did not yield a contradiction but %s", Arrays.asList(result));
			return false;
		}
		return true;
	}

	/**
	 * Split an application term into function symbol and parameters. This also
	 * supports splitting integer and rational constants like {@code (/ 3.0 5.0)} or
	 * {@code (- 5)}.
	 *
	 * @param term The term to split.
	 * @return The function symbol and the paramters.
	 */
	private FunctionSplit splitApplication(Term term) {
		if (term instanceof ApplicationTerm) {
			final ApplicationTerm app = (ApplicationTerm) term;
			return new FunctionSplit(app.getFunction(), app.getParameters());
		} else if (term instanceof ConstantTerm) {
			final Theory t = term.getTheory();
			final Sort sort = term.getSort();
			final Object value = ((ConstantTerm) term).getValue();
			if (value instanceof Rational) {
				final Rational rat = (Rational) value;
				if (!rat.isIntegral()) {
					final FunctionSymbol fsym = t.getFunctionWithResult(SMTLIBConstants.DIVIDE, null, null,
							new Sort[] { sort, sort });
					final Term[] params = new Term[2];
					params[0] = Rational.valueOf(rat.numerator(), BigInteger.ONE).toTerm(sort);
					params[1] = Rational.valueOf(rat.denominator(), BigInteger.ONE).toTerm(sort);
					assert term == t.term(fsym, params);
					return new FunctionSplit(fsym, params);
				} else if (rat.signum() < 0) {
					final FunctionSymbol fsym = t.getFunctionWithResult(SMTLIBConstants.MINUS, null, null,
							new Sort[] { sort });
					final Term[] params = new Term[1];
					params[0] = rat.negate().toTerm(sort);
					assert term == t.term(fsym, params);
					return new FunctionSplit(fsym, params);
				}
			} else if (value instanceof BigInteger) {
				final BigInteger bigInt = (BigInteger) value;
				if (bigInt.signum() < 0) {
					final FunctionSymbol fsym = t.getFunctionWithResult(SMTLIBConstants.MINUS, null, null,
							new Sort[] { sort });
					final Term[] params = new Term[1];
					params[0] = t.constant(bigInt.negate(), sort);
					assert term == t.term(fsym, params);
					return new FunctionSplit(fsym, params);
				}
			}
		}
		return null;
	}

	private Term createAnd(Term[] args) {
		final Theory theory = mSkript.getTheory();
		return args.length == 0 ? theory.mTrue : args.length == 1 ? args[0] : theory.term(SMTLIBConstants.AND, args);
	}

	public boolean checkModelProof(Term proof) {
		mNumOracles = mNumResolutions = mNumAxioms = mNumAssertions = mNumDefineFun = 0;
		mAssertions = Collections.emptySet();

		final FormulaUnLet unletter = new FormulaUnLet();
		proof = unletter.unlet(proof);

		final Map<FunctionSymbol, Term> funcDefs = new HashMap<FunctionSymbol, Term>();
		while (ProofRules.isRefineFun(proof)) {
			final AnnotatedTerm refineFunTerm = (AnnotatedTerm) proof;
			final Object[] annotValues = (Object[]) refineFunTerm.getAnnotations()[0].getValue();
			final FunctionSymbol func = (FunctionSymbol) annotValues[0];
			final Term def = (Term) annotValues[1];
			addRefineFun(funcDefs, func, def);
			proof = refineFunTerm.getSubterm();
		}

		final ProofLiteral[] result = getProvedClause(funcDefs, proof);
		Term destFormula = createAnd(mSkript.getAssertions());
		destFormula = unletter.transform(destFormula);
		if (result != null && result.length != 1 || result[0].getPolarity() != true
				|| result[0].getAtom() != destFormula) {
			reportError("The proof did not prove the assertions but %s", Arrays.asList(result));
			return false;
		}
		return true;
	}

	private void checkFunctionConsistency(FunctionSymbol func, TermVariable[] variables, Term definition) {
		if (variables.length != func.getParameterSorts().length) {
			throw new AssertionError("Parameter count mismatch");
		}
		if (func.getDefinition() != null
				&& (func.getDefinition() != definition || !Arrays.equals(func.getDefinitionVars(), variables))) {
			throw new AssertionError("Inconsistent function definition.");
		}
	}

	public void addRefineFun(Map<FunctionSymbol, Term> funcDefs, FunctionSymbol func, Term def) {
		if (func.isIntern()) {
			// TODO: check that function definition is refinement.
			// i.e. divison is only refined for division by 0,
			// selector is only refined for different constructor,
			// @diff is only refined in such a way that it returns an element where the
			// arrays differ.
		}
		if (def instanceof LambdaTerm) {
			final LambdaTerm lambda = (LambdaTerm) def;
			checkFunctionConsistency(func, lambda.getVariables(), lambda.getSubterm());
		} else {
			checkFunctionConsistency(func, new TermVariable[0], def);
		}
		if (funcDefs.containsKey(func)) {
			throw new AssertionError("Double function definition.");
		}
		funcDefs.put(func, def);
	}

	private static Term expandDefinition(Term definition, TermVariable[] vars, Term[] params) {
		return new FormulaUnLet().unlet(definition.getTheory().let(vars, params, definition));
	}

	void registerExpand(String funcName, Expander expander) {
		mInternalFunctionExpander.put(funcName, expander);
	}

	private void addTheoryDefinitions() {
		final Theory theory = mSkript.getTheory();
		final Logics logic = theory.getLogic();
		if (logic.isArithmetic() || logic.isBitVector()) {
			ArithmeticRules.registerRules(this);
		}
		if (logic.isBitVector()) {
			BitvectorRules.registerRules(this);
		}
	}

	public int getNumberOfHoles() {
		return mNumOracles;
	}

	public int getNumberOfResolutions() {
		return mNumResolutions;
	}

	public int getNumberOfAxioms() {
		return mNumAxioms;
	}

	public int getNumberOfAssertions() {
		return mNumAssertions;
	}

	public int getNumberOfDefineFun() {
		return mNumDefineFun;
	}

	/**
	 * Check a proof for consistency and compute the proved clause. This prints
	 * warnings for missing pivot literals.
	 *
	 * @param proof the proof to check.
	 * @return the proved clause.
	 */
	public ProofLiteral[] getProvedClause(final Term proof) {
		return getProvedClause(null, proof);
	}

	/**
	 * Check a proof for consistency and compute the proved clause. This prints
	 * warnings for missing pivot literals.
	 *
	 * @param funcDefs the function definitions (for expand rule)
	 * @param proof    the proof to check.
	 * @return the proved clause.
	 */
	public ProofLiteral[] getProvedClause(final Map<FunctionSymbol, Term> funcDefs, final Term proof) {
		// Initializing the proof-checker-cache
		mCacheConv = new HashMap<>();
		if (funcDefs != null) {
			for (final Map.Entry<FunctionSymbol, Term> funcDef : funcDefs.entrySet()) {
				final FunctionSymbol func = funcDef.getKey();
				final Term def = funcDef.getValue();
				if (func.getDefinition() != null) {
					// check that definitions equal
					if (func.getDefinitionVars().length == 0) {
						if (func.getDefinition() != def) {
							throw new AssertionError("Inconsistent function definition.");
						}
					} else {
						final LambdaTerm lambda = (LambdaTerm) def;
						if (func.getDefinition() != lambda.getSubterm()
								|| !Arrays.equals(func.getDefinitionVars(), lambda.getVariables())) {
							throw new AssertionError("Inconsistent function definition.");
						}
					}
				}
				mFunctionDefinitions.put(func, def);
			}
		}
		run(new ProofWalker(proof));
		assert (mStackResults.size() == 1);
		if (funcDefs != null) {
			for (final FunctionSymbol func : funcDefs.keySet()) {
				mFunctionDefinitions.remove(func);
			}
		}
		// clear state
		mCacheConv = null;

		return stackPop();
	}

	private void reportError(final String msg, final Object... params) {
		mLogger.error(msg, params);
	}

	private void reportWarning(final String msg, final Object... params) {
		mLogger.warn(msg, params);
	}

	/**
	 * The proof walker. This takes a proof term and pushes the proven formula on
	 * the result stack. It also checks the proof cache to prevent running over the
	 * same term twice.
	 *
	 * @param proofTerm The proof term. Its sort must be {@literal @}Proof.
	 */
	void walk(Term proofTerm) {
		while (proofTerm instanceof AnnotatedTerm && !ProofRules.isAxiom(proofTerm)
				&& !ProofRules.isDefineFun(proofTerm)) {
			if (ProofRules.isRefineFun(proofTerm)) {
				mLogger.warn("Ignoring refine-fun in the middle of the proof term", proofTerm);
			}
			proofTerm = ((AnnotatedTerm) proofTerm).getSubterm();
		}
		/* Check the cache, if the unfolding step was already done */
		if (mCacheConv.containsKey(proofTerm)) {
			mStackResults.push(mCacheConv.get(proofTerm));
			return;
		}
		if (ProofRules.isDefineFun(proofTerm)) {
			new DefineFunWalker((AnnotatedTerm) proofTerm).enqueue(this);
		} else if (ProofRules.isAxiom(proofTerm)) {
			stackPush(computeAxiom(proofTerm), proofTerm);
		} else if (ProofRules.isProofRule(ProofRules.RES, proofTerm)) {
			new ResolutionWalker((ApplicationTerm) proofTerm).enqueue(this);
		} else {
			stackPush(checkAssert(proofTerm), proofTerm);
		}
	}

	/**
	 * Handle the resolution rule. The stack should contain the converted input
	 * clauses.
	 *
	 * @param resApp The <code>{@literal @}res</code> application from the original
	 *               proof.
	 */
	ProofLiteral[] walkResolution(final ApplicationTerm resApp, final ProofLiteral[] posClause,
			final ProofLiteral[] negClause) {
		mNumResolutions++;

		/*
		 * allDisjuncts is the currently computed resolution result.
		 */
		final HashSet<ProofLiteral> allDisjuncts = new HashSet<>();

		final Term pivot = resApp.getParameters()[0];
		final ProofLiteral posPivot = new ProofLiteral(pivot, true);
		final ProofLiteral negPivot = new ProofLiteral(pivot, false);

		/* Add non-pivot disjuncts of the first clause. */
		boolean pivotFound = false;
		for (final ProofLiteral lit : posClause) {
			if (lit.equals(posPivot)) {
				pivotFound = true;
			} else {
				allDisjuncts.add(lit);
			}
		}

		/* Remove the pivot from allDisjuncts */
		if (!pivotFound) {
			reportWarning("Could not find pivot %s in %s", posPivot, Arrays.asList(posClause));
		}

		pivotFound = false;
		for (final ProofLiteral lit : negClause) {
			if (lit.equals(negPivot)) {
				pivotFound = true;
			} else {
				allDisjuncts.add(lit);
			}
		}

		if (!pivotFound) {
			reportWarning("Could not find pivot %s in %s", negPivot, Arrays.asList(negClause));
		}
		return allDisjuncts.toArray(new ProofLiteral[allDisjuncts.size()]);
	}

	/* === Auxiliary functions === */

	void stackPush(final ProofLiteral[] pushClause, final Term keyTerm) {
		mCacheConv.put(keyTerm, pushClause);
		mStackResults.push(pushClause);
	}

	ProofLiteral[] stackPop() {
		return mStackResults.pop();
	}

	public ProofLiteral[] computeAxiom(final Term axiom) {
		mNumAxioms++;
		final Theory theory = axiom.getTheory();
		assert ProofRules.isAxiom(axiom);
		final Annotation[] annots = ((AnnotatedTerm) axiom).getAnnotations();
		switch (annots[0].getKey()) {
		case ":" + ProofRules.ORACLE: {
			mNumOracles++;
			mNumAxioms--;
			reportWarning("Used oracle: %s", Arrays.asList(annots).subList(1, annots.length));
			mLogger.info("Full oracle: %s", new Object() {
				@Override
				public String toString() {
					final Term letted = new FormulaLet().let(axiom);
					final StringBuilder sb = new StringBuilder();
					ProofRules.printProof(sb, letted);
					return sb.toString();
				}
			});
			// convert to clause (and remove multiple occurrences)
			final ProofLiteral[] lits = ProofRules.proofLiteralsFromAnnotation((Object[]) annots[0].getValue());
			final LinkedHashSet<ProofLiteral> clause = new LinkedHashSet<>(Arrays.asList(lits));
			return clause.toArray(new ProofLiteral[clause.size()]);
		}
		case ":" + ProofRules.TRUEI: {
			final Object[] ruleParams = (Object[]) annots[0].getValue();
			assert ruleParams.length == 0;
			return new ProofLiteral[] { new ProofLiteral(theory.term(SMTLIBConstants.TRUE), true) };
		}
		case ":" + ProofRules.FALSEE: {
			final Object[] ruleParams = (Object[]) annots[0].getValue();
			assert ruleParams.length == 0;
			return new ProofLiteral[] { new ProofLiteral(theory.term(SMTLIBConstants.FALSE), false) };
		}
		case ":" + ProofRules.NOTI: {
			assert annots.length == 1;
			final Object[] ruleParams = (Object[]) annots[0].getValue();
			assert ruleParams.length == 1;
			final ApplicationTerm notTerm = (ApplicationTerm) ruleParams[0];
			if (!notTerm.getFunction().isIntern() || !notTerm.getFunction().getName().equals(SMTLIBConstants.NOT)) {
				reportError("Expected not application");
				return getTrueClause(notTerm.getTheory());
			}
			// (not t), t
			return new ProofLiteral[] { new ProofLiteral(notTerm, true),
					new ProofLiteral(notTerm.getParameters()[0], true) };
		}
		case ":" + ProofRules.NOTE: {
			assert annots.length == 1;
			final Object[] ruleParams = (Object[]) annots[0].getValue();
			assert ruleParams.length == 1;
			final ApplicationTerm notTerm = (ApplicationTerm) ruleParams[0];
			if (!notTerm.getFunction().isIntern() || !notTerm.getFunction().getName().equals(SMTLIBConstants.NOT)) {
				reportError("Expected not application");
				return getTrueClause(notTerm.getTheory());
			}
			// ~(not t), ~t
			return new ProofLiteral[] { new ProofLiteral(notTerm, false),
					new ProofLiteral(notTerm.getParameters()[0], false) };
		}
		case ":" + ProofRules.ORI: {
			assert annots.length == 1;
			final Object[] ruleParams = (Object[]) annots[0].getValue();
			assert ruleParams.length == 2;
			final ApplicationTerm orTerm = (ApplicationTerm) ruleParams[1];
			if (!ProofRules.isApplication(SMTLIBConstants.OR, orTerm)) {
				reportError("Expected or application");
				return getTrueClause(orTerm.getTheory());
			}
			final Term[] orParams = orTerm.getParameters();
			final int pos = (Integer) ruleParams[0];
			assert pos >= 0 && pos < orParams.length;

			// (or t1 ... tn), ~tpos
			return new ProofLiteral[] { new ProofLiteral(orTerm, true), new ProofLiteral(orParams[pos], false) };
		}
		case ":" + ProofRules.ORE: {
			assert annots.length == 1;
			final Object[] ruleParams = (Object[]) annots[0].getValue();
			assert ruleParams.length == 1;
			final ApplicationTerm orTerm = (ApplicationTerm) ruleParams[0];
			if (!ProofRules.isApplication(SMTLIBConstants.OR, orTerm)) {
				reportError("Expected or application");
				return getTrueClause(orTerm.getTheory());
			}
			final Term[] params = orTerm.getParameters();

			// ~(or t1 ... tn), t1, ..., tn
			final HashSet<ProofLiteral> clause = new LinkedHashSet<>();
			clause.add(new ProofLiteral(orTerm, false));
			for (final Term param : params) {
				clause.add(new ProofLiteral(param, true));
			}
			return clause.toArray(new ProofLiteral[clause.size()]);
		}
		case ":" + ProofRules.ANDI: {
			assert annots.length == 1;
			final Object[] ruleParams = (Object[]) annots[0].getValue();
			assert ruleParams.length == 1;
			final ApplicationTerm andTerm = (ApplicationTerm) ruleParams[0];
			if (!andTerm.getFunction().isIntern() || !andTerm.getFunction().getName().equals(SMTLIBConstants.AND)) {
				reportError("Expected and application");
				return getTrueClause(andTerm.getTheory());
			}
			final Term[] params = andTerm.getParameters();

			// (and t1 ... tn), ~t1, ..., ~tn
			final HashSet<ProofLiteral> clause = new LinkedHashSet<>();
			clause.add(new ProofLiteral(andTerm, true));
			for (final Term param : params) {
				clause.add(new ProofLiteral(param, false));
			}
			return clause.toArray(new ProofLiteral[clause.size()]);
		}
		case ":" + ProofRules.ANDE: {
			assert annots.length == 1;
			final Object[] ruleParams = (Object[]) annots[0].getValue();
			assert ruleParams.length == 2;
			final ApplicationTerm andTerm = (ApplicationTerm) ruleParams[1];
			if (!andTerm.getFunction().isIntern() || !andTerm.getFunction().getName().equals(SMTLIBConstants.AND)) {
				reportError("Expected and application");
				return getTrueClause(andTerm.getTheory());
			}
			final Term[] params = andTerm.getParameters();
			final int pos = (Integer) ruleParams[0];
			assert pos >= 0 && pos < params.length;

			// ~(and t1 ... tn), tpos
			return new ProofLiteral[] { new ProofLiteral(andTerm, false), new ProofLiteral(params[pos], true) };
		}
		case ":" + ProofRules.IMPI: {
			assert annots.length == 1;
			final Object[] ruleParams = (Object[]) annots[0].getValue();
			assert ruleParams.length == 2;
			final ApplicationTerm impTerm = (ApplicationTerm) ruleParams[1];
			if (!impTerm.getFunction().isIntern() || !impTerm.getFunction().getName().equals(SMTLIBConstants.IMPLIES)) {
				reportError("Expected => application");
				return getTrueClause(impTerm.getTheory());
			}
			final Term[] params = impTerm.getParameters();
			final int pos = (Integer) ruleParams[0];
			assert pos >= 0 && pos < params.length;

			// (=> t1 ... tn), tpos (~tpos if pos == n)
			return new ProofLiteral[] { new ProofLiteral(impTerm, true),
					new ProofLiteral(params[pos], pos < params.length - 1) };
		}
		case ":" + ProofRules.IMPE: {
			assert annots.length == 1;
			final Object[] ruleParams = (Object[]) annots[0].getValue();
			assert ruleParams.length == 1;
			final ApplicationTerm impTerm = (ApplicationTerm) ruleParams[0];
			if (!impTerm.getFunction().isIntern() || !impTerm.getFunction().getName().equals(SMTLIBConstants.IMPLIES)) {
				reportError("Expected => application");
				return getTrueClause(impTerm.getTheory());
			}
			final Term[] params = impTerm.getParameters();

			// ~(=> t1 ... tn), ~t1, ..., ~tn-1, tn
			final HashSet<ProofLiteral> clause = new LinkedHashSet<>();
			clause.add(new ProofLiteral(impTerm, false));
			for (int i = 0; i < params.length; i++) {
				clause.add(new ProofLiteral(params[i], i == params.length - 1));
			}
			return clause.toArray(new ProofLiteral[clause.size()]);
		}
		case ":" + ProofRules.IFFI1: {
			assert annots.length == 1;
			final Object[] ruleParams = (Object[]) annots[0].getValue();
			assert ruleParams.length == 1;
			final ApplicationTerm iffTerm = (ApplicationTerm) ruleParams[0];
			if (!iffTerm.getFunction().isIntern() || !iffTerm.getFunction().getName().equals(SMTLIBConstants.EQUALS)) {
				reportError("Expected = application");
				return getTrueClause(iffTerm.getTheory());
			}
			final Term[] params = iffTerm.getParameters();
			if (params.length != 2 || params[0].getSort().getName() != SMTLIBConstants.BOOL) {
				return reportViolatedSideCondition(axiom);
			}

			// (= t1 t2), t1, t2
			return new ProofLiteral[] { new ProofLiteral(iffTerm, true), new ProofLiteral(params[0], true),
					new ProofLiteral(params[1], true) };
		}
		case ":" + ProofRules.IFFI2: {
			assert annots.length == 1;
			final Object[] ruleParams = (Object[]) annots[0].getValue();
			assert ruleParams.length == 1;
			final ApplicationTerm iffTerm = (ApplicationTerm) ruleParams[0];
			if (!iffTerm.getFunction().isIntern() || !iffTerm.getFunction().getName().equals(SMTLIBConstants.EQUALS)) {
				reportError("Expected = application");
				return getTrueClause(iffTerm.getTheory());
			}
			final Term[] params = iffTerm.getParameters();
			if (params.length != 2 || params[0].getSort().getName() != SMTLIBConstants.BOOL) {
				return reportViolatedSideCondition(axiom);
			}

			// (= t1 t2), ~t1, ~t2
			return new ProofLiteral[] { new ProofLiteral(iffTerm, true), new ProofLiteral(params[0], false),
					new ProofLiteral(params[1], false) };
		}
		case ":" + ProofRules.IFFE1: {
			assert annots.length == 1;
			final Object[] ruleParams = (Object[]) annots[0].getValue();
			assert ruleParams.length == 1;
			final ApplicationTerm iffTerm = (ApplicationTerm) ruleParams[0];
			if (!iffTerm.getFunction().isIntern() || !iffTerm.getFunction().getName().equals(SMTLIBConstants.EQUALS)) {
				reportError("Expected = application");
				return getTrueClause(iffTerm.getTheory());
			}
			final Term[] params = iffTerm.getParameters();
			if (params.length != 2 || params[0].getSort().getName() != SMTLIBConstants.BOOL) {
				return reportViolatedSideCondition(axiom);
			}

			// ~(= t1 t2), t1, ~t2
			return new ProofLiteral[] { new ProofLiteral(iffTerm, false), new ProofLiteral(params[0], true),
					new ProofLiteral(params[1], false) };
		}
		case ":" + ProofRules.IFFE2: {
			assert annots.length == 1;
			final Object[] ruleParams = (Object[]) annots[0].getValue();
			assert ruleParams.length == 1;
			final ApplicationTerm iffTerm = (ApplicationTerm) ruleParams[0];
			if (!iffTerm.getFunction().isIntern() || !iffTerm.getFunction().getName().equals(SMTLIBConstants.EQUALS)) {
				reportError("Expected = application");
				return getTrueClause(iffTerm.getTheory());
			}
			final Term[] params = iffTerm.getParameters();
			if (params.length != 2 || params[0].getSort().getName() != SMTLIBConstants.BOOL) {
				return reportViolatedSideCondition(axiom);
			}

			// ~(= t1 t2), ~t1, t2
			return new ProofLiteral[] { new ProofLiteral(iffTerm, false), new ProofLiteral(params[0], false),
					new ProofLiteral(params[1], true) };
		}
		case ":" + ProofRules.XORI: {
			assert annots.length == 1;
			final Term[][] xorLists = (Term[][]) annots[0].getValue();
			assert xorLists.length == 3;
			if (!ProofRules.checkXorParams(xorLists)) {
				return reportViolatedSideCondition(axiom);
			}
			// (xor set0), (xor set1), ~(xor set2)
			final ProofLiteral[] clause = new ProofLiteral[3];
			for (int i = 0; i < 3; i++) {
				final Term term = xorLists[i].length == 1 ? xorLists[i][0]
						: theory.term(SMTLIBConstants.XOR, xorLists[i]);
				assert term != null;
				clause[i] = new ProofLiteral(term, i < 2);
			}
			return clause;
		}
		case ":" + ProofRules.XORE: {
			assert annots.length == 1;
			final Term[][] xorLists = (Term[][]) annots[0].getValue();
			assert xorLists.length == 3;
			if (!ProofRules.checkXorParams(xorLists)) {
				return reportViolatedSideCondition(axiom);
			}
			// ~(xor set0), ~(xor set1), ~(xor set2)
			final ProofLiteral[] clause = new ProofLiteral[3];
			for (int i = 0; i < 3; i++) {
				final Term term = xorLists[i].length == 1 ? xorLists[i][0]
						: theory.term(SMTLIBConstants.XOR, xorLists[i]);
				assert term != null;
				clause[i] = new ProofLiteral(term, false);
			}
			return clause;
		}
		case ":" + ProofRules.EQI: {
			assert annots.length == 1;
			final Object[] ruleParams = (Object[]) annots[0].getValue();
			assert ruleParams.length == 1;
			final ApplicationTerm eqTerm = (ApplicationTerm) ruleParams[0];
			if (!eqTerm.getFunction().isIntern() || !eqTerm.getFunction().getName().equals(SMTLIBConstants.EQUALS)) {
				reportError("Expected = application");
				return getTrueClause(eqTerm.getTheory());
			}
			final Term[] params = eqTerm.getParameters();

			// (= t1 ... tn), ~(= t1 t2), ~(tn-1 tn)
			final ProofLiteral[] clause = new ProofLiteral[params.length];
			clause[0] = new ProofLiteral(eqTerm, true);
			for (int i = 0; i < params.length - 1; i++) {
				clause[i + 1] = new ProofLiteral(theory.term(SMTLIBConstants.EQUALS, params[i], params[i + 1]), false);
			}
			return clause;
		}
		case ":" + ProofRules.EQE: {
			assert annots.length == 1;
			final Object[] ruleParams = (Object[]) annots[0].getValue();
			assert ruleParams.length == 3;
			final ApplicationTerm eqTerm = (ApplicationTerm) ruleParams[2];
			if (!eqTerm.getFunction().isIntern() || !eqTerm.getFunction().getName().equals(SMTLIBConstants.EQUALS)) {
				reportError("Expected = application");
				return getTrueClause(eqTerm.getTheory());
			}
			final Term[] params = eqTerm.getParameters();
			final int pos0 = (Integer) ruleParams[0];
			final int pos1 = (Integer) ruleParams[1];
			assert 0 <= pos0 && pos0 < params.length && 0 <= pos1 && pos1 < params.length;

			// ~(= t1 ... tn), (= ti tj)
			return new ProofLiteral[] { new ProofLiteral(eqTerm, false),
					new ProofLiteral(theory.term(SMTLIBConstants.EQUALS, params[pos0], params[pos1]), true) };
		}
		case ":" + ProofRules.DISTINCTI: {
			assert annots.length == 1;
			final Object[] ruleParams = (Object[]) annots[0].getValue();
			assert ruleParams.length == 1;
			final ApplicationTerm distinctTerm = (ApplicationTerm) ruleParams[0];
			if (!distinctTerm.getFunction().isIntern()
					|| !distinctTerm.getFunction().getName().equals(SMTLIBConstants.DISTINCT)) {
				reportError("Expected distinct application");
				return getTrueClause(distinctTerm.getTheory());
			}
			final Term[] params = distinctTerm.getParameters();
			final int len = params.length;

			// (distinct t1 ... tn), (= t1 t2),...
			final ProofLiteral[] clause = new ProofLiteral[1 + len * (len - 1) / 2];
			clause[0] = new ProofLiteral(distinctTerm, true);
			int pos = 1;
			for (int i = 0; i < len - 1; i++) {
				for (int j = i + 1; j < len; j++) {
					clause[pos++] = new ProofLiteral(theory.term(SMTLIBConstants.EQUALS, params[i], params[j]), true);
				}
			}
			assert pos == clause.length;
			return clause;
		}
		case ":" + ProofRules.DISTINCTE: {
			assert annots.length == 1;
			final Object[] ruleParams = (Object[]) annots[0].getValue();
			assert ruleParams.length == 3;
			final ApplicationTerm distinctTerm = (ApplicationTerm) ruleParams[2];
			if (!distinctTerm.getFunction().isIntern()
					|| !distinctTerm.getFunction().getName().equals(SMTLIBConstants.DISTINCT)) {
				reportError("Expected distinct application");
				return getTrueClause(distinctTerm.getTheory());
			}
			final Term[] params = distinctTerm.getParameters();
			final int pos0 = (Integer) ruleParams[0];
			final int pos1 = (Integer) ruleParams[1];
			assert 0 <= pos0 && pos0 < params.length && 0 <= pos1 && pos1 < params.length;

			// ~(distinct t1 ... tn), ~(= ti tj)
			return new ProofLiteral[] { new ProofLiteral(distinctTerm, false),
					new ProofLiteral(theory.term(SMTLIBConstants.EQUALS, params[pos0], params[pos1]), false) };
		}
		case ":" + ProofRules.ITE1: {
			assert annots.length == 1;
			final Object[] ruleParams = (Object[]) annots[0].getValue();
			assert ruleParams.length == 1;
			final ApplicationTerm iteTerm = (ApplicationTerm) ruleParams[0];
			if (!iteTerm.getFunction().isIntern() || !iteTerm.getFunction().getName().equals(SMTLIBConstants.ITE)) {
				reportError("Expected ite application");
				return getTrueClause(iteTerm.getTheory());
			}
			final Term[] params = iteTerm.getParameters();
			assert params.length == 3;

			// (= (ite c t e) t), ~c
			return new ProofLiteral[] { new ProofLiteral(theory.term(SMTLIBConstants.EQUALS, iteTerm, params[1]), true),
					new ProofLiteral(params[0], false) };
		}
		case ":" + ProofRules.ITE2: {
			assert annots.length == 1;
			final Object[] ruleParams = (Object[]) annots[0].getValue();
			assert ruleParams.length == 1;
			final ApplicationTerm iteTerm = (ApplicationTerm) ruleParams[0];
			if (!iteTerm.getFunction().isIntern() || !iteTerm.getFunction().getName().equals(SMTLIBConstants.ITE)) {
				reportError("Expected ite application");
				return getTrueClause(iteTerm.getTheory());
			}
			final Term[] params = iteTerm.getParameters();
			assert params.length == 3;

			// (= (ite c t e) e), c
			return new ProofLiteral[] { new ProofLiteral(theory.term(SMTLIBConstants.EQUALS, iteTerm, params[2]), true),
					new ProofLiteral(params[0], true) };
		}
		case ":" + ProofRules.DELANNOT: {
			assert annots.length == 1;
			final Object[] ruleParams = (Object[]) annots[0].getValue();
			assert ruleParams.length == 1;
			if (!(ruleParams[0] instanceof AnnotatedTerm)) {
				return reportViolatedSideCondition(axiom);
			}
			final AnnotatedTerm annotTerm = (AnnotatedTerm) ruleParams[0];
			final Term subterm = annotTerm.getSubterm();

			// (= (! t :...) t)
			return new ProofLiteral[] {
					new ProofLiteral(theory.term(SMTLIBConstants.EQUALS, annotTerm, subterm), true) };
		}
		case ":" + ProofRules.REFL: {
			assert annots.length == 1;
			final Term[] ruleParams = (Term[]) annots[0].getValue();
			assert ruleParams.length == 1;

			// (= a a)
			return new ProofLiteral[] {
					new ProofLiteral(theory.term(SMTLIBConstants.EQUALS, ruleParams[0], ruleParams[0]), true) };
		}
		case ":" + ProofRules.SYMM: {
			assert annots.length == 1;
			final Term[] ruleParams = (Term[]) annots[0].getValue();
			assert ruleParams.length == 2;

			// (= a0 a1), ~(= a1 a0)
			return new ProofLiteral[] { new ProofLiteral(theory.term(SMTLIBConstants.EQUALS, ruleParams), true),
					new ProofLiteral(theory.term(SMTLIBConstants.EQUALS, ruleParams[1], ruleParams[0]), false) };
		}
		case ":" + ProofRules.TRANS: {
			assert annots.length == 1;
			final Term[] ruleParams = (Term[]) annots[0].getValue();
			assert ruleParams.length > 2;
			final int len = ruleParams.length;

			// (= a0 alen-1), ~(= a0 a1), ..., ~(= alen-2 alen-1)
			final ProofLiteral[] clause = new ProofLiteral[len];
			clause[0] = new ProofLiteral(theory.term(SMTLIBConstants.EQUALS, ruleParams[0], ruleParams[len - 1]), true);
			for (int i = 0; i < len - 1; i++) {
				clause[i + 1] = new ProofLiteral(theory.term(SMTLIBConstants.EQUALS, ruleParams[i], ruleParams[i + 1]), false);
			}
			return clause;
		}
		case ":" + ProofRules.CONG: {
			assert annots.length == 1;
			final Term[] congArgs = (Term[]) annots[0].getValue();
			assert congArgs.length == 2;
			final FunctionSplit split0 = splitApplication(congArgs[0]);
			final FunctionSplit split1 = splitApplication(congArgs[1]);
			if (split0 == null || split1 == null || split0.mFunc != split1.mFunc
					|| split0.mParams.length != split1.mParams.length) {
				return reportViolatedSideCondition(axiom);
			}
			final FunctionSymbol func = split0.mFunc;
			final int paramCount = split0.mParams.length;
			final Term app0 = theory.term(func, split0.mParams);
			final Term app1 = theory.term(func, split1.mParams);

			// (= (f a0...an) (f b0... bn)), ~(= a0 b0), ..., ~(= an bn)
			final LinkedHashSet<ProofLiteral> clause = new LinkedHashSet<>();
			clause.add(new ProofLiteral(theory.term(SMTLIBConstants.EQUALS, app0, app1), true));
			for (int i = 0; i < paramCount; i++) {
				clause.add(new ProofLiteral(theory.term(SMTLIBConstants.EQUALS, split0.mParams[i], split1.mParams[i]),
						false));
			}
			return clause.toArray(new ProofLiteral[clause.size()]);
		}
		case ":" + ProofRules.EXPAND: {
			assert annots.length == 1;
			final Object[] ruleParams = (Object[]) annots[0].getValue();
			assert ruleParams.length == 1;
			final ApplicationTerm app = (ApplicationTerm) ruleParams[0];
			final FunctionSymbol func = app.getFunction();
			final Term[] params = app.getParameters();
			Term rhs;
			if (func.isLeftAssoc() && params.length > 2) {
				rhs = params[0];
				for (int i = 1; i < params.length; i++) {
					rhs = theory.term(func, rhs, params[i]);
				}
			} else if (func.isRightAssoc() && params.length > 2) {
				rhs = params[params.length - 1];
				for (int i = params.length - 2; i >= 0; i--) {
					rhs = theory.term(func, params[i], rhs);
				}
			} else if (func.isChainable() && params.length > 2) {
				final Term[] chain = new Term[params.length - 1];
				for (int i = 0; i < chain.length; i++) {
					chain[i] = theory.term(func, params[i], params[i + 1]);
				}
				rhs = theory.term("and", chain);
			} else if (func.getDefinition() != null) {
				rhs = expandDefinition(func.getDefinition(), func.getDefinitionVars(), params);
			} else if (func.isIntern() && mInternalFunctionExpander.containsKey(func.getName())) {
				final Expander expander = mInternalFunctionExpander.get(func.getName());
				rhs = expander.expand(func, params);
			} else if (mFunctionDefinitions.containsKey(func)) {
				final Term definition = mFunctionDefinitions.get(func);
				if (definition instanceof LambdaTerm) {
					final LambdaTerm lambda = (LambdaTerm) definition;
					rhs = expandDefinition(lambda.getSubterm(), lambda.getVariables(), params);
				} else {
					assert params.length == 0;
					rhs = definition;
				}
			} else {
				throw new AssertionError();
			}
			return new ProofLiteral[] { new ProofLiteral(theory.term("=", app, rhs), true) };
		}
		case ":" + ProofRules.FORALLI:
		case ":" + ProofRules.EXISTSE: {
			assert annots.length == 1;
			final Object[] ruleParams = (Object[]) annots[0].getValue();
			assert ruleParams.length == 1;
			final boolean isForall = annots[0].getKey().equals(":" + ProofRules.FORALLI);
			final QuantifiedFormula quant = (QuantifiedFormula) ruleParams[0];
			if (quant.getQuantifier() != (isForall ? QuantifiedFormula.FORALL : QuantifiedFormula.EXISTS)) {
				reportError("Quantifier of wrong type");
				return getTrueClause(theory);
			}
			final TermVariable[] termVars = quant.getVariables();
			final Term[] skolemTerms = new ProofRules(theory).getSkolemVars(termVars, quant.getSubformula(), isForall);
			final Term letted = theory.let(termVars, skolemTerms, quant.getSubformula());

			// (forall (vars) F), ~(let skolem F)
			// ~(exists (vars) F), (let skolem F)
			return new ProofLiteral[] { new ProofLiteral(quant, isForall),
					new ProofLiteral(new FormulaUnLet().unlet(letted), !isForall) };
		}
		case ":" + ProofRules.FORALLE:
		case ":" + ProofRules.EXISTSI: {
			assert annots.length == 1;
			final Object[] ruleParams = (Object[]) annots[0].getValue();
			assert ruleParams.length == 2;
			final boolean isForall = annots[0].getKey().equals(":" + ProofRules.FORALLE);
			final QuantifiedFormula quant = (QuantifiedFormula) ruleParams[1];
			if (quant.getQuantifier() != (isForall ? QuantifiedFormula.FORALL : QuantifiedFormula.EXISTS)) {
				reportError("Quantifier of wrong type");
				return getTrueClause(theory);
			}
			final TermVariable[] termVars = quant.getVariables();
			final Term[] values = (Term[]) ruleParams[0];
			final Term letted = theory.let(termVars, values, quant.getSubformula());

			// ~(forall (vars) F), (let values F)
			// (exists (vars) F), ~(let values F)
			return new ProofLiteral[] { new ProofLiteral(quant, !isForall),
					new ProofLiteral(new FormulaUnLet().unlet(letted), isForall) };
		}
		case ":" + ProofRules.TRICHOTOMY: {
			if (!theory.getLogic().isArithmetic() && !theory.getLogic().isBitVector()) {
				reportError("Proof requires arithmetic");
				return getTrueClause(theory);
			}
			final Term[] params = (Term[]) annots[0].getValue();
			assert annots.length == 1;
			if (params.length != 2) {
				throw new AssertionError();
			}
			return ArithmeticRules.trichotomy(this, theory, params);
		}
		case ":" + ProofRules.TOTAL: {
			if (!theory.getLogic().isArithmetic() && !theory.getLogic().isBitVector()) {
				reportError("Proof requires arithmetic");
				return getTrueClause(theory);
			}
			final Term[] params = (Term[]) annots[0].getValue();
			assert annots.length == 1;
			assert params.length == 2;
			return ArithmeticRules.total(this, theory, params);
		}
		case ":" + ProofRules.TOTALINT: {
			if (!theory.getLogic().hasIntegers() && !theory.getLogic().isBitVector()) {
				reportError("Proof requires integer arithmetic");
				return getTrueClause(theory);
			}
			assert annots.length == 1;
			final Term[] params = (Term[]) annots[0].getValue();
			assert params.length == 2;
			final ProofLiteral[] result = ArithmeticRules.totalInt(this, theory, params);
			if (result == null) {
				return reportViolatedSideCondition(axiom);
			}
			return result;
		}
		case ":" + ProofRules.FARKAS: {
			if (!theory.getLogic().isArithmetic() && !theory.getLogic().isBitVector()) {
				reportError("Proof requires arithmetic");
				return getTrueClause(theory);
			}
			final Object[] params = (Object[]) annots[0].getValue();
			assert annots.length == 1;
			if (!ArithmeticRules.checkFarkas(params)) {
				return reportViolatedSideCondition(axiom);
			}
			final HashSet<ProofLiteral> clause = new HashSet<>();
			for (int i = 1; i < params.length; i += 2) {
				clause.add(new ProofLiteral((Term) params[i], false));
			}
			return clause.toArray(new ProofLiteral[clause.size()]);
		}
		case ":" + ProofRules.MULPOS: {
			if (!theory.getLogic().isArithmetic() && !theory.getLogic().isBitVector()) {
				reportError("Proof requires arithmetic");
				return getTrueClause(theory);
			}
			final Term[] ineqs = (Term[]) annots[0].getValue();
			assert annots.length == 0;
			if (!ArithmeticRules.checkMulPos(ineqs)) {
				return reportViolatedSideCondition(axiom);
			}
			final HashSet<ProofLiteral> clause = new HashSet<>();
			for (int i = 0; i < ineqs.length; i++) {
				clause.add(new ProofLiteral(ineqs[i], i == ineqs.length - 1));
			}
			return clause.toArray(new ProofLiteral[clause.size()]);
		}
		case ":" + ProofRules.POLYADD: {
			if (!theory.getLogic().isArithmetic() && !theory.getLogic().isBitVector()) {
				reportError("Proof requires arithmetic");
				return getTrueClause(theory);
			}
			final Term[] params = (Term[]) annots[0].getValue();
			assert annots.length == 1;
			assert params.length == 2;
			if (!ArithmeticRules.checkPolyAdd(params[0], params[1])) {
				return reportViolatedSideCondition(axiom);
			}
			return new ProofLiteral[] {
					new ProofLiteral(theory.term(SMTLIBConstants.EQUALS, params[0], params[1]), true) };
		}
		case ":" + ProofRules.POLYMUL: {
			if (!theory.getLogic().isArithmetic() && !theory.getLogic().isBitVector()) {
				reportError("Proof requires arithmetic");
				return getTrueClause(theory);
			}
			final Term[] params = (Term[]) annots[0].getValue();
			assert annots.length == 1;
			assert params.length == 2;
			if (!ArithmeticRules.checkPolyMul(params[0], params[1])) {
				return reportViolatedSideCondition(axiom);
			}
			return new ProofLiteral[] {
					new ProofLiteral(theory.term(SMTLIBConstants.EQUALS, params[0], params[1]), true) };
		}
		case ":" + ProofRules.TOREALDEF: {
			if (!theory.getLogic().hasReals() || (!theory.getLogic().isIRA() && !theory.getLogic().isBitVector())) {
				reportError("Proof requires arithmetic");
				return getTrueClause(theory);
			}
			assert annots.length == 1;
			final Object[] params = (Object[]) annots[0].getValue();
			assert params.length == 1;
			final Term integerTerm = (Term) params[0];
			final Term lhs = theory.term(SMTLIBConstants.TO_REAL, integerTerm);
			final Term rhs = ArithmeticRules.computePolyToReal(integerTerm);
			return new ProofLiteral[] { new ProofLiteral(theory.term(SMTLIBConstants.EQUALS, lhs, rhs), true) };
		}
		case ":" + ProofRules.DIVIDEDEF: {
			if (!theory.getLogic().hasReals()) {
				reportError("Proof requires real arithmetic");
				return getTrueClause(theory);
			}
			final Term[] divParams = (Term[]) annots[0].getValue();
			assert annots.length == 1;
			assert divParams.length >= 2;
			final Term divide = theory.term(SMTLIBConstants.DIVIDE, divParams);
			final Term[] mulParams = new Term[divParams.length];
			System.arraycopy(divParams, 1, mulParams, 0, divParams.length - 1);
			mulParams[divParams.length - 1] = divide;
			final Term lhs = theory.term(SMTLIBConstants.MUL, mulParams);
			final LinkedHashSet<ProofLiteral> clause = new LinkedHashSet<>();
			clause.add(new ProofLiteral(theory.term(SMTLIBConstants.EQUALS, lhs, divParams[0]), true));
			for (int i = 1; i < divParams.length; i++) {
				clause.add(new ProofLiteral(
						theory.term(SMTLIBConstants.EQUALS, divParams[i], Rational.ZERO.toTerm(divParams[i].getSort())),
						true));
			}
			return clause.toArray(new ProofLiteral[clause.size()]);
		}
		case ":" + ProofRules.TOINTLOW: {
			if (!theory.getLogic().isIRA()) {
				reportError("Proof requires integer and real arithmetic");
				return getTrueClause(theory);
			}
			final Term[] params = (Term[]) annots[0].getValue();
			assert annots.length == 1;
			assert params.length == 1;
			final Term arg = params[0];
			final Term toRealToInt = theory.term(SMTLIBConstants.TO_REAL, theory.term(SMTLIBConstants.TO_INT, arg));
			return new ProofLiteral[] { new ProofLiteral(theory.term(SMTLIBConstants.LEQ, toRealToInt, arg), true) };
		}
		case ":" + ProofRules.TOINTHIGH: {
			if (!theory.getLogic().isIRA()) {
				reportError("Proof requires integer and real arithmetic");
				return getTrueClause(theory);
			}
			final Term[] params = (Term[]) annots[0].getValue();
			assert annots.length == 1;
			assert params.length == 1;
			final Term arg = params[0];
			final Term toRealToInt = theory.term(SMTLIBConstants.TO_REAL, theory.term(SMTLIBConstants.TO_INT, arg));
			final Term toRealPlusOne = theory.term(SMTLIBConstants.PLUS, toRealToInt,
					Rational.ONE.toTerm(arg.getSort()));
			return new ProofLiteral[] { new ProofLiteral(theory.term(SMTLIBConstants.LT, arg, toRealPlusOne), true) };
		}
		case ":" + ProofRules.DIVLOW: {
			if (!theory.getLogic().hasIntegers() && !theory.getLogic().isBitVector()) {
				reportError("Proof requires integer arithmetic");
				return getTrueClause(theory);
			}
			final Term[] params = (Term[]) annots[0].getValue();
			assert annots.length == 1;
			assert params.length == 2;
			final Term arg = params[0];
			final Term divisor = params[1];
			final Term divTerm = theory.term(SMTLIBConstants.DIV, arg, divisor);
			final Term mulDivTerm = theory.term(SMTLIBConstants.MUL, divisor, divTerm);
			final Term zero = Rational.ZERO.toTerm(divisor.getSort());
			return new ProofLiteral[] { new ProofLiteral(theory.term(SMTLIBConstants.LEQ, mulDivTerm, arg), true),
					new ProofLiteral(theory.term(SMTLIBConstants.EQUALS, divisor, zero), true) };
		}
		case ":" + ProofRules.DIVHIGH: {
			if (!theory.getLogic().hasIntegers() && !theory.getLogic().isBitVector()) {
				reportError("Proof requires integer arithmetic");
				return getTrueClause(theory);
			}
			final Term[] params = (Term[]) annots[0].getValue();
			assert annots.length == 1;
			assert params.length == 2;
			final Term arg = params[0];
			final Term divisor = params[1];
			final Term divTerm = theory.term(SMTLIBConstants.DIV, arg, divisor);
			final Term mulDivTerm = theory.term(SMTLIBConstants.MUL, divisor, divTerm);
			final Term mulDivTermPlus = theory.term(SMTLIBConstants.PLUS, mulDivTerm,
					theory.term(SMTLIBConstants.ABS, divisor));
			final Term zero = Rational.ZERO.toTerm(divisor.getSort());
			return new ProofLiteral[] { new ProofLiteral(theory.term(SMTLIBConstants.LT, arg, mulDivTermPlus), true),
					new ProofLiteral(theory.term(SMTLIBConstants.EQUALS, divisor, zero), true) };
		}
		case ":" + ProofRules.MODDEF: {
			if (!theory.getLogic().hasIntegers() && !theory.getLogic().isBitVector()) {
				reportError("Proof requires integer arithmetic");
				return getTrueClause(theory);
			}
			final Term[] params = (Term[]) annots[0].getValue();
			assert annots.length == 1;
			assert params.length == 2;
			final Term arg = params[0];
			final Term divisor = params[1];
			final Term divTerm = theory.term(SMTLIBConstants.DIV, arg, divisor);
			final Term mulDivTerm = theory.term(SMTLIBConstants.MUL, divisor, divTerm);
			final Term modTerm = theory.term(SMTLIBConstants.MOD, arg, divisor);
			final Term modDef = theory.term(SMTLIBConstants.PLUS, mulDivTerm, modTerm);
			final Term zero = Rational.ZERO.toTerm(divisor.getSort());
			return new ProofLiteral[] { new ProofLiteral(theory.term(SMTLIBConstants.EQUALS, modDef, arg), true),
					new ProofLiteral(theory.term(SMTLIBConstants.EQUALS, divisor, zero), true) };
		}
		case ":" + ProofRules.SELECTSTORE1: {
			if (!theory.getLogic().isArray()) {
				reportError("Proof requires array theory");
				return getTrueClause(theory);
			}
			assert annots.length == 1;
			final Term[] params = (Term[]) annots[0].getValue();
			assert params.length == 3;

			// (= (select (store a i v) i) v)
			final Term store = theory.term(SMTLIBConstants.STORE, params[0], params[1], params[2]);
			final Term selectStore = theory.term(SMTLIBConstants.SELECT, store, params[1]);
			return new ProofLiteral[] {
					new ProofLiteral(theory.term(SMTLIBConstants.EQUALS, selectStore, params[2]), true) };
		}
		case ":" + ProofRules.SELECTSTORE2: {
			if (!theory.getLogic().isArray()) {
				reportError("Proof requires array theory");
				return getTrueClause(theory);
			}
			assert annots.length == 1;
			final Term[] params = (Term[]) annots[0].getValue();
			assert params.length == 4;

			// (= (select (store a i v) j) (select a j))
			final Term store = theory.term(SMTLIBConstants.STORE, params[0], params[1], params[2]);
			final Term selectStore = theory.term(SMTLIBConstants.SELECT, store, params[3]);
			final Term select = theory.term(SMTLIBConstants.SELECT, params[0], params[3]);
			return new ProofLiteral[] {
					new ProofLiteral(theory.term(SMTLIBConstants.EQUALS, selectStore, select), true),
					new ProofLiteral(theory.term(SMTLIBConstants.EQUALS, params[1], params[3]), true) };
		}
		case ":" + ProofRules.EXTDIFF: {
			if (!theory.getLogic().isArray()) {
				reportError("Proof requires array theory");
				return getTrueClause(theory);
			}
			assert annots.length == 1;
			final Term[] params = (Term[]) annots[0].getValue();
			assert params.length == 2;

			// (= a b), ~(= (select a (@diff a b)) (select b (@diff a b)))
			final Term diff = theory.term(SMTInterpolConstants.DIFF, params[0], params[1]);
			final Term select0 = theory.term(SMTLIBConstants.SELECT, params[0], diff);
			final Term select1 = theory.term(SMTLIBConstants.SELECT, params[1], diff);
			return new ProofLiteral[] {
					new ProofLiteral(theory.term(SMTLIBConstants.EQUALS, params[0], params[1]), true),
					new ProofLiteral(theory.term(SMTLIBConstants.EQUALS, select0, select1), false) };
		}
		case ":" + ProofRules.CONST: {
			if (!theory.getLogic().isArray()) {
				reportError("Proof requires array theory");
				return getTrueClause(theory);
			}
			assert annots.length == 1;
			final Term[] params = (Term[]) annots[0].getValue();
			assert params.length == 2;
			final Term value = params[0];
			final Term index = params[1];

			// (= (select (const value) index) value)
			final Sort arraySort = theory.getSort(SMTLIBConstants.ARRAY, index.getSort(), value.getSort());
			final Term constArray = theory.term(SMTLIBConstants.CONST, null, arraySort, value);
			final Term select = theory.term(SMTLIBConstants.SELECT, constArray, index);
			return new ProofLiteral[] { new ProofLiteral(theory.term(SMTLIBConstants.EQUALS, select, value), true) };
		}
		case ":" + ProofRules.DT_PROJECT: {
			if (!theory.getLogic().isDatatype()) {
				reportError("Proof requires data type theory");
				return getTrueClause(theory);
			}
			assert annots.length == 1;
			final Term[] params = (Term[]) annots[0].getValue();
			assert params.length == 1;
			final ApplicationTerm selConsTerm = (ApplicationTerm) params[0];
			final FunctionSymbol selector = selConsTerm.getFunction();
			assert selector.isSelector();
			final ApplicationTerm consTerm = (ApplicationTerm) selConsTerm.getParameters()[0];
			if (!consTerm.getFunction().isConstructor()) {
				return reportViolatedSideCondition(axiom);
			}
			final DataType dataType = (DataType) consTerm.getSort().getSortSymbol();
			final Constructor cons = dataType.getConstructor(consTerm.getFunction().getName());
			final int selectPos = cons.getSelectorIndex(selector.getName());
			final Term consArg = consTerm.getParameters()[selectPos];

			// + (= (seli (cons a1 ... an)) ai)
			final Term provedEq = theory.term(SMTLIBConstants.EQUALS, selConsTerm, consArg);
			return new ProofLiteral[] { new ProofLiteral(provedEq, true) };
		}
		case ":" + ProofRules.DT_CONS: {
			if (!theory.getLogic().isDatatype()) {
				reportError("Proof requires data type theory");
				return getTrueClause(theory);
			}
			assert annots.length == 1;
			final Term[] params = (Term[]) annots[0].getValue();
			assert params.length == 1;
			final ApplicationTerm isConsTerm = (ApplicationTerm) params[0];
			if (!isConsTerm.getFunction().getName().equals(SMTLIBConstants.IS)) {
				return reportViolatedSideCondition(axiom);
			}
			final Term dataTerm = isConsTerm.getParameters()[0];
			final DataType dataType = (DataType) dataTerm.getSort().getSortSymbol();
			final Constructor cons = dataType.getConstructor(isConsTerm.getFunction().getIndices()[0]);
			final String[] selectors = cons.getSelectors();
			final Term[] selectTerms = new Term[selectors.length];
			for (int i = 0; i < selectors.length; i++) {
				selectTerms[i] = theory.term(selectors[i], dataTerm);
			}
			final Term consTerm = theory.term(cons.getName(), null,
					(cons.needsReturnOverload() ? dataTerm.getSort() : null), selectTerms);

			// - ((_ is cons) u), + (= (cons (sel1 u) ... (seln u)) u)
			final Term provedEq = theory.term(SMTLIBConstants.EQUALS, consTerm, dataTerm);
			return new ProofLiteral[] { new ProofLiteral(isConsTerm, false), new ProofLiteral(provedEq, true) };
		}
		case ":" + ProofRules.DT_TESTI: {
			if (!theory.getLogic().isDatatype()) {
				reportError("Proof requires data type theory");
				return getTrueClause(theory);
			}
			assert annots.length == 1;
			final Term[] params = (Term[]) annots[0].getValue();
			assert params.length == 1;
			final ApplicationTerm consTerm = (ApplicationTerm) params[0];
			final FunctionSymbol consFunc = consTerm.getFunction();
			if (!consFunc.isConstructor()) {
				return reportViolatedSideCondition(axiom);
			}
			final Term isTerm = theory.term(SMTLIBConstants.IS, new String[] { consFunc.getName() }, null, consTerm);

			// + ((_ is cons) (cons a1 ... an))
			return new ProofLiteral[] { new ProofLiteral(isTerm, true) };
		}
		case ":" + ProofRules.DT_TESTE: {
			if (!theory.getLogic().isDatatype()) {
				reportError("Proof requires data type theory");
				return getTrueClause(theory);
			}
			assert annots.length == 1;
			final Object[] params = (Object[]) annots[0].getValue();
			assert params.length == 2;
			final String otherCons = (String) params[0];
			final ApplicationTerm consTerm = (ApplicationTerm) params[1];
			final FunctionSymbol consFunc = consTerm.getFunction();
			if (!consFunc.isConstructor() || consFunc.getName().equals(otherCons)) {
				return reportViolatedSideCondition(axiom);
			}
			final Term isTerm = theory.term(SMTLIBConstants.IS, new String[] { otherCons }, null, consTerm);

			// + ((_ is otherCons) (cons a1 ... an))
			return new ProofLiteral[] { new ProofLiteral(isTerm, false) };
		}
		case ":" + ProofRules.DT_EXHAUST: {
			if (!theory.getLogic().isDatatype()) {
				reportError("Proof requires data type theory");
				return getTrueClause(theory);
			}
			assert annots.length == 1;
			final Term[] params = (Term[]) annots[0].getValue();
			assert params.length == 1;
			final Term data = params[0];
			final DataType dataType = (DataType) data.getSort().getSortSymbol();
			final Constructor[] constrs = dataType.getConstructors();
			// + ((_ is cons0) data) ... + ((_ is consn) data)
			final ProofLiteral[] lits = new ProofLiteral[constrs.length];
			for (int i = 0; i < lits.length; i++) {
				final Term tester = theory.term(SMTLIBConstants.IS, new String[] { constrs[i].getName() }, null, data);
				lits[i] = new ProofLiteral(tester, true);
			}
			return lits;
		}
		case ":" + ProofRules.DT_ACYCLIC: {
			if (!theory.getLogic().isDatatype()) {
				reportError("Proof requires data type theory");
				return getTrueClause(theory);
			}
			assert annots.length == 1;
			final Object[] params = (Object[]) annots[0].getValue();
			assert params.length == 2;
			final Term consTerm = (Term) params[0];
			final int[] positions = (int[]) params[1];
			if (positions.length == 0) {
				return reportViolatedSideCondition(axiom);
			}
			Term subTerm = consTerm;
			for (final int pos : positions) {
				final ApplicationTerm parent = (ApplicationTerm) subTerm;
				if (!parent.getFunction().isConstructor()) {
					return reportViolatedSideCondition(axiom);
				}
				subTerm = parent.getParameters()[pos];
			}
			final Term provedIneq = theory.term(SMTLIBConstants.EQUALS, consTerm, subTerm);
			return new ProofLiteral[] { new ProofLiteral(provedIneq, false) };
		}
		case ":" + ProofRules.DT_MATCH: {
			if (!theory.getLogic().isDatatype()) {
				reportError("Proof requires data type theory");
				return getTrueClause(theory);
			}
			assert annots.length == 1;
			final Term[] params = (Term[]) annots[0].getValue();
			assert params.length == 1;
			if (!(params[0] instanceof MatchTerm)) {
				return reportViolatedSideCondition(axiom);
			}
			final MatchTerm matchTerm = (MatchTerm) params[0];
			final Term iteTerm = buildIteForMatch(matchTerm);

			final Term provedEq = theory.term(SMTLIBConstants.EQUALS, matchTerm, iteTerm);
			return new ProofLiteral[] { new ProofLiteral(provedEq, true) };
		}
		case ":" + ProofRules.BVCONST: {
			if (!theory.getLogic().isBitVector()) {
				reportError("Proof requires bit vector theory");
				return getTrueClause(theory);
			}
			assert annots.length == 1;
			final Object[] ruleParams = (Object[]) annots[0].getValue();
			assert ruleParams.length == 2;
			final Term natTerm = (Term) ruleParams[0];
			if (!natTerm.getSort().isInternal() || !natTerm.getSort().getName().equals("Int")
					|| !(natTerm instanceof ConstantTerm)
					|| !(((ConstantTerm) natTerm).getValue() instanceof Rational)) {
				reportError("Expected constant integer argument");
				return getTrueClause(theory);
			}
			final Rational constRational = (Rational) ((ConstantTerm) natTerm).getValue();
			final BigInteger constValue = constRational.numerator();
			final Integer bitLengthInt = (Integer) ruleParams[1];
			final String bitLength = bitLengthInt.toString();
			if (!constRational.denominator().equals(BigInteger.ONE) || constValue.signum() < 0
					|| constValue.bitLength() > bitLengthInt) {
				reportError("Constant integer argument out of range");
				return getTrueClause(theory);
			}
			final Term bvTerm = theory.term("bv" + constValue.toString(), new String[] { bitLength }, null);
			final Term int2bvTerm = theory.term(SMTLIBConstants.INT_TO_BV, new String[] { bitLength }, null, natTerm);
			final Term provedEq = theory.term(SMTLIBConstants.EQUALS, bvTerm, int2bvTerm);
			return new ProofLiteral[] { new ProofLiteral(provedEq, true) };
		}
		case ":" + ProofRules.BVLITERAL: {
			if (!theory.getLogic().isBitVector()) {
				reportError("Proof requires bit vector theory");
				return getTrueClause(theory);
			}
			assert annots.length == 1;
			final Object[] ruleParams = (Object[]) annots[0].getValue();
			assert ruleParams.length == 1;
			final Term litTerm = (Term) ruleParams[0];
			if (!litTerm.getSort().isInternal() || !litTerm.getSort().getName().equals(SMTLIBConstants.BITVEC)
					|| !(litTerm instanceof ConstantTerm) || !(((ConstantTerm) litTerm).getValue() instanceof String)) {
				reportError("Expected literal argument");
				return getTrueClause(theory);
			}
			final String litValue = (String) ((ConstantTerm) litTerm).getValue();
			int bitLengthInt;
			BigInteger constValue;
			if (litValue.matches("#b[01]+")) {
				constValue = new BigInteger(litValue.substring(2), 2);
				bitLengthInt = litValue.length() - 2;
			} else if (litValue.matches("#x[0-9a-fA-F]+")) {
				constValue = new BigInteger(litValue.substring(2), 16);
				bitLengthInt = 4 * (litValue.length() - 2);
			} else {
				reportError("Expected bit-vector literal");
				return getTrueClause(theory);
			}
			final Term constTerm = Rational.valueOf(constValue, BigInteger.ONE).toTerm(theory.getNumericSort());
			final Term int2bvTerm = theory.term(SMTLIBConstants.INT_TO_BV,
					new String[] { String.valueOf(bitLengthInt) }, null, constTerm);
			final Term provedEq = theory.term(SMTLIBConstants.EQUALS, litTerm, int2bvTerm);
			return new ProofLiteral[] { new ProofLiteral(provedEq, true) };
		}
		case ":" + ProofRules.INT2UBV2INT: {
			if (!theory.getLogic().isBitVector()) {
				reportError("Proof requires bit vector theory");
				return getTrueClause(theory);
			}
			assert annots.length == 1;
			final Object[] ruleParams = (Object[]) annots[0].getValue();
			assert ruleParams.length == 2;
			final Term natTerm = (Term) ruleParams[1];
			if (!natTerm.getSort().isInternal() || !natTerm.getSort().getName().equals("Int")) {
				reportError("Expected integer argument");
				return getTrueClause(natTerm.getTheory());
			}
			final int bl = (Integer) ruleParams[0];
			final String bitLength = Integer.toString(bl);
			final Term nat2bv2nat = theory.term(SMTLIBConstants.UBV_TO_INT,
					theory.term(SMTLIBConstants.INT_TO_BV, new String[] { bitLength }, null, natTerm));
			final BigInteger pow2 = BigInteger.ONE.shiftLeft(bl);
			final Term pow2Term = theory.constant(Rational.valueOf(pow2, BigInteger.ONE), theory.getNumericSort());
			final Term modTerm = theory.term(SMTLIBConstants.MOD, natTerm, pow2Term);
			final Term provedEq = theory.term(SMTLIBConstants.EQUALS, nat2bv2nat, modTerm);
			return new ProofLiteral[] { new ProofLiteral(provedEq, true) };
		}
		case ":" + ProofRules.INT2SBV2INT: {
			if (!theory.getLogic().isBitVector()) {
				reportError("Proof requires bit vector theory");
				return getTrueClause(theory);
			}
			assert annots.length == 1;
			final Object[] ruleParams = (Object[]) annots[0].getValue();
			assert ruleParams.length == 2;
			final Term natTerm = (Term) ruleParams[1];
			if (!natTerm.getSort().isInternal() || !natTerm.getSort().getName().equals("Int")) {
				reportError("Expected integer argument");
				return getTrueClause(natTerm.getTheory());
			}
			final Sort intSort = natTerm.getSort();
			final int bl = (Integer) ruleParams[0];
			final String bitLength = Integer.toString(bl);
			final Term nat2bv2nat = theory.term(SMTLIBConstants.SBV_TO_INT,
					theory.term(SMTLIBConstants.INT_TO_BV, new String[] { bitLength }, null, natTerm));
			final Rational pow2 = Rational.valueOf(BigInteger.ONE.shiftLeft(bl), BigInteger.ONE);
			final Rational pow2sign = Rational.valueOf(BigInteger.ONE.shiftLeft(bl - 1), BigInteger.ONE);
			final Term shiftTerm = theory.term(SMTLIBConstants.PLUS, natTerm, pow2sign.toTerm(intSort));
			final Term modTerm = theory.term(SMTLIBConstants.MOD, shiftTerm, pow2.toTerm(intSort));
			final Term resultTerm = theory.term(SMTLIBConstants.PLUS, modTerm, pow2sign.negate().toTerm(intSort));
			final Term provedEq = theory.term(SMTLIBConstants.EQUALS, nat2bv2nat, resultTerm);
			return new ProofLiteral[] { new ProofLiteral(provedEq, true) };
		}
		case ":" + ProofRules.UBV2INT2BV: {
			if (!theory.getLogic().isBitVector()) {
				reportError("Proof requires bit vector theory");
				return getTrueClause(theory);
			}
			assert annots.length == 1;
			final Object[] ruleParams = (Object[]) annots[0].getValue();
			assert ruleParams.length == 1;
			final Term bvTerm = (Term) ruleParams[0];
			assert bvTerm.getSort().isBitVecSort();
			final String[] bitLength = bvTerm.getSort().getIndices();
			final Term bv2int2bv = theory.term(SMTLIBConstants.INT_TO_BV, bitLength, null,
					theory.term(SMTLIBConstants.UBV_TO_INT, bvTerm));
			final Term provedEq = theory.term(SMTLIBConstants.EQUALS, bv2int2bv, bvTerm);
			return new ProofLiteral[] { new ProofLiteral(provedEq, true) };
		}
		default:
			reportError("Unknown axiom %s", axiom);
			return getTrueClause(axiom.getTheory());
		}
	}

	private ProofLiteral[] reportViolatedSideCondition(final Term axiom) {
		final StringBuilder sb = new StringBuilder();
		sb.append("Side-condition violated in ");
		ProofRules.printProof(sb, axiom);
		reportError(sb.toString());
		return getTrueClause(axiom.getTheory());
	}

	/**
	 * Dummy clause (+ true) that is created for axioms whose side-condition is not
	 * valid.
	 *
	 * @return a dummy clause that doesn't proof anything (but is valid).
	 */
	private ProofLiteral[] getTrueClause(final Theory theory) {
		return new ProofLiteral[] { new ProofLiteral(theory.mTrue, true) };
	}

	private static Term buildLetForMatch(final Constructor constr, final TermVariable[] vars, final Term dataTerm,
			final Term caseTerm) {
		final Theory theory = dataTerm.getTheory();
		final Term[] selectTerms = new Term[vars.length];
		if (constr == null) {
			assert vars.length == 1;
			selectTerms[0] = dataTerm;
		} else {
			assert constr.getSelectors().length == vars.length;
			for (int i = 0; i < vars.length; i++) {
				selectTerms[i] = theory.term(constr.getSelectors()[i], dataTerm);
			}
		}
		return new FormulaUnLet().unlet(theory.let(vars, selectTerms, caseTerm));
	}

	public static Term buildIteForMatch(final MatchTerm matchTerm) {
		final Theory theory = matchTerm.getTheory();
		final Term dataTerm = matchTerm.getDataTerm();
		final Term[] cases = matchTerm.getCases();
		final TermVariable[][] vars = matchTerm.getVariables();
		final Constructor[] constrs = matchTerm.getConstructors();

		Term iteTerm;
		iteTerm = buildLetForMatch(constrs[constrs.length - 1], vars[constrs.length - 1], dataTerm,
				cases[constrs.length - 1]);
		for (int i = constrs.length - 2; i >= 0; i--) {
			final Term caseTerm = buildLetForMatch(constrs[i], vars[i], dataTerm, cases[i]);
			if (constrs[i] == null) {
				// SMT-LIB standard allows the default case in the middle, with the semantics
				// that
				// all following cases are redundant.
				iteTerm = caseTerm;
			} else {
				final Term condTerm = theory.term(SMTLIBConstants.IS, new String[] { constrs[i].getName() }, null,
						dataTerm);
				iteTerm = theory.term(SMTLIBConstants.ITE, condTerm, caseTerm, iteTerm);
			}
		}
		return iteTerm;
	}

	public ProofLiteral[] checkAssert(final Term axiom) {
		mNumAssertions++;
		final ApplicationTerm appTerm = (ApplicationTerm) axiom;
		final Term[] params = appTerm.getParameters();
		assert appTerm.getFunction().getName() == ProofRules.PREFIX + ProofRules.ASSUME;
		assert params.length == 1;
		if (!mAssertions.contains(params[0])) {
			reportError("Unknown assumption: %s", params[0]);
			return getTrueClause(axiom.getTheory());
		}
		return new ProofLiteral[] { new ProofLiteral(params[0], true) };
	}

	/**
	 * The main proof walker that handles a term of sort {@literal @}Proof. It just
	 * calls the walk function.
	 */
	static class ProofWalker implements Walker {
		final Term mTerm;

		public ProofWalker(final Term term) {
			assert term.getSort().getName().equals(ProofRules.PREFIX + ProofRules.PROOF);
			mTerm = term;
		}

		@Override
		public void walk(final NonRecursive engine) {
			((MinimalProofChecker) engine).walk(mTerm);
		}
	}

	/**
	 * The proof walker that handles define-fun.
	 */
	static class DefineFunWalker implements Walker {
		final AnnotatedTerm mProof;

		public DefineFunWalker(final AnnotatedTerm term) {
			mProof = term;
		}

		public void enqueue(final MinimalProofChecker engine) {
			engine.mNumDefineFun++;
			final Object[] annotValues = (Object[]) mProof.getAnnotations()[0].getValue();
			final FunctionSymbol func = (FunctionSymbol) annotValues[0];
			final Term def = (Term) annotValues[1];
			if (def instanceof LambdaTerm) {
				final LambdaTerm lambda = (LambdaTerm) def;
				engine.checkFunctionConsistency(func, lambda.getVariables(), lambda.getSubterm());
			} else {
				engine.checkFunctionConsistency(func, new TermVariable[0], def);
			}
			if (engine.mFunctionDefinitions.containsKey(func)) {
				throw new AssertionError("Double function definition.");
			}
			engine.mFunctionDefinitions.put(func, def);
			engine.enqueueWalker(this);
			engine.enqueueWalker(new ProofWalker(mProof.getSubterm()));
		}

		@Override
		public void walk(final NonRecursive parent) {
			final MinimalProofChecker engine = (MinimalProofChecker) parent;
			final Object[] annotValues = (Object[]) mProof.getAnnotations()[0].getValue();
			final FunctionSymbol func = (FunctionSymbol) annotValues[0];
			engine.mFunctionDefinitions.remove(func);
		}
	}

	/**
	 * The proof walker that handles the resolution rule after its arguments are
	 * converted. It just calls the walkResolution function.
	 */
	static class ResolutionWalker implements Walker {
		final ApplicationTerm mTerm;

		public ResolutionWalker(final ApplicationTerm term) {
			mTerm = term;
		}

		public void enqueue(final MinimalProofChecker engine) {
			final Term[] params = mTerm.getParameters();
			engine.enqueueWalker(this);
			engine.enqueueWalker(new ProofWalker(params[2]));
			engine.enqueueWalker(new ProofWalker(params[1]));
		}

		@Override
		public void walk(final NonRecursive engine) {
			final MinimalProofChecker checker = (MinimalProofChecker) engine;
			final ProofLiteral[] negClause = checker.stackPop();
			final ProofLiteral[] posClause = checker.stackPop();
			checker.stackPush(checker.walkResolution(mTerm, posClause, negClause), mTerm);
		}
	}

	static class FunctionSplit {
		FunctionSymbol mFunc;
		Term[] mParams;

		public FunctionSplit(FunctionSymbol func, Term[] params) {
			mFunc = func;
			mParams = params;
		}
	}

	static interface Expander {
		public Term expand(FunctionSymbol f, Term[] args);
	}
}
