/*
 * Copyright (C) 2009-2012 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.smtinterpol.convert;

import java.math.BigInteger;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.logic.AnnotatedTerm;
import de.uni_freiburg.informatik.ultimate.logic.Annotation;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.ConstantTerm;
import de.uni_freiburg.informatik.ultimate.logic.FormulaUnLet;
import de.uni_freiburg.informatik.ultimate.logic.FunctionSymbol;
import de.uni_freiburg.informatik.ultimate.logic.MatchTerm;
import de.uni_freiburg.informatik.ultimate.logic.NonRecursive;
import de.uni_freiburg.informatik.ultimate.logic.QuantifiedFormula;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.SMTLIBConstants;
import de.uni_freiburg.informatik.ultimate.logic.SMTLIBException;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermTransformer;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.logic.Theory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.interpolate.Interpolator;
import de.uni_freiburg.informatik.ultimate.smtinterpol.option.SMTInterpolConstants;
import de.uni_freiburg.informatik.ultimate.smtinterpol.proof.IProofTracker;
import de.uni_freiburg.informatik.ultimate.smtinterpol.proof.ProofConstants;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.bitvector.BvToIntUtils;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.bitvector.BvUtils;
import de.uni_freiburg.informatik.ultimate.smtinterpol.util.Polynomial;
import de.uni_freiburg.informatik.ultimate.util.datastructures.UnifyHash;

/**
 * Build a representation of the formula where only not, or, ite and =/2 are
 * present. Linear arithmetic terms are converted into Polynomials. We normalize
 * quantifiers to universal quantifiers. Additionally, this term transformer
 * removes all annotations from the formula.
 *
 * @author Jochen Hoenicke, Juergen Christ
 */
public class TermCompiler extends TermTransformer {

	private Map<Term, Set<String>> mNames;
	UnifyHash<Term> mCanonicalPolys = new UnifyHash<>();

	private IProofTracker mTracker;
	private LogicSimplifier mUtils;
	private final static String BITVEC_CONST_PATTERN = "bv\\d+";
	// TODO make it an option
	boolean mEagerMod = true;

	static class TransitivityStep implements Walker {
		final Term mFirst;

		public TransitivityStep(final Term first) {
			mFirst = first;
		}

		@Override
		public void walk(final NonRecursive engine) {
			final TermCompiler compiler = (TermCompiler) engine;
			final Term second = compiler.getConverted();
			compiler.setResult(compiler.mTracker.transitivity(mFirst, second));
		}
	}

	public void setProofTracker(final IProofTracker tracker) {
		mTracker = tracker;
		mUtils = new LogicSimplifier(tracker);
	}

	public void setAssignmentProduction(final boolean on) {
		if (on) {
			mNames = new HashMap<>();
		} else {
			mNames = null;
		}
	}

	public Map<Term, Set<String>> getNames() {
		return mNames;
	}

	@Override
	public void convert(final Term term) {
		if (term.getSort().isInternal()) {
			/* check if we support the internal sort */
			switch (term.getSort().getName()) {
			case "Bool":
			case "Int":
			case "Real":
			case "Array":
			case "BitVec":
				/* okay */
				break;
			default:
				throw new UnsupportedOperationException("Unsupported internal sort: " + term.getSort());
			}
		}
		if (term instanceof ApplicationTerm) {
			final ApplicationTerm appTerm = (ApplicationTerm) term;
			final FunctionSymbol fsym = appTerm.getFunction();
			// TODO: The following is commented out because of the lambdas in
			// QuantifierTheory
			// if (fsym.isModelValue()) {
			// throw new SMTLIBException("Model values not allowed in input");
			// }
			final Term[] params = appTerm.getParameters();
			if (fsym.isLeftAssoc() && params.length > 2) {
				final Theory theory = appTerm.getTheory();
				final String fsymName = fsym.getName();
				if (fsymName == "and" || fsymName == "or" || fsymName == "+" || fsymName == "-" || fsymName == "*") {
					// We keep some n-ary internal operators
					enqueueWalker(new BuildApplicationTerm(appTerm));
					pushTerms(params);
					return;
				}
				Term rhs = params[0];
				for (int i = 1; i < params.length; i++) {
					rhs = theory.term(fsym, rhs, params[i]);
				}
				final Term rewrite = mTracker.buildRewrite(appTerm, rhs, ProofConstants.RW_EXPAND);
				enqueueWalker(new TransitivityStep(rewrite));
				for (int i = params.length - 1; i > 0; i--) {
					final ApplicationTerm binAppTerm = (ApplicationTerm) rhs;
					enqueueWalker(new BuildApplicationTerm(binAppTerm));
					pushTerm(binAppTerm.getParameters()[1]);
					rhs = binAppTerm.getParameters()[0];
				}
				pushTerm(params[0]);
				return;
			}
			if (fsym.isRightAssoc() && params.length > 2) {
				final Theory theory = appTerm.getTheory();
				if (fsym == theory.mImplies) {
					// We keep n-ary implies
					enqueueWalker(new BuildApplicationTerm(appTerm));
					pushTerms(params);
					return;
				}
				Term rhs = params[params.length - 1];
				for (int i = params.length - 2; i >= 0; i--) {
					rhs = theory.term(fsym, params[i], rhs);
				}
				final Term rewrite = mTracker.buildRewrite(appTerm, rhs, ProofConstants.RW_EXPAND);
				enqueueWalker(new TransitivityStep(rewrite));
				for (int i = params.length - 1; i > 0; i--) {
					final ApplicationTerm binAppTerm = (ApplicationTerm) rhs;
					enqueueWalker(new BuildApplicationTerm(binAppTerm));
					rhs = binAppTerm.getParameters()[1];
				}
				pushTerms(params);
				return;
			}
			if (fsym.isChainable() && params.length > 2 && !fsym.getName().equals("=")) {
				final Theory theory = appTerm.getTheory();
				final Term[] conjs = new Term[params.length - 1];
				for (int i = 0; i < params.length - 1; i++) {
					conjs[i] = theory.term(fsym, params[i], params[i + 1]);
				}
				final Term rhs = theory.term("and", conjs);
				final Term rewrite = mTracker.buildRewrite(appTerm, rhs, ProofConstants.RW_EXPAND);
				enqueueWalker(new TransitivityStep(rewrite));
				enqueueWalker(new BuildApplicationTerm((ApplicationTerm) rhs));
				pushTerms(conjs);
				return;
			}
			if(term.getSort().isBitVecSort() && appTerm.getParameters().length == 0 && !fsym.isIntern()) {
//				final Theory theory = appTerm.getTheory();
//				final BvToIntUtils bvToIntUtils = new BvToIntUtils(theory, mUtils);
//				final Term rhs = bvToIntUtils.bv2nat(appTerm, mEagerMod);
//				final Term rewrite = mTracker.buildRewrite(appTerm, rhs, ProofConstants.RW_BVTOINT_CONST);
//				setResult(rewrite);
//				return;
				//TODO we just do nothing here?
			}
		} else if (term instanceof ConstantTerm && term.getSort().isNumericSort()) {
			final Term res = SMTAffineTerm.convertConstant((ConstantTerm) term).toTerm(term.getSort());
			setResult(mTracker.buildRewrite(term, res, ProofConstants.RW_CANONICAL_SUM));
			return;
		} else if (term instanceof ConstantTerm && term.getSort().isBitVecSort()) {
			final Theory theory = term.getTheory();
			final BvUtils bvUtils = new BvUtils(theory, mUtils);
			final BvToIntUtils bvToIntUtils = new BvToIntUtils(theory, mUtils, bvUtils);
			setResult(bvToIntUtils.translateBvConstantTerm((ConstantTerm) term, mEagerMod));
			return;
		} else if (term instanceof TermVariable) {
			if (term.getSort().isBitVecSort()) {
				final Theory theory = term.getTheory();
				final BvToIntUtils bvToIntUtils = new BvToIntUtils(theory, mUtils, null);
				setResult(bvToIntUtils.translateTermVariable((TermVariable) term, mEagerMod));
			} else {
				setResult(mTracker.reflexivity(term));
				return;
			}
		}
		super.convert(term);
	}

	@Override
	public void convertApplicationTerm(final ApplicationTerm appTerm, final Term[] args) {
		final FunctionSymbol fsym = appTerm.getFunction();
		final Theory theory = appTerm.getTheory();
		final BvUtils bvUtils = new BvUtils(theory, mUtils);
		final BvToIntUtils bvToIntUtils = new BvToIntUtils(theory, mUtils, bvUtils);

		Term convertedApp = mTracker.congruence(mTracker.reflexivity(appTerm), args);
		if (mTracker.getProvedTerm(convertedApp) instanceof ConstantTerm) {
			setResult(convertedApp);
			return;
		}

		final Term[] params = ((ApplicationTerm) mTracker.getProvedTerm(convertedApp)).getParameters();

		if (fsym.getDefinition() != null && !fsym.getName().startsWith("@skolem.")
				&& !fsym.getName().startsWith("@AUX")) {
			final HashMap<TermVariable, Term> substs = new HashMap<>();
			for (int i = 0; i < params.length; i++) {
				substs.put(fsym.getDefinitionVars()[i], params[i]);
			}
			final FormulaUnLet unletter = new FormulaUnLet();
			unletter.addSubstitutions(substs);
			final Term expanded = unletter.unlet(fsym.getDefinition());
			final Term expandedProof = mTracker.buildRewrite(mTracker.getProvedTerm(convertedApp), expanded,
					ProofConstants.RW_EXPAND_DEF);
			enqueueWalker(new TransitivityStep(mTracker.transitivity(convertedApp, expandedProof)));
			pushTerm(expanded);
			return;
		}

		if (fsym.isIntern()) {
			if (fsym.getName().matches(BITVEC_CONST_PATTERN)) {
				setResult(bvToIntUtils.translateBvConstant(fsym, convertedApp, mEagerMod));
				return;
			}
			switch (fsym.getName()) {
			case "not":
				setResult(mUtils.convertNot(convertedApp));
				return;
			case "and":
				setResult(mUtils.convertAnd(convertedApp));
				return;
			case "or":
				setResult(mUtils.convertOr(convertedApp));
				return;
			case "xor":
				setResult(mUtils.convertXor(convertedApp));
				return;
			case "=>":
				setResult(mUtils.convertImplies(convertedApp));
				return;
			case "ite":
				setResult(mUtils.convertIte(convertedApp));
				return;
			case "=":
				if (params[0].getSort().isBitVecSort()) {
					pushTerm(bvToIntUtils.translateRelations(mTracker, appTerm, convertedApp, true)); 
					//TODO setResult or PushTerm? see other bv relations too
					//VLT wegen nested eq
					return;
				}
				setResult(mUtils.convertEq(convertedApp));
				return;
			case "distinct":
				if (params[0].getSort().isBitVecSort()) {
					pushTerm(bvToIntUtils.translateRelations(mTracker, appTerm, convertedApp, true)); 
					//TODO setResult or PushTerm? see other bv relations too
					//VLT wegen nested eq
					return;
				}
				setResult(mUtils.convertDistinct(convertedApp));
				return;
			case "<=": {
				final Term lhs = mTracker.getProvedTerm(convertedApp);
				final Sort sort = params[0].getSort();
				final Polynomial poly = new Polynomial(params[0]);
				poly.add(Rational.MONE, params[1]);
				final Term rhs = theory.term("<=", unifyPolynomial(poly, sort), Rational.ZERO.toTerm(sort));
				final Term rewrite = mTracker.buildRewrite(lhs, rhs, ProofConstants.RW_LEQ_TO_LEQ0);
				setResult(mUtils.convertLeq0(mTracker.transitivity(convertedApp, rewrite)));
				return;
			}
			case ">=": {
				final Term lhs = mTracker.getProvedTerm(convertedApp);
				final Sort sort = params[0].getSort();
				final Polynomial poly = new Polynomial(params[1]);
				poly.add(Rational.MONE, params[0]);
				final Term rhs = theory.term("<=", unifyPolynomial(poly, sort), Rational.ZERO.toTerm(sort));
				final Term rewrite = mTracker.buildRewrite(lhs, rhs, ProofConstants.RW_GEQ_TO_LEQ0);
				setResult(mUtils.convertLeq0(mTracker.transitivity(convertedApp, rewrite)));
				return;
			}
			case ">": {
				final Term lhs = mTracker.getProvedTerm(convertedApp);
				final Sort sort = params[0].getSort();
				final Polynomial poly = new Polynomial(params[0]);
				poly.add(Rational.MONE, params[1]);
				final Term leq = theory.term("<=", unifyPolynomial(poly, sort), Rational.ZERO.toTerm(sort));
				final Term rhs = theory.term("not", leq);
				Term rewrite = mTracker.buildRewrite(lhs, rhs, ProofConstants.RW_GT_TO_LEQ0);
				final Term leqRewrite = mUtils.convertLeq0(mTracker.reflexivity(leq));
				rewrite = mTracker.congruence(mTracker.transitivity(convertedApp, rewrite), new Term[] { leqRewrite });
				setResult(mUtils.convertNot(rewrite));
				return;
			}
			case "<": {
				final Term lhs = mTracker.getProvedTerm(convertedApp);
				final Sort sort = params[0].getSort();
				final Polynomial poly = new Polynomial(params[1]);
				poly.add(Rational.MONE, params[0]);
				final Term leq = theory.term("<=", unifyPolynomial(poly, sort), Rational.ZERO.toTerm(sort));
				final Term rhs = theory.term("not", leq);
				Term rewrite = mTracker.buildRewrite(lhs, rhs, ProofConstants.RW_LT_TO_LEQ0);
				final Term leqRewrite = mUtils.convertLeq0(mTracker.reflexivity(leq));
				rewrite = mTracker.congruence(mTracker.transitivity(convertedApp, rewrite), new Term[] { leqRewrite });
				setResult(mUtils.convertNot(rewrite));
				return;
			}
			case "+": {
				final Term lhs = mTracker.getProvedTerm(convertedApp);
				final Polynomial poly = new Polynomial(params[0]);
				for (int i = 1; i < params.length; i++) {
					poly.add(Rational.ONE, new Polynomial(params[i]));
				}
				final Term rhs = unifyPolynomial(poly, convertedApp.getSort());
				final Term rewrite = mTracker.buildRewrite(lhs, rhs, ProofConstants.RW_CANONICAL_SUM);
				setResult(mTracker.transitivity(convertedApp, rewrite));
				return;
			}
			case "-": {
				final Term lhs = mTracker.getProvedTerm(convertedApp);
				final Polynomial result = new Polynomial(params[0]);
				if (params.length == 1) {
					result.mul(Rational.MONE);
				} else {
					for (int i = 1; i < params.length; i++) {
						result.add(Rational.MONE, params[i]);
					}
				}
				final Term rhs = unifyPolynomial(result, convertedApp.getSort());
				final Term rewrite = mTracker.buildRewrite(lhs, rhs, ProofConstants.RW_CANONICAL_SUM);
				setResult(mTracker.transitivity(convertedApp, rewrite));
				return;
			}
			case "*": {
				final Term lhs = mTracker.getProvedTerm(convertedApp);
				final Polynomial prod = new Polynomial(params[0]);
				for (int i = 1; i < params.length; i++) {
					prod.mul(new Polynomial(params[i]));
				}
				final Term rhs = unifyPolynomial(prod, convertedApp.getSort());
				final Term rewrite = mTracker.buildRewrite(lhs, rhs, ProofConstants.RW_CANONICAL_SUM);
				setResult(mTracker.transitivity(convertedApp, rewrite));
				return;
			}
			case "/": {
				final Term lhs = mTracker.getProvedTerm(convertedApp);
				final Polynomial arg0 = new Polynomial(params[0]);
				if (params[1] instanceof ConstantTerm) {
					final Rational arg1 = SMTAffineTerm.convertConstant((ConstantTerm) params[1]);
					if (arg1.equals(Rational.ZERO)) {
						setResult(convertedApp);
					} else {
						arg0.mul(arg1.inverse());
						final Term rhs = unifyPolynomial(arg0, convertedApp.getSort());
						final Term rewrite = mTracker.buildRewrite(lhs, rhs, ProofConstants.RW_CANONICAL_SUM);
						setResult(mTracker.transitivity(convertedApp, rewrite));
					}
					return;
				} else {
					setResult(convertedApp);
					return;
				}
			}
			case "div": {
				final Term lhs = mTracker.getProvedTerm(convertedApp);
				final Polynomial arg0 = new Polynomial(params[0]);
				if (params[1] instanceof ConstantTerm) {
					final Rational divisor = (Rational) ((ConstantTerm) params[1]).getValue();
					assert divisor.isIntegral();
					if (divisor.equals(Rational.ONE)) {
						final Term rhs = unifyPolynomial(arg0, convertedApp.getSort());
						final Term rewrite = mTracker.buildRewrite(lhs, rhs, ProofConstants.RW_DIV_ONE);
						setResult(mTracker.transitivity(convertedApp, rewrite));
					} else if (divisor.equals(Rational.MONE)) {
						arg0.mul(Rational.MONE);
						final Term rhs = unifyPolynomial(arg0, convertedApp.getSort());
						final Term rewrite = mTracker.buildRewrite(lhs, rhs, ProofConstants.RW_DIV_MONE);
						setResult(mTracker.transitivity(convertedApp, rewrite));
					} else if (arg0.isConstant() && !divisor.equals(Rational.ZERO)) {
						// We have (div c0 c1) ==> constDiv(c0, c1)
						final Rational div = constDiv(arg0.getConstant(), divisor);
						final Term rhs = div.toTerm(convertedApp.getSort());
						final Term rewrite = mTracker.buildRewrite(lhs, rhs, ProofConstants.RW_DIV_CONST);
						setResult(mTracker.transitivity(convertedApp, rewrite));
					} else {
						setResult(convertedApp);
					}
					return;
				} else {
					setResult(convertedApp);
					return;
				}
			}
			case "mod": {
				final Term lhs = mTracker.getProvedTerm(convertedApp);
				final Polynomial arg0 = new Polynomial(params[0]);
				if (params[1] instanceof ConstantTerm) {
					final Rational divisor = (Rational) ((ConstantTerm) params[1]).getValue();
					assert divisor.isIntegral();
					if (divisor.equals(Rational.ZERO)) {
						setResult(convertedApp);
					} else if (divisor.equals(Rational.ONE)) {
						// (mod x 1) == 0
						final Term rhs = Rational.ZERO.toTerm(convertedApp.getSort());
						final Term rewrite = mTracker.buildRewrite(lhs, rhs, ProofConstants.RW_MODULO_ONE);
						setResult(mTracker.transitivity(convertedApp, rewrite));
					} else if (divisor.equals(Rational.MONE)) {
						// (mod x -1) == 0
						final Term rhs = Rational.ZERO.toTerm(convertedApp.getSort());
						final Term rewrite = mTracker.buildRewrite(lhs, rhs, ProofConstants.RW_MODULO_MONE);
						setResult(mTracker.transitivity(convertedApp, rewrite));
					} else if (arg0.isConstant()) {
						// We have (mod c0 c1) ==> c0 - c1 * constDiv(c0, c1)
						final Rational c0 = arg0.getConstant();
						final Rational mod = c0.sub(constDiv(c0, divisor).mul(divisor));
						final Term rhs = mod.toTerm(convertedApp.getSort());
						final Term rewrite = mTracker.buildRewrite(lhs, rhs, ProofConstants.RW_MODULO_CONST);
						setResult(mTracker.transitivity(convertedApp, rewrite));
					} else {
						final Term div = theory.term("div", params[0], params[1]);
						arg0.add(divisor.negate(), div);
						final Term rhs = unifyPolynomial(arg0, params[1].getSort());
						final Term rewrite = mTracker.buildRewrite(lhs, rhs, ProofConstants.RW_MODULO);
						setResult(mTracker.transitivity(convertedApp, rewrite));
					}
					return;
				} else {
					setResult(convertedApp);
					return;
				}
			}
			case "to_real": {
				final Polynomial arg = new Polynomial(params[0]);
				final Term lhs = mTracker.getProvedTerm(convertedApp);
				final Term rhs = unifyPolynomial(arg, convertedApp.getSort());
				final Term rewrite = mTracker.buildRewrite(lhs, rhs, ProofConstants.RW_CANONICAL_SUM);
				setResult(mTracker.transitivity(convertedApp, rewrite));
				return;
			}
			case "to_int": {
				// We don't convert to_int here but defer it to the clausifier
				// But we simplify constants here...
				if (params[0] instanceof ConstantTerm) {
					final Rational value = (Rational) ((ConstantTerm) params[0]).getValue();
					final Term lhs = mTracker.getProvedTerm(convertedApp);
					final Term rhs = value.floor().toTerm(fsym.getReturnSort());
					final Term rewrite = mTracker.buildRewrite(lhs, rhs, ProofConstants.RW_TO_INT);
					setResult(mTracker.transitivity(convertedApp, rewrite));
					return;
				}
				break;
			}
			case "divisible": {
				final Term lhs = mTracker.getProvedTerm(convertedApp);
				BigInteger divisor1;
				try {
					divisor1 = new BigInteger(fsym.getIndices()[0]);
				} catch (final NumberFormatException e) {
					throw new SMTLIBException("index must be numeral", e);
				}
				final Rational divisor = Rational.valueOf(divisor1, BigInteger.ONE);
				Term rhs;
				if (divisor.equals(Rational.ONE)) {
					rhs = theory.mTrue;
				} else if (params[0] instanceof ConstantTerm) {
					final Rational value = (Rational) ((ConstantTerm) params[0]).getValue();
					rhs = value.equals(divisor.mul(constDiv(value, divisor))) ? theory.mTrue : theory.mFalse;
				} else {
					final Term divisorTerm = divisor.toTerm(params[0].getSort());
					rhs = theory.term("=", params[0],
							theory.term("*", divisorTerm, theory.term("div", params[0], divisorTerm)));
				}
				final Term rewrite = mTracker.buildRewrite(lhs, rhs, ProofConstants.RW_DIVISIBLE);
				setResult(mTracker.transitivity(convertedApp, rewrite));
				return;
			}
			case "store": {
				final Term lhs = mTracker.getProvedTerm(convertedApp);
				final Term array = params[0];
				final Term idx = params[1];
				final Term nestedIdx = getArrayStoreIdx(array);
				if (nestedIdx != null) {
					// Check for store-over-store
					final Polynomial diff = new Polynomial(idx);
					diff.add(Rational.MONE, nestedIdx);
					if (diff.isConstant() && diff.getConstant().equals(Rational.ZERO)) {
						// Found store-over-store => ignore inner store
						final ApplicationTerm appArray = (ApplicationTerm) array;
						final Term rhs = theory.term("store", appArray.getParameters()[0], params[1], params[2]);
						final Term rewrite = mTracker.buildRewrite(lhs, rhs, ProofConstants.RW_STORE_OVER_STORE);
						setResult(mTracker.transitivity(convertedApp, rewrite));
						return;
					}
				}
				break;
			}
			case "select": {
				Term lhs = mTracker.getProvedTerm(convertedApp);
				Term array = params[0];
				final Term idx = params[1];
				boolean isSelect = true;
				while (isSelect) {
					isSelect = false;
					final Term nestedIdx = getArrayStoreIdx(array);
					if (nestedIdx != null) {
						// Check for select-over-store
						final Polynomial diff = new Polynomial(idx);
						diff.add(Rational.MONE, new Polynomial(nestedIdx));
						if (diff.isConstant()) {
							// Found select-over-store
							final ApplicationTerm store = (ApplicationTerm) array;
							final Term rhs;
							if (diff.getConstant().equals(Rational.ZERO)) {
								// => transform into value
								rhs = store.getParameters()[2];
							} else { // Both indices are numerical and distinct.
								// => transform into (select a idx)
								isSelect = true;
								array = store.getParameters()[0];
								rhs = theory.term("select", array, idx);
							}
							final Term rewrite = mTracker.buildRewrite(lhs, rhs, ProofConstants.RW_SELECT_OVER_STORE);
							lhs = rhs;
							convertedApp = mTracker.transitivity(convertedApp, rewrite);
						}
					}
				}
				break;
			}
			case SMTLIBConstants.CONST: {
				final Sort sort = mTracker.getProvedTerm(convertedApp).getSort();
				assert sort.isArraySort();
				if (!isInfinite(sort.getArguments()[0])) {
					/*
					 * We don't support const over non-infinite index sorts. So we require the sort
					 * to be internal and non-bool. Non-bool is already checked earlier.
					 */
					throw new SMTLIBException("Const is only supported for infinite index sort");
				}
				break;
			}
			case "bvmul": {
				pushTerm(bvToIntUtils.translateBvArithmetic(mTracker, appTerm, convertedApp,  mEagerMod));
				return;
			}
			case "bvsub":			
			case "bvadd": {
				setResult(bvToIntUtils.translateBvArithmetic(mTracker, appTerm, convertedApp,  mEagerMod));
				return;
			}
			case "bvneg": {
				setResult(bvToIntUtils.translateBvNeg(mTracker, appTerm, convertedApp,  mEagerMod));
				return;
			}
			case "bvnot": {
				setResult(bvToIntUtils.translateBvNot(mTracker, appTerm, convertedApp,  mEagerMod));
				return;
			}
			case "concat": {
				pushTerm(bvToIntUtils.translateConcat(mTracker, appTerm, convertedApp,  mEagerMod));
				return;
			}
			case "bvudiv": {				
				pushTerm(bvToIntUtils.translateBvudiv(mTracker, appTerm, convertedApp,  mEagerMod));
				return;
			}
			case "bvurem": {
				pushTerm(bvToIntUtils.translateBvurem(mTracker, appTerm, convertedApp,  mEagerMod));
				return;
			}
			case "bvlshr": {
				setResult(bvToIntUtils.translateBvlshr(mTracker, appTerm, convertedApp,  mEagerMod));
				return;
			}
			case "bvshl": {
				setResult(bvToIntUtils.translateBvshl(mTracker, appTerm, convertedApp,  mEagerMod));
				return;
			}
			case "bvand":
			case "bvor": {
				throw new UnsupportedOperationException("Bit-Wise Operations not supported" + appTerm.getFunction().getName());			
//				setResult(bvUtils.transformBitwise(params, fsym));
//				return;
			}
			case "bvuge":
			case "bvslt":
			case "bvule":
			case "bvsle":
			case "bvugt":
			case "bvsgt":
			case "bvsge":
			case "bvult": {
				pushTerm(bvToIntUtils.translateRelations(mTracker, appTerm, convertedApp, true));
				return;
			}
			case "extract": {
				setResult(bvToIntUtils.translateExtract(mTracker, appTerm, convertedApp, true));
				return;
			}
			case "repeat": {
				setResult(bvUtils.transformRepeat(params, fsym, convertedApp));
				return;
			}
			case "zero_extend": {
				// abbreviates (concat ((_ repeat i) #b0) t)
//				if (fsym.getIndices()[0].equals("0")) {
//					setResult(params[0]);
//					return;
//				} else {
//					String repeat = "#b0";
//					for (int i = 1; i < Integer.parseInt(fsym.getIndices()[0]); i++) {
//						repeat = repeat + "0";
//					}
//					pushTerm(theory.term("concat", theory.binary(repeat), params[0]));
//					return;
//				}				
				setResult(bvToIntUtils.nat2bv(bvToIntUtils.bv2nat(convertedApp, mEagerMod), appTerm.getSort().getIndices(), mEagerMod));
				return;
			}
			case "sign_extend": {
				setResult(bvUtils.transformSignExtend(params, fsym, convertedApp));
				return;
			}
			case "rotate_left": {
				setResult(bvUtils.transformRotateleft(params, fsym, convertedApp));
				return;
			}
			case "rotate_right": {
				setResult(bvUtils.transformRotateright(params, fsym, convertedApp));
				return;
			}
			//From here on all bv function do pushTerm
			case "bvnand": {
				// (bvnand s t) abbreviates (bvnot (bvand s t))
				pushTerm(theory.term("bvnot", theory.term("bvand", params)));
				return;
			}
			case "bvnor": {
				// (bvnor s t) abbreviates (bvnot (bvor s t))
				pushTerm(theory.term("bvnot", theory.term("bvor", params)));
				return;
			}
			case "bvxor": {
				assert params.length == 2;
				pushTerm(bvUtils.transformBvxor(params));
				return;
			}
			case "bvxnor": {
				assert params.length == 2;
				pushTerm(bvUtils.transformBvxnor(params));
				return;
			}
			case "bvcomp": {
				pushTerm(bvUtils.transformBvcomp(params));
				return;
			}

			case "bvsdiv": {
				pushTerm(bvUtils.transformBvsdiv(params));
				return;
			}
			case "bvsrem": {
				pushTerm(bvUtils.transformBvsrem(params));
				return;
			}
			case "bvsmod": {
				pushTerm(bvUtils.transformBvsmod(params));
				return;
			}
			case "bvashr": {
				pushTerm(bvUtils.transformBvashr(params));
				return;
			}
			case "bv2nat": {
				//Term should only contain bv2nat around uninterpreted functions / constants
				setResult(bvToIntUtils.bv2nat(params[0], mEagerMod));
				return;
			}
			case "nat2bv": {
				setResult(bvToIntUtils.nat2bv(params[0],appTerm.getSort().getIndices(), mEagerMod));
				return;
//				throw new UnsupportedOperationException("Should be dealt with directly");
			}
			case "true":
			case "false":
			case SMTInterpolConstants.DIFF:
			case "@0": // lambda for QuantifierTheory
			case "is":
			case Interpolator.EQ:
				/* nothing to do */
				break;
			default:
				if (fsym.isConstructor() || fsym.isSelector()) {
					break;
				}
				if (fsym.getName().startsWith("@AUX") || fsym.getName().matches("@.*skolem.*")) {
					break;
				}
				throw new UnsupportedOperationException("Unsupported internal function " + fsym.getName());
			}
		}
		setResult(convertedApp);
	}

	private boolean isInfinite(final Sort sort) {
		if (sort.isInternal()) {
			switch (sort.getName()) {
			case "Int":
			case "Real":
				return true;
			case "Array": {
				final Sort[] args = sort.getArguments();
				final Sort indexSort = args[0];
				final Sort elemSort = args[1];
				return elemSort.isInternal() && isInfinite(indexSort);
			}
			default:
				return false;
			}
		}
		return false;
	}

	public final static Rational constDiv(final Rational c0, final Rational c1) {
		final Rational div = c0.div(c1);
		return c1.isNegative() ? div.ceil() : div.floor();
	}

	private final static Term getArrayStoreIdx(final Term array) {
		if (array instanceof ApplicationTerm) {
			final ApplicationTerm appArray = (ApplicationTerm) array;
			final FunctionSymbol arrayFunc = appArray.getFunction();
			if (arrayFunc.isIntern() && arrayFunc.getName().equals("store")) {
				// (store a i v)
				return appArray.getParameters()[1];
			}
		}
		return null;
	}

	@Override
	public void postConvertMatch(final MatchTerm oldMatch, final Term newDataTerm, final Term[] newCases) {
		setResult(mTracker.match(oldMatch, newDataTerm, newCases));
	}

	@Override
	public void postConvertQuantifier(final QuantifiedFormula old, final Term newBody) {
		final Theory theory = old.getTheory();
		if (!theory.getLogic().isQuantified()) {
			throw new SMTLIBException("Quantifier in quantifier-free logic");
		}
		setResult(mTracker.quantCong(old, newBody));
	}

	@Override
	public void postConvertAnnotation(final AnnotatedTerm old, final Annotation[] newAnnots, final Term newBody) {
		if (mNames != null && newBody.getSort() == newBody.getTheory().getBooleanSort()) {
			final Annotation[] oldAnnots = old.getAnnotations();
			for (final Annotation annot : oldAnnots) {
				if (annot.getKey().equals(":named")) {
					Set<String> oldNames = mNames.get(newBody);
					if (oldNames == null) {
						oldNames = new HashSet<>();
						mNames.put(newBody, oldNames);
					}
					oldNames.add(annot.getValue().toString());
				}
			}
		}
		setResult(
				mTracker.transitivity(mTracker.buildRewrite(old, old.getSubterm(), ProofConstants.RW_STRIP), newBody));
	}

	/**
	 * Canonicalize a polynomial, i.e. check if we already created this term with
	 * the summands in a different order.
	 *
	 * @param poly the polynomial to canonicalize and convert to a term.
	 * @param sort the Sort of the resulting term.
	 * @return the canonic summation term.
	 */
	public Term unifyPolynomial(final Polynomial poly, Sort sort) {
		final int hash = poly.hashCode() ^ sort.hashCode();
		for (final Term canonic : mCanonicalPolys.iterateHashCode(hash)) {
			if (canonic.getSort() == sort && poly.equals(new Polynomial(canonic))) {
				return canonic;
			}
		}
		final Term canonic = poly.toTerm(sort);
		mCanonicalPolys.put(hash, canonic);
		return canonic;
	}
}
