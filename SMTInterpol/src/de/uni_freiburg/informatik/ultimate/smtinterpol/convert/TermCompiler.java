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
import java.util.Arrays;
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
import de.uni_freiburg.informatik.ultimate.logic.NonRecursive;
import de.uni_freiburg.informatik.ultimate.logic.QuantifiedFormula;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.SMTLIBException;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermTransformer;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.logic.Theory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.interpolate.Interpolator;
import de.uni_freiburg.informatik.ultimate.smtinterpol.proof.IProofTracker;
import de.uni_freiburg.informatik.ultimate.smtinterpol.proof.ProofConstants;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.bitvector.BVUtils;
import de.uni_freiburg.informatik.ultimate.util.datastructures.UnifyHash;

/**
 * Build a representation of the formula where only not, or, ite and =/2 are present. Linear arithmetic terms are
 * converted into SMTAffineTerms. We normalize quantifiers to universal quantifiers. Additionally, this term transformer
 * removes all annotations from the formula.
 *
 * @author Jochen Hoenicke, Juergen Christ
 */
public class TermCompiler extends TermTransformer {

	private Map<Term, Set<String>> mNames;
	UnifyHash<ApplicationTerm> mCanonicalSums = new UnifyHash<>();

	private IProofTracker mTracker;
	private LogicSimplifier mUtils;
	private final static String BITVEC_CONST_PATTERN = "bv\\d+";

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
			// TODO: The following is commented out because of the lambdas in QuantifierTheory
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
				final ApplicationTerm rhs = theory.term("and", conjs);
				final Term rewrite = mTracker.buildRewrite(appTerm, rhs, ProofConstants.RW_EXPAND);
				enqueueWalker(new TransitivityStep(rewrite));
				enqueueWalker(new BuildApplicationTerm(rhs));
				pushTerms(conjs);
				return;
			}
		} else if (term instanceof ConstantTerm && term.getSort().isNumericSort()) {
			final Term res = SMTAffineTerm.convertConstant((ConstantTerm) term).toTerm(term.getSort());
			setResult(mTracker.buildRewrite(term, res, ProofConstants.RW_CANONICAL_SUM));
			return;
		} else if (term instanceof TermVariable) {
			setResult(mTracker.reflexivity(term));
			return;
		}
		super.convert(term);
	}

	@Override
	public void convertApplicationTerm(final ApplicationTerm appTerm, final Term[] args) {
		final FunctionSymbol fsym = appTerm.getFunction();
		final Theory theory = appTerm.getTheory();
		final Term convertedApp = mTracker.congruence(mTracker.reflexivity(appTerm), args);
		final Term[] params = ((ApplicationTerm) mTracker.getProvedTerm(convertedApp)).getParameters();
		final BVUtils bvUtils = new BVUtils(theory);

		if (fsym.getDefinition() != null) {
			final HashMap<TermVariable, Term> substs = new HashMap<>();
			for (int i = 0; i < params.length; i++) {
				substs.put(fsym.getDefinitionVars()[i], params[i]);
			}
			final FormulaUnLet unletter = new FormulaUnLet();
			unletter.addSubstitutions(substs);
			final Term expanded = unletter.unlet(fsym.getDefinition());
			final Term expandedProof =
					mTracker.buildRewrite(mTracker.getProvedTerm(convertedApp), expanded, ProofConstants.RW_EXPAND_DEF);
			enqueueWalker(new TransitivityStep(mTracker.transitivity(convertedApp, expandedProof)));
			pushTerm(expanded);
			return;
		}
		if (fsym.isIntern()) {
			if (fsym.getName().matches(BITVEC_CONST_PATTERN)) {
				// BitVec Constants created using Theory.getFunctionWithResult()
				// Not an instanceof ConstantTerm! translate to #b... ConstantTerm
				setResult(bvUtils.getBvConstAsBinaryConst(fsym, convertedApp.getSort()));
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
					final Term elimCM = bvUtils.eliminateConcatPerfectMatch(fsym, params);
					if (elimCM != null) {
						if (elimCM instanceof ApplicationTerm) {
							if (((ApplicationTerm) elimCM).getFunction().getName().equals("and")) {
								setResult(mUtils.convertAnd(elimCM));
								return;
							}
						}
						setResult(elimCM);
						return;
					}
					setResult(bvUtils.iterateOverBvEqualites(mUtils.convertEq(convertedApp), mUtils));
					return;
				}
				setResult(mUtils.convertEq(convertedApp));
				return;
			case "distinct":
				setResult(mUtils.convertDistinct(convertedApp));
				return;
			case "<=": {
				final Term lhs = mTracker.getProvedTerm(convertedApp);
				final Sort sort = params[0].getSort();
				final SMTAffineTerm affine1 = new SMTAffineTerm(params[0]);
				final SMTAffineTerm affine2 = new SMTAffineTerm(params[1]);
				affine2.negate();
				affine1.add(affine2);
				final Term rhs = theory.term("<=", affine1.toTerm(this, sort), Rational.ZERO.toTerm(sort));
				final Term rewrite = mTracker.buildRewrite(lhs, rhs, ProofConstants.RW_LEQ_TO_LEQ0);
				setResult(mUtils.convertLeq0(mTracker.transitivity(convertedApp, rewrite)));
				return;
			}
			case ">=": {
				final Term lhs = mTracker.getProvedTerm(convertedApp);
				final Sort sort = params[0].getSort();
				final SMTAffineTerm affine1 = new SMTAffineTerm(params[1]);
				final SMTAffineTerm affine2 = new SMTAffineTerm(params[0]);
				affine2.negate();
				affine1.add(affine2);
				final Term rhs = theory.term("<=", affine1.toTerm(this, sort), Rational.ZERO.toTerm(sort));
				final Term rewrite = mTracker.buildRewrite(lhs, rhs, ProofConstants.RW_GEQ_TO_LEQ0);
				setResult(mUtils.convertLeq0(mTracker.transitivity(convertedApp, rewrite)));
				return;
			}
			case ">": {
				final Term lhs = mTracker.getProvedTerm(convertedApp);
				final Sort sort = params[0].getSort();
				final SMTAffineTerm affine1 = new SMTAffineTerm(params[0]);
				final SMTAffineTerm affine2 = new SMTAffineTerm(params[1]);
				affine2.negate();
				affine1.add(affine2);
				final Term leq = theory.term("<=", affine1.toTerm(this, sort), Rational.ZERO.toTerm(sort));
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
				final SMTAffineTerm affine1 = new SMTAffineTerm(params[1]);
				final SMTAffineTerm affine2 = new SMTAffineTerm(params[0]);
				affine2.negate();
				affine1.add(affine2);
				final Term leq = theory.term("<=", affine1.toTerm(this, sort), Rational.ZERO.toTerm(sort));
				final Term rhs = theory.term("not", leq);
				Term rewrite = mTracker.buildRewrite(lhs, rhs, ProofConstants.RW_LT_TO_LEQ0);
				final Term leqRewrite = mUtils.convertLeq0(mTracker.reflexivity(leq));
				rewrite = mTracker.congruence(mTracker.transitivity(convertedApp, rewrite), new Term[] { leqRewrite });
				setResult(mUtils.convertNot(rewrite));
				return;
			}
			case "+": {
				final Term lhs = mTracker.getProvedTerm(convertedApp);
				final SMTAffineTerm sum = new SMTAffineTerm(params[0]);
				for (int i = 1; i < params.length; i++) {
					sum.add(new SMTAffineTerm(params[i]));
				}
				final Term rhs = sum.toTerm(this, convertedApp.getSort());
				final Term rewrite = mTracker.buildRewrite(lhs, rhs, ProofConstants.RW_CANONICAL_SUM);
				setResult(mTracker.transitivity(convertedApp, rewrite));
				return;
			}
			case "-": {
				final Term lhs = mTracker.getProvedTerm(convertedApp);
				final SMTAffineTerm result = new SMTAffineTerm(params[0]);
				if (params.length == 1) {
					result.negate();
				} else {
					for (int i = 1; i < params.length; i++) {
						final SMTAffineTerm subtrahend = new SMTAffineTerm(params[i]);
						subtrahend.negate();
						result.add(subtrahend);
					}
				}
				final Term rhs = result.toTerm(this, convertedApp.getSort());
				final Term rewrite = mTracker.buildRewrite(lhs, rhs, ProofConstants.RW_CANONICAL_SUM);
				setResult(mTracker.transitivity(convertedApp, rewrite));
				return;
			}
			case "*": {
				final Term lhs = mTracker.getProvedTerm(convertedApp);
				SMTAffineTerm prod = new SMTAffineTerm(params[0]);
				for (int i = 1; i < params.length; i++) {
					final SMTAffineTerm factor = new SMTAffineTerm(params[i]);
					if (prod.isConstant()) {
						factor.mul(prod.getConstant());
						prod = factor;
					} else if (factor.isConstant()) {
						prod.mul(factor.getConstant());
					} else {
						throw new UnsupportedOperationException("Unsupported non-linear arithmetic");
					}
				}
				final Term rhs = prod.toTerm(this, convertedApp.getSort());
				final Term rewrite = mTracker.buildRewrite(lhs, rhs, ProofConstants.RW_CANONICAL_SUM);
				setResult(mTracker.transitivity(convertedApp, rewrite));
				return;
			}
			case "/": {
				final Term lhs = mTracker.getProvedTerm(convertedApp);
				final SMTAffineTerm arg0 = new SMTAffineTerm(params[0]);
				if (params[1] instanceof ConstantTerm) {
					final Rational arg1 = SMTAffineTerm.convertConstant((ConstantTerm) params[1]);
					if (arg1.equals(Rational.ZERO)) {
						setResult(convertedApp);
					} else {
						arg0.mul(arg1.inverse());
						final Term rhs = arg0.toTerm(this, convertedApp.getSort());
						final Term rewrite = mTracker.buildRewrite(lhs, rhs, ProofConstants.RW_CANONICAL_SUM);
						setResult(mTracker.transitivity(convertedApp, rewrite));
					}
					return;
				} else {
					throw new UnsupportedOperationException("Unsupported non-linear arithmetic");
				}
			}
			case "div": {
				final Term lhs = mTracker.getProvedTerm(convertedApp);
				final SMTAffineTerm arg0 = new SMTAffineTerm(params[0]);
				if (params[1] instanceof ConstantTerm) {
					final Rational divisor = (Rational) ((ConstantTerm) params[1]).getValue();
					assert divisor.isIntegral();
					if (divisor.equals(Rational.ONE)) {
						final Term rhs = arg0.toTerm(this, convertedApp.getSort());
						final Term rewrite = mTracker.buildRewrite(lhs, rhs, ProofConstants.RW_DIV_ONE);
						setResult(mTracker.transitivity(convertedApp, rewrite));
					} else if (divisor.equals(Rational.MONE)) {
						arg0.negate();
						final Term rhs = arg0.toTerm(this, convertedApp.getSort());
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
					throw new UnsupportedOperationException("Unsupported non-linear arithmetic");
				}
			}
			case "mod": {
				final Term lhs = mTracker.getProvedTerm(convertedApp);
				final SMTAffineTerm arg0 = new SMTAffineTerm(params[0]);
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
						final Term rhs = arg0.toTerm(this, params[1].getSort());
						final Term rewrite = mTracker.buildRewrite(lhs, rhs, ProofConstants.RW_MODULO);
						setResult(mTracker.transitivity(convertedApp, rewrite));
					}
					return;
				} else {
					throw new UnsupportedOperationException("Unsupported non-linear arithmetic");
				}
			}
			case "to_real": {
				final SMTAffineTerm arg = new SMTAffineTerm(params[0]);
				final Term lhs = mTracker.getProvedTerm(convertedApp);
				final Term rhs = arg.toTerm(this, convertedApp.getSort());
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
					final SMTAffineTerm diff = new SMTAffineTerm(idx);
					diff.negate();
					diff.add(new SMTAffineTerm(nestedIdx));
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
				final Term lhs = mTracker.getProvedTerm(convertedApp);
				final Term array = params[0];
				final Term idx = params[1];
				final Term nestedIdx = getArrayStoreIdx(array);
				if (nestedIdx != null) {
					// Check for select-over-store
					final SMTAffineTerm diff = new SMTAffineTerm(idx);
					diff.negate();
					diff.add(new SMTAffineTerm(nestedIdx));
					if (diff.isConstant()) {
						// Found select-over-store
						final ApplicationTerm store = (ApplicationTerm) array;
						final Term rhs;
						if (diff.getConstant().equals(Rational.ZERO)) {
							// => transform into value
							rhs = store.getParameters()[2];
						} else { // Both indices are numerical and distinct.
							// => transform into (select a idx)
							rhs = theory.term("select", store.getParameters()[0], idx);
						}
						final Term rewrite = mTracker.buildRewrite(lhs, rhs, ProofConstants.RW_SELECT_OVER_STORE);
						setResult(mTracker.transitivity(convertedApp, rewrite));
						return;
					}
				}
				break;
			}
			case "const": {
				final Sort sort = mTracker.getProvedTerm(convertedApp).getSort();
				assert sort.isArraySort();
				if (!isInfinite(sort.getArguments()[0])) {
					/*
					 * We don't support const over non-infinite index sorts. So we require the sort to be internal and
					 * non-bool. Non-bool is already checked earlier.
					 */
					throw new SMTLIBException("Const is only supported for infinite index sort");
				}
				break;
			}
			case "concat": {
				if (bvUtils.isConstRelation(params[0], params[1])) {
					setResult(bvUtils.getProof(bvUtils.simplifyConcatConst(fsym, params[0], params[1]), convertedApp,
							mTracker, ProofConstants.RW_CONCAT));
					return;
				}
				setResult(convertedApp);
				return;
			}
			case "bvsub":
			case "bvudiv":
			case "bvurem": {
				if (bvUtils.isConstRelation(params[0], params[1])) {
					setResult(bvUtils.getProof(bvUtils.simplifyArithmeticConst(fsym, params[0], params[1]), convertedApp,
							mTracker, ProofConstants.RW_BVARITH));
					return;
				}
				setResult(convertedApp);
				return;
			}

			case "bvadd":
			case "bvmul": {
				if (bvUtils.isConstRelation(params[0], params[1])) {
					setResult(bvUtils.getProof(bvUtils.simplifyArithmeticConst(fsym, params[0], params[1]), convertedApp,
							mTracker, ProofConstants.RW_BVARITH));
					return;
				}
				setResult(bvUtils.orderParameters(fsym, params));
				return;
			}
			case "bvand":
			case "bvor": {
				if (bvUtils.isConstRelation(params[0], params[1])) {
					setResult(bvUtils.getProof(bvUtils.simplifyLogicalConst(fsym, params[0], params[1]), convertedApp,
							mTracker, ProofConstants.RW_BVLOGIC));
					return;
				} else {
					// order before bitmaskelimination!
					final Term bitMask =
							bvUtils.bitMaskElimination(
									bvUtils.orderParameters(fsym, params));
					setResult(bitMask);
					return;
				}
			}
			case "bvlshr":
			case "bvshl": {
				if (bvUtils.isConstRelation(params[0], params[1])) {
					setResult(bvUtils.getProof(bvUtils.simplifyShiftConst(fsym, params[0], params[1]), convertedApp,
							mTracker, ProofConstants.RW_BVSHIFT));
					return;
				}
				setResult(convertedApp);
				return;
			}
			case "bvneg": {
				if (params[0] instanceof ConstantTerm) {
					// TODO
					setResult(bvUtils.simplifyNegConst(fsym, params[0]));
					return;
				}
				setResult(convertedApp);
				return;
			}
			case "bvnot": {
				if (params[0] instanceof ConstantTerm) {
					// TODO
					setResult(bvUtils.simplifyNotConst(fsym, params[0]));
					return;
				}
				setResult(convertedApp);
				return;
			}
			case "bvuge":
			case "bvslt":
			case "bvule":
			case "bvsle":
			case "bvugt":
			case "bvsgt":
			case "bvsge":
			case "bvult": {
				// TODO FIX
				final Term bvult = bvUtils.getBvultTerm(convertedApp);
				if (bvult instanceof ApplicationTerm) {
					final ApplicationTerm appterm = (ApplicationTerm) bvult;
					if (appterm.getFunction().getName().equals("or")) {
						setResult(mUtils.convertOr(bvult));
						return;
					}
				}
				setResult(bvult);
				return;
			}
			case "extract": {
				if (params[0] instanceof ConstantTerm) {
					setResult(bvUtils.simplifySelectConst(fsym, params[0]));
					return;
				}
				final Term extract = bvUtils.propagateExtract(fsym, params[0]);
				setResult(extract); // TODO check obs fehlher hier gibt von wegen
				// convertiereung
				return;
			}
			case "bvnand":{
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
				// TODO bvxor is left associative
				// (bvxor s t) abbreviates (bvor (bvand s (bvnot t)) (bvand (bvnot s) t))
				pushTerm(theory.term("bvor",
						theory.term("bvand", params[0], theory.term("bvnot", params[1])),
						theory.term("bvand", theory.term("bvnot", params[0]), params[1])));
				return;
			}
			case "bvxnor": {
				// (bvxnor s t) abbreviates (bvor (bvand s t) (bvand (bvnot s) (bvnot t)))
				// bvxor is left associative
				pushTerm(theory.term("bvor",
						theory.term("bvand", params[0], params[1]),
						theory.term("bvand", theory.term("bvnot", params[0]), theory.term("bvnot", params[1]))));
				return;
			}
			case "bvcomp": {
				// bit comparator: equals #b1 iff all bits are equal
				final int size = Integer.parseInt(params[0].getSort().getIndices()[0]);
				final Term[] bvxnor = new Term[size];
				for (int i = 0; i < size; i++) {
					final String[] selectIndices = new String[2];
					selectIndices[0] = String.valueOf(i);
					selectIndices[1] = String.valueOf(i);

					final FunctionSymbol extractLhs =
							theory.getFunctionWithResult("extract", selectIndices.clone(), null,
									params[0].getSort());
					final FunctionSymbol extractRhs =
							theory.getFunctionWithResult("extract", selectIndices.clone(), null,
									params[0].getSort());
					final Term extrctLhs = theory.term(extractLhs, params[0]);
					final Term extrctRhs = theory.term(extractRhs, params[1]);

					bvxnor[i] = theory.term("bvor",
							theory.term("bvand", extrctLhs, extrctRhs),
							theory.term("bvand", theory.term("bvnot", extrctLhs), theory.term("bvnot", extrctRhs)));
				}
				if (size == 1) {
					pushTerm(bvxnor[0]);
					return;
				}
				Term result = bvxnor[0];
				for (int i = 1; i < size; i++) {
					result = theory.term("bvand", bvxnor[i], result);
				}
				pushTerm(result);
				return;
			}

			case "bvsdiv": {
				// (ite (and (= ((_ extract |m-1| |m-1|) s)#b0) (= ((_ extract |m-1| |m-1|) t) #b0))
				// (bvudiv s t)
				// (ite (and (= ((_ extract |m-1| |m-1|) s) #b1) (= ((_ extract |m-1| |m-1|) t) #b0))
				// (bvneg (bvudiv (bvneg s) t))
				// (ite (and (= ((_ extract |m-1| |m-1|) s) #b0) (= ((_ extract |m-1| |m-1|) t) #b1))
				// (bvneg (bvudiv s (bvneg t)))
				// (bvudiv (bvneg s) (bvneg t)))))
				final int size = Integer.parseInt(params[0].getSort().getIndices()[0]);
				final String[] selectIndices = new String[2];
				selectIndices[0] = String.valueOf(size - 1);
				selectIndices[1] = String.valueOf(size - 1);

				final FunctionSymbol extract =
						theory.getFunctionWithResult("extract", selectIndices.clone(), null,
								params[0].getSort());
				final Term extractSignLhs = theory.term(extract, params[0]);
				final Term extractSignRhs = theory.term(extract, params[1]);

				pushTerm(theory.ifthenelse(theory.term("and", theory.term("=", extractSignLhs, theory.binary("#b0")),
						theory.term("=", extractSignRhs, theory.binary("#b0"))),
						theory.term("bvudiv", params[0], params[1]),
						theory.ifthenelse(theory.term("and", theory.term("=", extractSignLhs, theory.binary("#b1")),
								theory.term("=", extractSignRhs, theory.binary("#b0"))),
								theory.term("bvneg", theory.term("bvudiv", theory.term("bvneg", params[0]), params[1])),
								theory.ifthenelse(
										theory.term("and", theory.term("=", extractSignLhs, theory.binary("#b0")),
												theory.term("=", extractSignRhs, theory.binary("#b1"))),
										theory.term("bvneg",
												theory.term("bvudiv", params[0], theory.term("bvneg", params[1]))),
										theory.term("bvudiv", theory.term("bvneg", params[0]),
												theory.term("bvneg", params[1]))))));
				return;
			}
			case "bvsrem": {
				// abbreviation as defined in the SMT-Lib
				final int size = Integer.parseInt(params[0].getSort().getIndices()[0]);
				final String[] selectIndices = new String[2];
				selectIndices[0] = String.valueOf(size - 1);
				selectIndices[1] = String.valueOf(size - 1);

				final FunctionSymbol extract =
						theory.getFunctionWithResult("extract", selectIndices.clone(), null,
								params[0].getSort());
				final Term extractSignLhs = theory.term(extract, params[0]);
				final Term extractSignRhs = theory.term(extract, params[1]);

				pushTerm(theory.ifthenelse(theory.term("and", theory.term("=", extractSignLhs, theory.binary("#b0")),
						theory.term("=", extractSignRhs, theory.binary("#b0"))),
						theory.term("bvurem", params[0], params[1]),
						theory.ifthenelse(theory.term("and", theory.term("=", extractSignLhs, theory.binary("#b1")),
								theory.term("=", extractSignRhs, theory.binary("#b0"))),
								theory.term("bvneg", theory.term("bvurem", theory.term("bvneg", params[0]), params[1])),
								theory.ifthenelse(
										theory.term("and", theory.term("=", extractSignLhs, theory.binary("#b0")),
												theory.term("=", extractSignRhs, theory.binary("#b1"))),
										theory.term("bvurem", params[0], theory.term("bvneg", params[1])),
										theory.term("bvneg", theory.term("bvurem", theory.term("bvneg", params[0]),
												theory.term("bvneg", params[1])))))));
				return;
			}
			case "bvsmod": {
				// abbreviation as defined in the SMT-Lib
				final int size = Integer.parseInt(params[0].getSort().getIndices()[0]);
				final String[] selectIndices = new String[2];
				selectIndices[0] = String.valueOf(size - 1);
				selectIndices[1] = String.valueOf(size - 1);

				final FunctionSymbol extract =
						theory.getFunctionWithResult("extract", selectIndices.clone(), null,
								params[0].getSort());
				final Term extractSignLhs = theory.term(extract, params[0]);
				final Term extractSignRhs = theory.term(extract, params[1]);
				final Term ite1 = theory.ifthenelse(theory.term("=", extractSignLhs, theory.binary("#b0")), params[0],
						theory.term("bvneg", params[0]));
				final Term ite2 = theory.ifthenelse(theory.term("=", extractSignRhs, theory.binary("#b0")), params[1],
						theory.term("bvneg", params[1]));
				final Term bvurem = theory.term("bvurem", ite1, ite2);

				final String[] constindices = new String[1];
				constindices[0] = params[0].getSort().getIndices()[0];
				final Term zeroVec =
						theory.term(theory.getFunctionWithResult("bv0", constindices, null, params[0].getSort()));

				final Term elseTerm3 = theory.ifthenelse(
						theory.and(theory.term("=", extractSignLhs, theory.binary("#b0")),
								theory.term("=", extractSignRhs, theory.binary("#b1"))),
						theory.term("bvadd", bvurem, params[1]),
						theory.term("bvneg", bvurem));
				final Term elseTerm2 = theory.ifthenelse(
						theory.and(theory.term("=", extractSignLhs, theory.binary("#b1")),
								theory.term("=", extractSignRhs, theory.binary("#b0"))),
						theory.term("bvadd", theory.term("bvneg", bvurem), params[1]),
						elseTerm3);
				final Term elseTerm =
						theory.ifthenelse(
								theory.and(theory.term("=", extractSignLhs, theory.binary("#b0")),
										theory.term("=", extractSignRhs, theory.binary("#b0"))),
								bvurem,
								elseTerm2);
				pushTerm(theory.ifthenelse(theory.term("=", bvurem, zeroVec), bvurem, elseTerm));
				return;
			}
			case "bvashr": {
				// abbreviation as defined in the SMT-Lib
				final int size = Integer.parseInt(params[0].getSort().getIndices()[0]);
				final String[] selectIndices = new String[2];
				selectIndices[0] = String.valueOf(size - 1);
				selectIndices[1] = String.valueOf(size - 1);

				final FunctionSymbol extract =
						theory.getFunctionWithResult("extract", selectIndices.clone(), null,
								params[0].getSort());

				pushTerm(theory.ifthenelse(
						theory.term("=", theory.term(extract, params[0]), theory.binary("#b0")),
						theory.term("bvlshr", params[0], params[1]),
						theory.term("bvnot", theory.term("bvlshr", theory.term("bvnot", params[0]), params[1]))));
				return;
			}
			case "repeat": {
				if (fsym.getIndices()[0].equals("1")) {
					setResult(params[0]);
					return;
				} else {
					Term repeat = params[0];
					for (int i = 1; i < Integer.parseInt(fsym.getIndices()[0]); i++) { //start from 1
						repeat = theory.term("concat", params[0], repeat);
					}
					pushTerm(repeat);
					return;
				}
			}
			case "zero_extend": {
				// abbreviates (concat ((_ repeat i) #b0) t)
				if (fsym.getIndices()[0].equals("0")) {
					setResult(params[0]);
					return;
				} else if(fsym.getIndices()[0].equals("1")){
					pushTerm(theory.term("concat", theory.binary("#b0"), params[0]));
					return;
				}else{
					Term repeat = theory.binary("#b0");
					for (int i = 1; i < Integer.parseInt(fsym.getIndices()[0]); i++) {
						repeat = theory.term("concat", theory.binary("#b0"), repeat); // TODO strings instead of terms
					}
					pushTerm(theory.term("concat", repeat, params[0]));
					return;
				}
			}

			case "sign_extend": {
				// abbreviates (concat ((_ repeat i) ((_ extract |m-1| |m-1|) t)) t)

				final int size = Integer.parseInt(params[0].getSort().getIndices()[0]);
				final String[] selectIndices = new String[2];
				selectIndices[0] = String.valueOf(size - 1);
				selectIndices[1] = String.valueOf(size - 1);

				final FunctionSymbol extract =
						theory.getFunctionWithResult("extract", selectIndices.clone(), null,
								params[0].getSort());

				if (fsym.getIndices()[0].equals("0")) {
					setResult(params[0]);
					return;
				} else if(fsym.getIndices()[0].equals("1")){
					pushTerm(theory.term("concat", theory.term(extract, params[0]), params[0]));
					return;
				}else{
					Term repeat = theory.term(extract, params[0]);
					for (int i = 1; i < Integer.parseInt(fsym.getIndices()[0]); i++) {
						repeat = theory.term("concat", theory.term(extract, params[0]), repeat);
					}
					pushTerm(theory.term("concat", repeat, params[0]));
					return;
				}
			}

			case "rotate_left": {
				final int size = Integer.parseInt(params[0].getSort().getIndices()[0]);


				if (fsym.getIndices()[0].equals("0")) {
					setResult(params[0]);
					return;
				} else if (size == 1) {
					setResult(params[0]);
					return;
				} else {

					final String[] selectIndicesLhs = new String[2];
					selectIndicesLhs[0] = String.valueOf(size - 2);
					selectIndicesLhs[1] = "0";

					final FunctionSymbol extractLhs =
							theory.getFunctionWithResult("extract", selectIndicesLhs, null,
									params[0].getSort());

					final String[] selectIndicesRhs = new String[2];
					selectIndicesRhs[0] = String.valueOf(size - 1);
					selectIndicesRhs[1] = String.valueOf(size - 1);

					final FunctionSymbol extractRhs =
							theory.getFunctionWithResult("extract", selectIndicesRhs, null,
									params[0].getSort());

					final Term concat = theory.term("concat", theory.term(extractLhs, params[0]),
							theory.term(extractRhs, params[0]));

					final String[] rotateIndice = new String[1];
					rotateIndice[0] = String.valueOf(Integer.parseInt(fsym.getIndices()[0]) - 1);

					final FunctionSymbol rotateLeft =
							theory.getFunctionWithResult("rotate_left", rotateIndice, null,
									params[0].getSort());

					final Term rotate = theory.term(rotateLeft, concat);

					pushTerm(rotate);
					return;
				}
			}
			case "rotate_right": {
				final int size = Integer.parseInt(params[0].getSort().getIndices()[0]);

				if (fsym.getIndices()[0].equals("0")) {
					setResult(params[0]);
					return;
				} else if (size == 1) {
					setResult(params[0]);
					return;
				} else {

					final String[] selectIndicesLhs = new String[2];
					selectIndicesLhs[0] = "0";
					selectIndicesLhs[1] = "0";

					final FunctionSymbol extractLhs =
							theory.getFunctionWithResult("extract", selectIndicesLhs, null,
									params[0].getSort());

					final String[] selectIndicesRhs = new String[2];
					selectIndicesRhs[0] = String.valueOf(size - 1);
					selectIndicesRhs[1] = "1";

					final FunctionSymbol extractRhs =
							theory.getFunctionWithResult("extract", selectIndicesRhs, null,
									params[0].getSort());

					final Term concat = theory.term("concat", theory.term(extractLhs, params[0]),
							theory.term(extractRhs, params[0]));

					final String[] rotateIndice = new String[1];
					rotateIndice[0] = String.valueOf(Integer.parseInt(fsym.getIndices()[0]) - 1);

					final FunctionSymbol rotateLeft =
							theory.getFunctionWithResult("rotate_right", rotateIndice, null,
									params[0].getSort());

					final Term rotate = theory.term(rotateLeft, concat);

					pushTerm(rotate);
					return;
				}
			}
			case "true":
			case "false":
			case "@diff":
			case "@0": // lambda for QuantifierTheory
			case Interpolator.EQ:
				/* nothing to do */
				break;
			default:
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
	public void postConvertQuantifier(final QuantifiedFormula old, final Term newBody) {
		final Theory theory = old.getTheory();
		if (!theory.getLogic().isQuantified()) {
			throw new SMTLIBException("Quantifier in quantifier-free logic");
		}
		if (old.getQuantifier() == QuantifiedFormula.EXISTS) {
			setResult(mTracker.exists(old, newBody));
		} else {
			// We should create (forall (x) (newBody x))
			// This becomes (not (exists (x) (not (newBody x))))
			final Term notNewBody = mUtils.convertNot(mTracker
					.congruence(mTracker.reflexivity(theory.term("not", old.getSubformula())), new Term[] { newBody }));
			setResult(mUtils.convertNot(mTracker.forall(old, notNewBody)));
		}
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
	 * Canonicalize a summation term, i.e. check if we already created this term with the summands in a different order.
	 *
	 * @param sumTerm
	 *            the summation term of the form {@code (+ p1 ... pn)}.
	 * @return the canonic summation term.
	 */
	public ApplicationTerm unifySummation(final ApplicationTerm sumTerm) {
		assert sumTerm.getFunction().getName() == "+";
		final HashSet<Term> summands = new HashSet<>();
		int hash = 0;
		for (final Term p : sumTerm.getParameters()) {
			final boolean fresh = summands.add(p);
			assert fresh;
			hash += p.hashCode();
		}
		hash = summands.hashCode();
		for (final ApplicationTerm canonic : mCanonicalSums.iterateHashCode(hash)) {
			if (canonic.getParameters().length == summands.size()
					&& summands.containsAll(Arrays.asList(canonic.getParameters()))) {
				return canonic;
			}
		}
		mCanonicalSums.put(hash, sumTerm);
		return sumTerm;
	}
}
