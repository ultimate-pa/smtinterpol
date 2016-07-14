/**
 * 
 */
package de.uni_freiburg.informatik.ultimate.smtinterpol.proof;

//import java.text.Annotation;

import java.math.BigDecimal;
import java.math.BigInteger;
import java.util.ArrayList;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.logic.AnnotatedTerm;
import de.uni_freiburg.informatik.ultimate.logic.Annotation;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.ConstantTerm;
import de.uni_freiburg.informatik.ultimate.logic.FunctionSymbol;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.Theory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.convert.SMTAffineTerm;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.DPLLAtom;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.Literal;

/**
 * @author Markus
 *
 */
public class RuleApplicator implements IRuleApplicator{

	/**
	 * 
	 */
	public RuleApplicator() {
	}
	
	private static class Rewrite {
		Rewrite mNext;
		public Term toTerm() {
			throw new InternalError("toTerm called on sentinel");
		}
	}
	
	private class RemoveConnective extends Rewrite {
		private final int mRule;
		private final Term[] mArgs;
		private final Term mRes;
		public RemoveConnective(int rule, Term[] args, Term res) {
			mRule = rule;
			/* If rule is RW_AND_TO_OR, we are called from createAndInplace.  We
			 * have to clone the args since they get changed!
			 */
			mArgs = rule == ProofConstants.RW_AND_TO_OR ? args.clone() : args;
			mRes = res;
		}
		@Override
		public Term toTerm() {
			Theory t = mArgs[0].getTheory();
			Term orig, res;
			Term[] resArgs = mArgs;
			switch(mRule) {
			case ProofConstants.RW_AND_TO_OR:
				resArgs = new Term[mArgs.length];
				orig = t.term(t.mAnd, mArgs);
				for (int i = 0; i < resArgs.length; ++i)
					resArgs[i] = t.term(t.mNot, mArgs[i]);
				res = t.term(t.mNot, t.term(t.mOr, resArgs));
				break;
			case ProofConstants.RW_XOR_TO_DISTINCT:
				orig = t.term(t.mXor, mArgs);
				res = t.term("distinct", resArgs);
				break;
			case ProofConstants.RW_IMP_TO_OR:
				resArgs = new Term[resArgs.length];
				orig = t.term(t.mImplies, mArgs);
				for (int i = 1; i < resArgs.length; ++i)
					resArgs[i] = t.term(t.mNot, mArgs[i - 1]);
				resArgs[0] = mArgs[mArgs.length - 1];
				res = t.term(t.mOr, resArgs);
				break;
			case ProofConstants.RW_LEQ_TO_LEQ0:
				orig = t.term("<=", mArgs);
				resArgs = new Term[2];
				resArgs[0] = SMTAffineTerm.cleanup(mRes);
				resArgs[1] = resArgs[0].getSort().getName().equals("Int")
					? t.numeral(BigInteger.ZERO) : t.decimal(BigDecimal.ZERO);
				res = t.term("<=", resArgs);
				break;
			case ProofConstants.RW_GEQ_TO_LEQ0:
				orig = t.term(">=", mArgs);
				resArgs = new Term[2];
				resArgs[0] = SMTAffineTerm.cleanup(mRes);
				resArgs[1] = resArgs[0].getSort().getName().equals("Int")
					? t.numeral(BigInteger.ZERO) : t.decimal(BigDecimal.ZERO);
				res = t.term("<=", resArgs);
				break;
			case ProofConstants.RW_GT_TO_LEQ0:
				orig = t.term(">", mArgs);
				resArgs = new Term[2];
				resArgs[0] = SMTAffineTerm.cleanup(mRes);
				resArgs[1] = resArgs[0].getSort().getName().equals("Int")
					? t.numeral(BigInteger.ZERO) : t.decimal(BigDecimal.ZERO);
				res = t.term(t.mNot, t.term("<=", resArgs));
				break;
			case ProofConstants.RW_LT_TO_LEQ0:
				orig = t.term("<", mArgs);
				resArgs = new Term[2];
				resArgs[0] = SMTAffineTerm.cleanup(mRes);
				resArgs[1] = resArgs[0].getSort().getName().equals("Int")
					? t.numeral(BigInteger.ZERO) : t.decimal(BigDecimal.ZERO);
				res = t.term(t.mNot, t.term("<=", resArgs));
				break;
			default:
				throw new InternalError(
						"BUG in ProofTracker: RemoveConnective");
			}
			return buildProofTerm(orig, res, "removeConnective");
		}
	}
	

	@Override
	public Term expand(ApplicationTerm orig, Term expanded) {	
		return this.buildProofTerm(orig, expanded, "expand");
	}

	@Override
	public Term expandDef(Term orig, Term res) {
		return this.buildProofTerm(orig, res, "expandDef");
	}

	@Override
	public Term equality(Term[] args, Object res, int rule) {
		Term tres = null;
		if (res instanceof Term) {
			tres = (Term) res;
		}
		else {
			Theory t = args[0].getTheory();
			assert res instanceof Term[];
			Term[] resArgs = (Term[]) res;
			if (resArgs.length == 0)
				tres = t.mTrue;
			else if (resArgs.length == 1)
				tres = rule == ProofConstants.RW_EQ_FALSE 
					? t.term(t.mNot, resArgs[0]) : resArgs[0];
			else if (rule == ProofConstants.RW_EQ_TRUE) {
				// We use inplace algorithms.  So clone the array.
				tres = t.term(t.mAnd, resArgs.clone());
			} else if (rule == ProofConstants.RW_EQ_FALSE)
				tres = t.term(t.mNot, t.term(t.mOr, resArgs));
			else if (rule == ProofConstants.RW_EQ_SIMP)
				tres = t.term("=", resArgs);
			else {
				throw new InternalError("Strange result in equality rewrite");
			}
		}
		Theory t = tres.getTheory();
		Term argsTerm = t.term("=", args);	
		return this.buildProofTerm(argsTerm, tres, "equality");
	}

	@Override
	public Term distinct(Term[] args, Term res, int rule) {
		if (res == null) {
			Theory t = args[0].getTheory();
			if (rule == ProofConstants.RW_DISTINCT_TRUE) {
				if (args[0] == t.mTrue)
					res = t.term(t.mNot, args[1]);
				else
					res = t.term(t.mNot, args[0]);
			} else
				throw new InternalError("Result should be given");
		}
		Theory t = res.getTheory();
		Term argsTerm = t.term("distinct", args);
		return this.buildProofTerm(argsTerm, res, "distinct");
	}

	@Override
	public Term distinctBoolEq(Term lhs, Term rhs, boolean firstNegated) {
		Theory t = lhs.getTheory();
		Term distinct = t.term("distinct", lhs, rhs);
		Term res = firstNegated ? t.term("=", t.term(t.mNot, lhs), rhs)
			: t.term("=", lhs, t.term(t.mNot, rhs));		
		return this.buildProofTerm(distinct, res, "distinctBoolEq");
	}

	@Override
	public Term negation(Term pos, Term res, int rule) {
		Theory t = res.getTheory();		
		Term argsTerm = t.term(t.mNot, pos);
		return this.buildProofTerm(argsTerm, res, "negation");
	}

	@Override
	public Term or(Term[] args, Term res, int rule) {
		Theory t = res.getTheory();
		Term argsTerm = t.term("or", args);
		return this.buildProofTerm(argsTerm, res, "or");
	}

	@Override
	public Term ite(Term cond, Term thenTerm, Term elseTerm, Term res, int rule) {
		Theory t = cond.getTheory();
		if (res == null) {
			switch(rule) {
			case ProofConstants.RW_ITE_BOOL_2:
				res = t.term(t.mNot, cond);
				break;
			case ProofConstants.RW_ITE_BOOL_4:
				res = t.term(t.mNot, t.term(t.mOr, cond,
						t.term(t.mNot, elseTerm)));
				break;
			case ProofConstants.RW_ITE_BOOL_5:
				res = t.term(t.mOr, t.term(t.mNot, cond), thenTerm);
				break;
			case ProofConstants.RW_ITE_BOOL_6:
				res = t.term(t.mNot,	t.term(t.mOr, t.term(t.mNot, cond),
						t.term(t.mNot, thenTerm)));
				break;
			default:
				throw new InternalError("BUG in ProofTracker: ITE");
			}
		}
		Term argsTerm = t.term("ite", cond, thenTerm, elseTerm);
		return this.buildProofTerm(argsTerm, res, "ite");
	}

	@Override
	public Term removeConnective(Term[] origArgs, Term result, int rule) {
		RemoveConnective rmC = new RemoveConnective(rule, origArgs, result);
		return rmC.toTerm();
	}

	@Override
	public Term strip(AnnotatedTerm orig) {
		return this.buildProofTerm(orig, orig.getSubterm(), "strip");
	}

	@Override
	public Term sum(FunctionSymbol fsym, Term[] args, Term res) {
		Theory t = fsym.getTheory();
		Term left = SMTAffineTerm.cleanup(t.term(fsym, args));
		Term right = SMTAffineTerm.cleanup(res);
		if (left != right){
			Term statement = t.term("=", left, right);
			
			Annotation[] sum = new Annotation[1];
			sum[0] = new Annotation(":sum", null);
			
			Term proof = (AnnotatedTerm) t.annotatedTerm(sum, statement);
			Term proof1 = t.term("@rewrite", proof);
			
			Annotation[] f = new Annotation[1];
			f[0] = new Annotation(":proof", proof1);
			
			return (AnnotatedTerm) t.annotatedTerm(f, right);
		}
		else{
			Term proof = t.term("@refl", right);
			
			Annotation[] annotions = new Annotation[1];
			annotions[0] = new Annotation(":proof", proof);

			return (AnnotatedTerm) t.annotatedTerm(annotions, right);
		}
	}

	@Override
	public Term normalized(ConstantTerm term, SMTAffineTerm res) {
		Theory t = res.getTheory();
		Term rhs = SMTAffineTerm.cleanup(res);
		if (term != rhs){
			Term statement = t.term("=", term, rhs);
			
			Annotation[] normalized = new Annotation[1];
			normalized[0] = new Annotation(":normalized", null);
			
			Term proof = (AnnotatedTerm) t.annotatedTerm(normalized, statement);
			Term proof1 = t.term("@rewrite", proof);
			
			Annotation[] f = new Annotation[1];
			f[0] = new Annotation(":proof", proof1);
			
			return (AnnotatedTerm) t.annotatedTerm(f, rhs);
		}
		else{
			Term proof = t.term("@refl", res);
			
			Annotation[] annotions = new Annotation[1];
			annotions[0] = new Annotation(":proof", proof);

			return (AnnotatedTerm) t.annotatedTerm(annotions, res);
		}
	}

	@Override
	public Term toLeq0(Term orig, SMTAffineTerm leq, int rule) {
		Theory t = orig.getTheory();
		Term right = t.term(
				"<=", SMTAffineTerm.cleanup(leq),
				leq.getSort().getName().equals("Int")
					? t.numeral(BigInteger.ZERO) : t.decimal(BigDecimal.ZERO));
		
		if (rule == ProofConstants.RW_LT_TO_LEQ0
				|| rule == ProofConstants.RW_GT_TO_LEQ0)
			right = t.term(t.mNot, right);
		if (right != orig){
			Term statement = t.term("=", orig, right);
			
			Annotation[] toLeq0 = new Annotation[1];
			toLeq0[0] = new Annotation(":toLeq0", null);
			
			Term proof = (AnnotatedTerm) t.annotatedTerm(toLeq0, statement);
			Term proof1 = t.term("@rewrite", proof);
			
			Annotation[] f = new Annotation[1];
			f[0] = new Annotation(":proof", proof1);
			
			return (AnnotatedTerm) t.annotatedTerm(f, right);
		}
		else{
			Term proof = t.term("@refl", right);
			
			Annotation[] annotions = new Annotation[1];
			annotions[0] = new Annotation(":proof", proof);
			
			return (AnnotatedTerm) t.annotatedTerm(annotions, right);
		}
	}

	@Override
	public Term leqSimp(SMTAffineTerm leq, Term res, int rule) {
		Theory t = res.getTheory();
		Term left = t.term("<=", SMTAffineTerm.cleanup(leq),
				leq.getSort().getName().equals("Int")
					? t.numeral(BigInteger.ZERO) : t.decimal(BigDecimal.ZERO));
		
		Term statement = t.term("=", left, res);
		
		Annotation[] leqSimp = new Annotation[1];
		leqSimp[0] = new Annotation(":leqSimp", null);
		
		Term proof = (AnnotatedTerm) t.annotatedTerm(leqSimp, statement);
		Term proof1 = t.term("@rewrite", proof);
		
		Annotation[] f = new Annotation[1];
		f[0] = new Annotation(":proof", proof1);
		
		return (AnnotatedTerm) t.annotatedTerm(f, res);
	}

	@Override
	public Term desugar(ApplicationTerm orig, Term[] origArgs, Term[] newArgs) {
		Theory t = orig.getTheory();
		FunctionSymbol fsym = orig.getFunction();
		Term left = t.term(fsym, origArgs);
		Term right = t.term(fsym, newArgs);
		
		Term statement = t.term("=", left, right);
		
		Annotation[] desugar = new Annotation[1];
		desugar[0] = new Annotation(":desugar", null);
		
		Term proof = (AnnotatedTerm) t.annotatedTerm(desugar, statement);
		Term proof1 = t.term("@rewrite", proof);
		
		Annotation[] f = new Annotation[1];
		f[0] = new Annotation(":proof", proof1);
		
		return (AnnotatedTerm) t.annotatedTerm(f, right);
	}

	@Override
	public Term modulo(ApplicationTerm appTerm, Term res) {
		Theory t = appTerm.getTheory();
		Term statement = t.term("=", appTerm, res);
		
		Annotation[] modulo = new Annotation[1];
		modulo[0] = new Annotation(":modulo", null);
		
		Term proof = (AnnotatedTerm) t.annotatedTerm(modulo, statement);
		Term proof1 = t.term("@rewrite", proof);
		
		Annotation[] f = new Annotation[1];
		f[0] = new Annotation(":proof", proof1);
		
		return (AnnotatedTerm) t.annotatedTerm(f, res);
	}

	@Override
	public Term mod(Term x, Term y, Term res, int rule) {
		Theory t = x.getTheory();
		Term mod = t.term(
				"mod", SMTAffineTerm.cleanup(x), SMTAffineTerm.cleanup(y));
		Term statement = t.term("=", mod, SMTAffineTerm.cleanup(res));
		
		Annotation[] modulo = new Annotation[1];
		modulo[0] = new Annotation(":mod", null);
		
		Term proof = (AnnotatedTerm) t.annotatedTerm(modulo, statement);
		Term proof1 = t.term("@rewrite", proof);
		
		Annotation[] f = new Annotation[1];
		f[0] = new Annotation(":proof", proof1);
		
		return (AnnotatedTerm) t.annotatedTerm(f, SMTAffineTerm.cleanup(res));
		
	}

	@Override
	public Term div(Term x, Term y, Term res, int rule) {
		Theory t = x.getTheory();
		Term mod = t.term(
				"div", SMTAffineTerm.cleanup(x), SMTAffineTerm.cleanup(y));
		
		Term statement = t.term("=", mod, SMTAffineTerm.cleanup(res));
		
		Annotation[] div = new Annotation[1];
		div[0] = new Annotation(":div", null);
		
		Term proof = (AnnotatedTerm) t.annotatedTerm(div, statement);
		Term proof1 = t.term("@rewrite", proof);
		
		Annotation[] f = new Annotation[1];
		f[0] = new Annotation(":proof", proof1);
		
		return (AnnotatedTerm) t.annotatedTerm(f, SMTAffineTerm.cleanup(res));
	}

	@Override
	public Term divisible(FunctionSymbol divn, Term div, Term res) {
		Theory t = res.getTheory();
		
		//TODO: mindestens 2 argumente für divn
		Term divisible = t.term(divn, SMTAffineTerm.cleanup(div));
		
		Term statement = t.term("=", divisible, res);
		
		Annotation[] divisibleAnno = new Annotation[1];
		divisibleAnno[0] = new Annotation(":divisible", null);
		
		Term proof = (AnnotatedTerm) t.annotatedTerm(divisibleAnno, statement);
		Term proof1 = t.term("@rewrite", proof);
		
		Annotation[] f = new Annotation[1];
		f[0] = new Annotation(":proof", proof1);
		
		return (AnnotatedTerm) t.annotatedTerm(f, res);
	}

	@Override
	public Term toInt(Term arg, Term res) {
		Theory t = arg.getTheory();
		Term toint = t.term("to_int", SMTAffineTerm.cleanup(arg));
		
		Term statement = t.term("=", toint, SMTAffineTerm.cleanup(res));
		
		Annotation[] toInt = new Annotation[1];
		toInt[0] = new Annotation(":toInt", null);
		
		Term proof = (AnnotatedTerm) t.annotatedTerm(toInt, statement);
		Term proof1 = t.term("@rewrite", proof);
		
		Annotation[] f = new Annotation[1];
		f[0] = new Annotation(":proof", proof1);
		
		return (AnnotatedTerm) t.annotatedTerm(f, SMTAffineTerm.cleanup(res));
	}

	@Override
	public Term toReal(Term arg, Term res) {
		Theory t = arg.getTheory();
		Term orig = t.term(
				"to_real", SMTAffineTerm.cleanup(arg));
		
		Term statement = t.term("=", orig, SMTAffineTerm.cleanup(res));
		
		Annotation[] toReal = new Annotation[1];
		toReal[0] = new Annotation(":toReal", null);
		
		Term proof = (AnnotatedTerm) t.annotatedTerm(toReal, statement);
		Term proof1 = t.term("@rewrite", proof);
		
		Annotation[] f = new Annotation[1];
		f[0] = new Annotation(":proof", proof1);
		
		return (AnnotatedTerm) t.annotatedTerm(f, SMTAffineTerm.cleanup(res));
	}

	@Override
	public Term arrayRewrite(Term[] args, Term result, int rule) {
		Theory t = result.getTheory();
		Term input;
			
		if (rule == ProofConstants.RW_STORE_OVER_STORE) {
			input = t.term("store", args);
		}
		else {
			input =  t.term("select", args);
		}
		
		Term statement = t.term("=", input, result);
		
		Annotation[] arrayRewrite = new Annotation[1];
		arrayRewrite[0] = new Annotation(":arrayRewrite", null);
		
		Term proof = (AnnotatedTerm) t.annotatedTerm(arrayRewrite, statement);
		Term proof1 = t.term("@rewrite", proof);
		
		Annotation[] f = new Annotation[1];
		f[0] = new Annotation(":proof", proof1);
		
		return (AnnotatedTerm) t.annotatedTerm(f, result);
	}

	@Override
	public Term storeRewrite(ApplicationTerm store, Term result,
			boolean arrayFirst) {
		Term array = store.getParameters()[0];
		Theory t = store.getTheory();
		Term orig = arrayFirst ? t.term("=", array, store)
			: t.term("=", store, array);
		
		Term statement = t.term("=", orig, result);
		
		Annotation[] storeRewrite = new Annotation[1];
		storeRewrite[0] = new Annotation(":storeRewrite", null);
		
		Term proof = (AnnotatedTerm) t.annotatedTerm(storeRewrite, statement);
		Term proof1 = t.term("@rewrite", proof);
		
		Annotation[] f = new Annotation[1];
		f[0] = new Annotation(":proof", proof1);
		
		return (AnnotatedTerm) t.annotatedTerm(f, result);
	}

	@Override
	public Term quoted(Term orig, Literal quote) {
		Theory theory = orig.getTheory();
		Term t = quote.getSMTFormula(orig.getTheory(), true);
		
		Term statement = theory.term("=", orig, t);
		
		Annotation[] quoted = new Annotation[1];
		quoted[0] = new Annotation(":quoted", null);
		
		Term proof = (AnnotatedTerm) theory.annotatedTerm(quoted, statement);
		Term proof1 = theory.term("@rewrite", proof);
		
		Annotation[] f = new Annotation[1];
		f[0] = new Annotation(":proof", proof1);
		
		return (AnnotatedTerm) theory.annotatedTerm(f, t);
	}

	@Override
	public Term eq(Term lhs, Term rhs, Term res) {
		Theory t = res.getTheory();
		Term orig = res.getTheory().term("=", lhs, rhs);
		if (orig != res) {
			Term statement = t.term("=", orig, res);
			
			Annotation[] eq = new Annotation[1];
			eq[0] = new Annotation(":eq", null);
			
			Term proof = (AnnotatedTerm) t.annotatedTerm(eq, statement);
			Term proof1 = t.term("@rewrite", proof);
			
			Annotation[] f = new Annotation[1];
			f[0] = new Annotation(":proof", proof1);
			
			return (AnnotatedTerm) t.annotatedTerm(f, res);
		}
		else {
			Term proof = t.term("@refl", res);
			
			Annotation[] annotions = new Annotation[1];
			annotions[0] = new Annotation(":proof", proof);
			
			return (AnnotatedTerm) t.annotatedTerm(annotions, res);
		}

	}

	@Override
	public Term eq(Term lhs, Term rhs, DPLLAtom eqAtom) {
		Theory t = lhs.getTheory();
		Term res = SMTAffineTerm.cleanup(eqAtom.getSMTFormula(t, true));
		Term orig = SMTAffineTerm.cleanup(t.term("=", lhs, rhs));
		if (orig != res) {
			Term statement = t.term("=", orig, res);
			
			Annotation[] eq = new Annotation[1];
			eq[0] = new Annotation(":eq", null);
			
			Term proof = (AnnotatedTerm) t.annotatedTerm(eq, statement);
			Term proof1 = t.term("@rewrite", proof);
			
			Annotation[] f = new Annotation[1];
			f[0] = new Annotation(":proof", proof1);
			
			return (AnnotatedTerm) t.annotatedTerm(f, res);
		}
		else {
			Term proof = t.term("@refl", res);
			
			Annotation[] annotions = new Annotation[1];
			annotions[0] = new Annotation(":proof", proof);
			
			return (AnnotatedTerm) t.annotatedTerm(annotions, res);
		}
	}

	@Override
	public Term leq0(SMTAffineTerm sum, Literal lit) {
		Theory t = sum.getTheory();
		Term orig = t.term("<=", SMTAffineTerm.cleanup(sum),
				sum.getSort().getName().equals("Int")
					? t.numeral(BigInteger.ZERO) : t.decimal(BigDecimal.ZERO));
		Term res = lit.getSMTFormula(t, true);
		if (orig != res) {
			Term statement = t.term("=", orig, res);
			
			Annotation[] eq = new Annotation[1];
			eq[0] = new Annotation(":eq", null);
			
			Term proof = (AnnotatedTerm) t.annotatedTerm(eq, statement);
			Term proof1 = t.term("@rewrite", proof);
			
			Annotation[] f = new Annotation[1];
			f[0] = new Annotation(":proof", proof1);
			
			return (AnnotatedTerm) t.annotatedTerm(f, res);
		}
		else {
			Term proof = t.term("@refl", res);
			
			Annotation[] annotions = new Annotation[1];
			annotions[0] = new Annotation(":proof", proof);
			
			return (AnnotatedTerm) t.annotatedTerm(annotions, res);
		}
	}

	@Override
	public Term intern(Term term, Literal lit) {
		Theory t = term.getTheory();
		Term orig = SMTAffineTerm.cleanup(term);
		Term res = lit.getSMTFormula(t, true);
		if (orig != res) {
			Term statement = t.term("=", orig, res);
			
			Annotation[] eq = new Annotation[1];
			eq[0] = new Annotation(":eq", null);
			
			Term proof = (AnnotatedTerm) t.annotatedTerm(eq, statement);
			Term proof1 = t.term("@rewrite", proof);
			
			Annotation[] f = new Annotation[1];
			f[0] = new Annotation(":proof", proof1);
			
			return (AnnotatedTerm) t.annotatedTerm(f, res);
		}
		else {
			Term proof = t.term("@refl", res);
			
			Annotation[] annotions = new Annotation[1];
			annotions[0] = new Annotation(":proof", proof);
			
			return (AnnotatedTerm) t.annotatedTerm(annotions, res);
		}
	}

	@Override
	public Term negateLit(Literal lit, Theory theory) {
		assert lit.getSign() == -1 : "Literal not negated!";
		Term lhs = theory.term(theory.mNot,
				SMTAffineTerm.cleanup(lit.getSMTFormula(theory, true)));
		Term rhs = SMTAffineTerm.cleanup(
				lit.getAtom().getSMTFormula(theory, true));
		
		Term statement = theory.term("=", lhs, rhs);
		
		Annotation[] negateLit = new Annotation[1];
		negateLit[0] = new Annotation(":negateLit", null);
		
		Term proof = (AnnotatedTerm) theory.annotatedTerm(negateLit, statement);
		Term proof1 = theory.term("@rewrite", proof);
		
		Annotation[] f = new Annotation[1];
		f[0] = new Annotation(":proof", proof1);
		
		return (AnnotatedTerm) theory.annotatedTerm(f, rhs);
	}

	@Override
	public Term flatten(Term[] args, boolean simpOr) {
		// TODO clausifier
		return null;
	}

	@Override
	public Term orSimpClause(Term[] args) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Term reflexivity(Term a) {
		
		Theory theory = a.getTheory();
		
		Term proof = theory.term("@refl", a);
		
		Annotation[] annotions = new Annotation[1];
		annotions[0] = new Annotation(":proof", proof);

		return (AnnotatedTerm) theory.annotatedTerm(annotions, a);
	}

	@Override
	public Term transitivity(Term a, Term b) {
		
		AnnotatedTerm aTa = (AnnotatedTerm) a;
		AnnotatedTerm aTb = (AnnotatedTerm) b;		
		
		Theory theory = a.getTheory();
		
		Annotation[] AnnotationTermA = aTa.getAnnotations();
		Term proof1 = (Term) AnnotationTermA[0].getValue();
		
		assert proof1 != null;
		
		Annotation[] AnnotationTermB = aTb.getAnnotations();
		Term proof2 = (Term) AnnotationTermB[0].getValue();
		
		assert proof2 != null;
		
		Term resultProof = theory.term("@trans", proof1, proof2);
		
		Annotation[] AnnotationResult = new Annotation[1];
		AnnotationResult[0] = new Annotation(":proof", resultProof);
		
		Term result = theory.annotatedTerm(AnnotationResult, aTb.getSubterm());
		
		return result;
	}

	@Override
	public Term congruence(Term a, Term[] b) {
		
		AnnotatedTerm annotatedTermA = (AnnotatedTerm) a;
		ApplicationTerm applicationTermA =
				(ApplicationTerm) annotatedTermA.getSubterm();
		Theory theory = a.getTheory();
		FunctionSymbol func = applicationTermA.getFunction();
		int length = b.length;
		
		Term[] paras = new Term[length];
		List<Term> proofs = new ArrayList<Term>();
		proofs.add((Term) ((AnnotatedTerm) a).getAnnotations()[0].getValue());
		
		for (int i = 0; i < length; i++) {
			AnnotatedTerm annot = (AnnotatedTerm) b[i];
			paras[i] = annot.getSubterm();
			Annotation proof = annot.getAnnotations()[0];
			assert proof.getKey().equals(":proof");
			
			ApplicationTerm s = (ApplicationTerm) proof.getValue();
			
			if (!s.getFunction().getName().equals("@refl")){
				proofs.add(s);
			}
			
		}
		
		Term[] proofsAsArray = proofs.toArray(new Term[0]);
		
		Term resultProof;
		
		if (proofsAsArray.length == 1){
			resultProof = proofsAsArray[0];
		}
		else {
			resultProof = theory.term("@cong", proofsAsArray);
		}
		
		Annotation[] annotationResult = new Annotation[1];
		annotationResult[0] = new Annotation(":proof", resultProof);
		
		Term resultTerm = theory.term(func, paras);
		
		Term result = theory.annotatedTerm(annotationResult, resultTerm);
		return result;
	}

	@Override
	public Term clause(Term proof) {
		// TODO Auto-generated method stub
		return null;
	}

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.smtinterpol.proof.IRuleApplicator#auxAxiom(int, de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.Literal, de.uni_freiburg.informatik.ultimate.logic.Term, de.uni_freiburg.informatik.ultimate.logic.Term, java.lang.Object)
	 */
	@Override
	public Term auxAxiom(int auxKind, Literal auxLit, Term data, Term base,
			Object auxData) {
		// TODO Auto-generated method stub
		return null;
	}

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.smtinterpol.proof.IRuleApplicator#split(de.uni_freiburg.informatik.ultimate.logic.Term, de.uni_freiburg.informatik.ultimate.logic.Term, int)
	 */
	@Override
	public Term split(Term data, Term proof, int splitKind) {
		// TODO Auto-generated method stub
		return null;
	}

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.smtinterpol.proof.IRuleApplicator#getRewriteProof(de.uni_freiburg.informatik.ultimate.logic.Term)
	 */
	@Override
	public Term getRewriteProof(Term asserted) {
		// TODO Auto-generated method stub
		return null;
	}
	
	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.smtinterpol.proof.IRuleApplicator#getDescendent()
	 */
	@Override
	public IRuleApplicator getDescendent() {
		// TODO Auto-generated method stub
		return null;
	}

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.smtinterpol.proof.IRuleApplicator#prepareIRAHack(de.uni_freiburg.informatik.ultimate.logic.Term[])
	 */
	@Override
	public Term[] prepareIRAHack(Term[] args) {
		// TODO Auto-generated method stub
		return null;
	}
	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.smtinterpol.proof.IRuleApplicator#markPosition()
	 */
	@Override
	public void markPosition() {
		// TODO Auto-generated method stub
		
	}

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.smtinterpol.proof.IRuleApplicator#produceAuxAxiom(de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.Literal, de.uni_freiburg.informatik.ultimate.logic.Term[])
	 */
	@Override
	public Term[] produceAuxAxiom(Literal auxlit, Term... args) {
		// TODO Auto-generated method stub
		return null;
	}

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.smtinterpol.proof.IRuleApplicator#notifyLiteral(de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.Literal, de.uni_freiburg.informatik.ultimate.logic.Term)
	 */
	@Override
	public boolean notifyLiteral(Literal lit, Term t) {
		// TODO Auto-generated method stub
		return false;
	}

	@Override
	public Term getTerm(Term t) {
		if (t instanceof AnnotatedTerm) {
			return ((AnnotatedTerm) t).getSubterm();
		}
		else {
			return t;
		}
	}

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.smtinterpol.proof.IRuleApplicator#save()
	 */
	@Override
	public void save() {
		// TODO Auto-generated method stub
		
	}

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.smtinterpol.proof.IRuleApplicator#cleanSave()
	 */
	@Override
	public void cleanSave() {
		// TODO Auto-generated method stub
		
	}

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.smtinterpol.proof.IRuleApplicator#notifyFalseLiteral(de.uni_freiburg.informatik.ultimate.logic.Term)
	 */
	@Override
	public void notifyFalseLiteral(Term t) {
		// TODO Auto-generated method stub
		
	}

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.smtinterpol.proof.IRuleApplicator#restore()
	 */
	@Override
	public void restore() {
		// TODO Auto-generated method stub
		
	}

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.smtinterpol.proof.IRuleApplicator#reset()
	 */
	@Override
	public void reset() {
		// TODO Auto-generated method stub
		
	}
	
	public Term buildProofTerm(Term orig, Term res, String name){
		assert orig != null;
		assert res != null;
		assert name != null;
		Theory theory = orig.getTheory();
		Term statement = theory.term("=", orig, res);
		Annotation[] annot = new Annotation[1];
		annot[0] = new Annotation(":" + name, null);
		Term proof = (AnnotatedTerm) theory.annotatedTerm(annot, statement);
		Annotation[] f = new Annotation[1];
		f[0] = new Annotation(":proof", theory.term("@rewrite", proof));
		return (AnnotatedTerm) theory.annotatedTerm(f, res);
	}


}
