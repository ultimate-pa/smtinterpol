/**
 * 
 */
package de.uni_freiburg.informatik.ultimate.smtinterpol.proof;

import java.math.BigDecimal;
import java.math.BigInteger;

import de.uni_freiburg.informatik.ultimate.logic.AnnotatedTerm;
import de.uni_freiburg.informatik.ultimate.logic.Annotation;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.ConstantTerm;
import de.uni_freiburg.informatik.ultimate.logic.FunctionSymbol;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.Theory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.convert.SMTAffineTerm;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.DPLLAtom;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.Literal;

/**
 * @author Markus
 *
 */
public class NoopRuleApplicator implements IRuleApplicator {

	/**
	 * 
	 */
	public NoopRuleApplicator() {
	}

	@Override
	public Term expand(ApplicationTerm orig, Term expanded) {
		return expanded;
	}

	@Override
	public Term expandDef(Term orig, Term res) {
		return res;
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
		return tres;
			
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
		return res;
	}
	
	@Override
	public Term distinctBoolEq(Term lhs, Term rhs, boolean firstNegated) {
		Theory t = lhs.getTheory();
		Term res;
		if (firstNegated) {
			res = t.term("=", t.term(t.mNot, lhs), rhs);
		}
		else {
			res = t.term("=", lhs, t.term(t.mNot, rhs));
		}
		return res;
	}

	@Override
	public Term negation(Term pos, Term res, int rule) {
		return res;
	}

	@Override
	public Term or(Term[] args, Term res, int rule) {
		return res;
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
		return res;
	}

	@Override
	public Term removeConnective(Term[] origArgs, Term result, int rule) {
		return result;
	}

	@Override
	public Term strip(AnnotatedTerm orig) {
		return orig.getSubterm();
	}

	@Override
	public Term sum(FunctionSymbol fsym, Term[] args, Term res) {
		Term right = SMTAffineTerm.cleanup(res);
		return right;
	}

	@Override
	public Term normalized(ConstantTerm term, SMTAffineTerm res) {
		Term rhs = SMTAffineTerm.cleanup(res);
		return rhs;
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
		return right;
	}

	@Override
	public Term leqSimp(SMTAffineTerm leq, Term res, int rule) {
		return res;
	}

	@Override
	public Term desugar(ApplicationTerm orig, Term[] origArgs, Term[] newArgs) {
		Theory t = orig.getTheory();
		return t.term(orig.getFunction(), newArgs);
	}

	@Override
	public Term modulo(ApplicationTerm appTerm, Term res) {
		return res;
	}

	@Override
	public Term mod(Term x, Term y, Term res, int rule) {
		return SMTAffineTerm.cleanup(res);
	}

	@Override
	public Term div(Term x, Term y, Term res, int rule) {
		return SMTAffineTerm.cleanup(res);
	}

	@Override
	public Term divisible(FunctionSymbol divn, Term div, Term res) {
		return res;
	}

	@Override
	public Term toInt(Term arg, Term res) {
		return SMTAffineTerm.cleanup(res);
	}

	@Override
	public Term toReal(Term arg, Term res) {
		return SMTAffineTerm.cleanup(res);
	}

	@Override
	public Term arrayRewrite(Term[] args, Term result, int rule) {
		return result;
	}

	@Override
	public Term storeRewrite(ApplicationTerm store, Term result,
			boolean arrayFirst) {
		return result;
	}

	@Override
	public Term quoted(Term orig, Literal quote) {
		return quote.getSMTFormula(orig.getTheory(), true);
	}

	@Override
	public Term eq(Term lhs, Term rhs, Term res) {
		return res;
	}

	@Override
	public Term eq(Term lhs, Term rhs, DPLLAtom eqAtom) {
		Theory t = lhs.getTheory();
		return SMTAffineTerm.cleanup(eqAtom.getSMTFormula(t, true));
	}

	@Override
	public Term leq0(SMTAffineTerm sum, Literal lit) {
		Theory t = sum.getTheory();
		return lit.getSMTFormula(t, true);
	}

	@Override
	public Term intern(Term term, Literal lit) {
		Theory t = term.getTheory();
		return lit.getSMTFormula(t, true);
	}

	@Override
	public Term negateLit(Literal lit, Theory theory) {
		return SMTAffineTerm.cleanup(lit.getAtom().getSMTFormula(theory, true));
	}

	@Override
	public Term flatten(Term[] args, boolean simpOr) {
		// TODO without flattenhelper?
		return null;
	}

	@Override
	public Term orSimpClause(Term[] args) {
		// TODO mLits?
		return null;
	}

	@Override
	public Term reflexivity(Term a) {
		return a;
	}

	@Override
	public Term transitivity(Term a, Term b) {
		return b;
	}

	@Override
	public Term congruence(Term a, Term[] b) {
		Theory theory = a.getSort().getTheory();
		FunctionSymbol func = ((ApplicationTerm) a).getFunction();
		Term resultTerm = theory.term(func, b);
		return resultTerm;
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
	 * @see de.uni_freiburg.informatik.ultimate.smtinterpol.proof.IRuleApplicator#clause(de.uni_freiburg.informatik.ultimate.logic.Term)
	 */
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

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.smtinterpol.proof.IRuleApplicator#notifyFalseLiteral(de.uni_freiburg.informatik.ultimate.logic.Term)
	 */
	@Override
	public void notifyFalseLiteral(Term t) {
		// TODO Auto-generated method stub
		
	}

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.smtinterpol.proof.IRuleApplicator#reset()
	 */
	@Override
	public void reset() {
		// TODO Auto-generated method stub
		
	}

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.smtinterpol.proof.IRuleApplicator#save()
	 */
	@Override
	public void save() {
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
	 * @see de.uni_freiburg.informatik.ultimate.smtinterpol.proof.IRuleApplicator#cleanSave()
	 */
	@Override
	public void cleanSave() {
		// TODO Auto-generated method stub
		
	}

}
