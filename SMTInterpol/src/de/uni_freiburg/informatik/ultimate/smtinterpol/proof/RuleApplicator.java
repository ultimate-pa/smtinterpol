/**
 * 
 */
package de.uni_freiburg.informatik.ultimate.smtinterpol.proof;

//import java.text.Annotation;

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
public class RuleApplicator implements IRuleApplicator{

	private static final Annotation[] Annotation = null;

	/**
	 * 
	 */
	public RuleApplicator() {
		// TODO Auto-generated constructor stub
	}

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.smtinterpol.proof.IRuleApplicator#expand(de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm)
	 */
	@Override
	public Term expand(ApplicationTerm orig, Term expanded) {
		// TODO Auto-generated method stub
		return null;
	}

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.smtinterpol.proof.IRuleApplicator#expandDef(de.uni_freiburg.informatik.ultimate.logic.Term, de.uni_freiburg.informatik.ultimate.logic.Term)
	 */
	@Override
	public Term expandDef(Term orig, Term res) {
		// TODO Auto-generated method stub
		return null;
	}

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.smtinterpol.proof.IRuleApplicator#equality(de.uni_freiburg.informatik.ultimate.logic.Term[], java.lang.Object, int)
	 */
	@Override
	public Term equality(Term[] args, Object res, int rule) {
		// TODO Auto-generated method stub
		return null;
	}

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.smtinterpol.proof.IRuleApplicator#distinct(de.uni_freiburg.informatik.ultimate.logic.Term[], de.uni_freiburg.informatik.ultimate.logic.Term, int)
	 */
	@Override
	public Term distinct(Term[] args, Term res, int rule) {
		// TODO Auto-generated method stub
		return null;
	}

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.smtinterpol.proof.IRuleApplicator#distinctBoolEq(de.uni_freiburg.informatik.ultimate.logic.Term, de.uni_freiburg.informatik.ultimate.logic.Term, boolean)
	 */
	@Override
	public Term distinctBoolEq(Term lhs, Term rhs, boolean firstNegated) {
		// TODO Auto-generated method stub
		return null;
	}

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.smtinterpol.proof.IRuleApplicator#negation(de.uni_freiburg.informatik.ultimate.logic.Term, de.uni_freiburg.informatik.ultimate.logic.Term, int)
	 */
	@Override
	public Term negation(Term pos, Term res, int rule) {
		// TODO Auto-generated method stub
		return null;
	}

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.smtinterpol.proof.IRuleApplicator#or(de.uni_freiburg.informatik.ultimate.logic.Term[], de.uni_freiburg.informatik.ultimate.logic.Term, int)
	 */
	@Override
	public Term or(Term[] args, Term res, int rule) {
		// TODO Auto-generated method stub
		return null;
	}

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.smtinterpol.proof.IRuleApplicator#ite(de.uni_freiburg.informatik.ultimate.logic.Term, de.uni_freiburg.informatik.ultimate.logic.Term, de.uni_freiburg.informatik.ultimate.logic.Term, de.uni_freiburg.informatik.ultimate.logic.Term, int)
	 */
	@Override
	public Term ite(Term cond, Term thenTerm, Term elseTerm, Term res, int rule) {
		// TODO Auto-generated method stub
		return null;
	}

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.smtinterpol.proof.IRuleApplicator#removeConnective(de.uni_freiburg.informatik.ultimate.logic.Term[], de.uni_freiburg.informatik.ultimate.logic.Term, int)
	 */
	@Override
	public Term removeConnective(Term[] origArgs, Term result, int rule) {
		// TODO Auto-generated method stub
		return null;
	}

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.smtinterpol.proof.IRuleApplicator#strip(de.uni_freiburg.informatik.ultimate.logic.AnnotatedTerm)
	 */
	@Override
	public Term strip(AnnotatedTerm orig) {
		// TODO Auto-generated method stub
		return null;
	}

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.smtinterpol.proof.IRuleApplicator#sum(de.uni_freiburg.informatik.ultimate.logic.FunctionSymbol, de.uni_freiburg.informatik.ultimate.logic.Term[], de.uni_freiburg.informatik.ultimate.logic.Term)
	 */
	@Override
	public Term sum(FunctionSymbol fsym, Term[] args, Term res) {
		// TODO Auto-generated method stub
		return null;
	}

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.smtinterpol.proof.IRuleApplicator#normalized(de.uni_freiburg.informatik.ultimate.logic.ConstantTerm, de.uni_freiburg.informatik.ultimate.smtinterpol.convert.SMTAffineTerm)
	 */
	@Override
	public Term normalized(ConstantTerm term, SMTAffineTerm res) {
		// TODO Auto-generated method stub
		return null;
	}

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.smtinterpol.proof.IRuleApplicator#toLeq0(de.uni_freiburg.informatik.ultimate.logic.Term, de.uni_freiburg.informatik.ultimate.smtinterpol.convert.SMTAffineTerm, int)
	 */
	@Override
	public Term toLeq0(Term orig, SMTAffineTerm leq, int rule) {
		// TODO Auto-generated method stub
		return null;
	}

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.smtinterpol.proof.IRuleApplicator#leqSimp(de.uni_freiburg.informatik.ultimate.smtinterpol.convert.SMTAffineTerm, de.uni_freiburg.informatik.ultimate.logic.Term, int)
	 */
	@Override
	public Term leqSimp(SMTAffineTerm leq, Term res, int rule) {
		// TODO Auto-generated method stub
		return null;
	}

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.smtinterpol.proof.IRuleApplicator#desugar(de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm, de.uni_freiburg.informatik.ultimate.logic.Term[], de.uni_freiburg.informatik.ultimate.logic.Term[])
	 */
	@Override
	public Term desugar(ApplicationTerm orig, Term[] origArgs, Term[] newArgs) {
		// TODO Auto-generated method stub
		return null;
	}

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.smtinterpol.proof.IRuleApplicator#modulo(de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm, de.uni_freiburg.informatik.ultimate.logic.Term)
	 */
	@Override
	public Term modulo(ApplicationTerm appTerm, Term res) {
		// TODO Auto-generated method stub
		return null;
	}

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.smtinterpol.proof.IRuleApplicator#mod(de.uni_freiburg.informatik.ultimate.logic.Term, de.uni_freiburg.informatik.ultimate.logic.Term, de.uni_freiburg.informatik.ultimate.logic.Term, int)
	 */
	@Override
	public Term mod(Term x, Term y, Term res, int rule) {
		// TODO Auto-generated method stub
		return null;
	}

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.smtinterpol.proof.IRuleApplicator#div(de.uni_freiburg.informatik.ultimate.logic.Term, de.uni_freiburg.informatik.ultimate.logic.Term, de.uni_freiburg.informatik.ultimate.logic.Term, int)
	 */
	@Override
	public Term div(Term x, Term y, Term res, int rule) {
		// TODO Auto-generated method stub
		return null;
	}

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.smtinterpol.proof.IRuleApplicator#divisible(de.uni_freiburg.informatik.ultimate.logic.FunctionSymbol, de.uni_freiburg.informatik.ultimate.logic.Term, de.uni_freiburg.informatik.ultimate.logic.Term)
	 */
	@Override
	public Term divisible(FunctionSymbol divn, Term div, Term res) {
		// TODO Auto-generated method stub
		return null;
	}

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.smtinterpol.proof.IRuleApplicator#toInt(de.uni_freiburg.informatik.ultimate.logic.Term, de.uni_freiburg.informatik.ultimate.logic.Term)
	 */
	@Override
	public Term toInt(Term arg, Term res) {
		// TODO Auto-generated method stub
		return null;
	}

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.smtinterpol.proof.IRuleApplicator#toReal(de.uni_freiburg.informatik.ultimate.logic.Term, de.uni_freiburg.informatik.ultimate.logic.Term)
	 */
	@Override
	public Term toReal(Term arg, Term res) {
		// TODO Auto-generated method stub
		return null;
	}

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.smtinterpol.proof.IRuleApplicator#arrayRewrite(de.uni_freiburg.informatik.ultimate.logic.Term[], de.uni_freiburg.informatik.ultimate.logic.Term, int)
	 */
	@Override
	public Term arrayRewrite(Term[] args, Term result, int rule) {
		// TODO Auto-generated method stub
		return null;
	}

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.smtinterpol.proof.IRuleApplicator#storeRewrite(de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm, de.uni_freiburg.informatik.ultimate.logic.Term, boolean)
	 */
	@Override
	public Term storeRewrite(ApplicationTerm store, Term result,
			boolean arrayFirst) {
		// TODO Auto-generated method stub
		return null;
	}

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.smtinterpol.proof.IRuleApplicator#quoted(de.uni_freiburg.informatik.ultimate.logic.Term, de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.Literal)
	 */
	@Override
	public Term quoted(Term orig, Literal quote) {
		// TODO Auto-generated method stub
		return null;
	}

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.smtinterpol.proof.IRuleApplicator#eq(de.uni_freiburg.informatik.ultimate.logic.Term, de.uni_freiburg.informatik.ultimate.logic.Term, de.uni_freiburg.informatik.ultimate.logic.Term)
	 */
	@Override
	public Term eq(Term lhs, Term rhs, Term res) {
		// TODO Auto-generated method stub
		return null;
	}

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.smtinterpol.proof.IRuleApplicator#eq(de.uni_freiburg.informatik.ultimate.logic.Term, de.uni_freiburg.informatik.ultimate.logic.Term, de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.DPLLAtom)
	 */
	@Override
	public Term eq(Term lhs, Term rhs, DPLLAtom eqAtom) {
		// TODO Auto-generated method stub
		return null;
	}

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.smtinterpol.proof.IRuleApplicator#leq0(de.uni_freiburg.informatik.ultimate.smtinterpol.convert.SMTAffineTerm, de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.Literal)
	 */
	@Override
	public Term leq0(SMTAffineTerm sum, Literal lit) {
		// TODO Auto-generated method stub
		return null;
	}

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.smtinterpol.proof.IRuleApplicator#intern(de.uni_freiburg.informatik.ultimate.logic.Term, de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.Literal)
	 */
	@Override
	public Term intern(Term term, Literal lit) {
		// TODO Auto-generated method stub
		return null;
	}

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.smtinterpol.proof.IRuleApplicator#negateLit(de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.Literal, de.uni_freiburg.informatik.ultimate.logic.Theory)
	 */
	@Override
	public Term negateLit(Literal lit, Theory theory) {
		// TODO Auto-generated method stub
		return null;
	}

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.smtinterpol.proof.IRuleApplicator#flatten(de.uni_freiburg.informatik.ultimate.logic.Term[], boolean)
	 */
	@Override
	public Term flatten(Term[] args, boolean simpOr) {
		// TODO Auto-generated method stub
		return null;
	}

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.smtinterpol.proof.IRuleApplicator#orSimpClause(de.uni_freiburg.informatik.ultimate.logic.Term[])
	 */
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
		
		AnnotatedTerm first = (AnnotatedTerm) a;
		AnnotatedTerm second = (AnnotatedTerm) b;
		
		Annotation[] c = first.getAnnotations();
		ApplicationTerm proofStep1 = (ApplicationTerm) c[0].getValue();
		
		Annotation[] d = second.getAnnotations();
		ApplicationTerm proofStep2 = (ApplicationTerm) d[0].getValue();
		
		Term[] parametersOfFirst = proofStep1.getParameters();
		Term[] parametersOfSecond = proofStep2.getParameters();
		
		Term[] resultingParameters = new Term[2];
		resultingParameters[0] = parametersOfFirst[0];
		resultingParameters[1] = parametersOfSecond[1];
		
		
		Term resultingProof = a.getTheory().term("=", resultingParameters);
		
		Annotation[] e = new Annotation[1];
		e[0] = new Annotation(":trans", resultingProof);
		
		AnnotatedTerm result = (AnnotatedTerm) a.getTheory().annotatedTerm(e, b);
		
		return result;
	}

	@Override
	public Term congruence(Term a, Term[] b) {
		// TODO Auto-generated method stub
		return null;
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

	@Override
	public Term getTerm(Term t) {
		return ((AnnotatedTerm) t).getSubterm();
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


}
