/**
 * 
 */
package de.uni_freiburg.informatik.ultimate.smtinterpol.proof;

import org.apache.log4j.Logger;
import org.junit.Assert;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.JUnit4;

import de.uni_freiburg.informatik.ultimate.logic.AnnotatedTerm;
import de.uni_freiburg.informatik.ultimate.logic.Annotation;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.ConstantTerm;
import de.uni_freiburg.informatik.ultimate.logic.FunctionSymbol;
import de.uni_freiburg.informatik.ultimate.logic.Logics;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.Theory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.convert.SMTAffineTerm;
import de.uni_freiburg.informatik.ultimate.smtinterpol.smtlib2.SMTInterpol;
import de.uni_freiburg.informatik.ultimate.smtinterpol.util.TestCaseWithLogger;

/**
 * @author Markus
 *
 */
@RunWith(JUnit4.class)
public class RuleApplicatorTest extends TestCaseWithLogger{
	
	private final Script mSolver;
	private final Term mA, mB, mC, mD, mX, mY, mZ;
	private final RuleApplicator mRuleApplicator;
	private final Theory mTheory;
	
	public RuleApplicatorTest(){
		mSolver = new SMTInterpol(Logger.getRootLogger());
		mSolver.setOption(":produce-proofs", Boolean.TRUE);
		mSolver.setLogic(Logics.QF_UFLIRA);
		Sort[] empty = {};
		mSolver.declareFun("a", empty, mSolver.sort("Bool"));
		mSolver.declareFun("b", empty, mSolver.sort("Bool"));
		mSolver.declareFun("c", empty, mSolver.sort("Bool"));
		mSolver.declareFun("d", empty, mSolver.sort("Bool"));
		
		mSolver.declareFun("x", empty, mSolver.sort("Int"));
		mSolver.declareFun("y", empty, mSolver.sort("Int"));
		mSolver.declareFun("z", empty, mSolver.sort("Int"));
		
		mA = mSolver.term("a");
		mB = mSolver.term("b");
		mC = mSolver.term("c");
		mD = mSolver.term("d");
		
		mX = mSolver.term("x");
		mY = mSolver.term("y");
		mZ = mSolver.term("z");
		
		mRuleApplicator = new RuleApplicator();
		
		mTheory = mA.getTheory();
		
	}
	
	@Test
	public void expand(){
		//Term orig = mTheory.and(mA, mB, mC);
		//Term expanded = mTheory.and(mTheory.and(mA, mB), mC);
		//Term result = mRuleApplicator.expand((ApplicationTerm) orig, expanded);
		System.out.println("expand");
		//System.out.println("Orig term: " + orig);
		//System.out.println("Expanded term: " + expanded);
		//System.out.println("Result term: " + result);
		System.out.println();
	}
	
	@Test
	public void expandDef(){
		Term result = mRuleApplicator.expandDef(mA, mB);
		System.out.println("expandDef");
		System.out.println("Term: " + mA);
		System.out.println("Expanded term: " + mB);
		System.out.println("Result term: " + result);
		System.out.println();
	}
	
	@Test
	public void equality(){
		Term[] args = new Term[2];
		args[0] = mA;
		args[1] = mA;
		int rule = ProofConstants.RW_EQ_SIMP;
		Term result = mRuleApplicator.equality(args, mA, rule);
		System.out.println("equality");
		for (int i = 0; i < args.length; i++) {
			System.out.println("InputTerm at position " + i + ": " + args[i]);
		}
		System.out.println("OutputTerm: " + mA);
		System.out.println("Result term: " + result);
		System.out.println();
	}
	
	@Test
	public void distinct(){
		Term[] args = new Term[2];
		args[0] = mA;
		args[1] = mSolver.term("true");
		int rule = ProofConstants.RW_DISTINCT_TRUE;
		Term result = mRuleApplicator.distinct(args, mTheory.term(mTheory.mNot,
				args[0]), rule);
		System.out.println("distinct");
		for (int i = 0; i < args.length; i++) {
			System.out.println("InputTerm at position " + i + ": " + args[i]);
		}
		System.out.println("OutputTerm: " + mSolver.term("not", args[0]));
		System.out.println("Result term: " + result);
		Assert.assertEquals("(! (not a) :proof (@rewrite (! (= (distinct a true) (not a)) :distinct)))", result.toString());
		System.out.println();
	}
	
	@Test
	public void distinctBoolEq(){
		Term result = mRuleApplicator.distinctBoolEq(mA, mB, true);
		System.out.println("distinctBoolEq");
		System.out.println("Result term: " + result);
		System.out.println();
	}
	
	@Test
	public void negation(){
		Term resultNegation = mRuleApplicator.negation(mA, mSolver.term("not", mA),
				ProofConstants.RW_NOT_SIMP);
		System.out.println("negation");
		System.out.println("Result: " + resultNegation.toString());
		System.out.println();
		
	}
	
	@Test
	public void or(){
		Term[] args = new Term[2];
		args[0] = mA;
		args[1] = mA;
		int rule = ProofConstants.RW_OR_SIMP;
		Term result = mRuleApplicator.or(args, mA, rule);
		System.out.println("or");
		for (int i = 0; i < args.length; i++) {
			System.out.println("InputTerm at position " + i + ": " + args[i]);
		}
		System.out.println("OutputTerm: " + mA);
		System.out.println("Result term: " + result);
		System.out.println();
	}
	
	@Test
	public void ite(){
		int rule = ProofConstants.RW_ITE_BOOL_2;
		Term result = mRuleApplicator.ite(mA, mTheory.mFalse, mTheory.mTrue,
				mTheory.term(mTheory.mNot, mA), rule);
		System.out.println("ite");
		System.out.println("cond: " + mA);
		System.out.println("then: " + mTheory.mFalse);
		System.out.println("else: " + mTheory.mTrue);
		System.out.println("Result term: " + result);
		System.out.println();
	}
	
	@Test
	public void removeConnective(){
		
	}
	
	@Test
	public void strip(){
		Annotation[] someAnnotaion = new Annotation[1];
		someAnnotaion[0] = new Annotation(":someAnnotaion", null);
		
		AnnotatedTerm annotatedTerm = (AnnotatedTerm) mTheory.annotatedTerm(
				someAnnotaion, mA);
		
		System.out.println("strip");
		System.out.println("Input: " + annotatedTerm);
				
		Term result = mRuleApplicator.strip(annotatedTerm);
		System.out.println("Result term: " + result);
		System.out.println();
	}
	
	@Test
	public void sum(){
		Term[] args = new Term[2];
		args[0] = mX;
		args[1] = mY;
		
		Term left = mTheory.term("+", args);
		Term right = mZ;
		ApplicationTerm appTerm = (ApplicationTerm) left;
		FunctionSymbol fsym = appTerm.getFunction();
		System.out.println("sum");
		Term result = mRuleApplicator.sum(fsym, args, right);
		
		for (int i = 0; i < args.length; i++) {
			System.out.println("InputTerm at position " + i + ": " + args[i]);
		}
		System.out.println("OutputTerm: " + right);
		System.out.println("Result term: " + result);
		System.out.println();
		
		
		Term right1 = left;
		System.out.println("sum");
		Term result1 = mRuleApplicator.sum(fsym, args, right1);
		
		for (int i = 0; i < args.length; i++) {
			System.out.println("InputTerm at position " + i + ": " + args[i]);
		}
		System.out.println("OutputTerm: " + right1);
		System.out.println("Result term: " + result1);
		System.out.println();
	}
	
	@Test
	public void normalized(){
		SMTAffineTerm term = SMTAffineTerm.create(mX);
		ConstantTerm cTerm = (ConstantTerm) mTheory.constant(1, mTheory.getSort("Int"));
		System.out.println("normalized");
		Term result = mRuleApplicator.normalized(cTerm, term);
		
		System.out.println("Result term: " + result);
		System.out.println();
	}
	
	@Test
	public void toLeq0(){
		Term[] args = new Term[2];
		args[0] = mX;
		args[1] = mY;
		
		Term orig = mTheory.term("<=", args);
		SMTAffineTerm smtAterm = SMTAffineTerm.create(mX);
		int rule = ProofConstants.RW_LEQ_TO_LEQ0;
		Term result = mRuleApplicator.toLeq0(orig, smtAterm, rule);
		// TODO: korrektheit
		System.out.println("toLeq0");
		System.out.println("Term orig: " + orig);
		System.out.println("SMTAffineTerm: "+ smtAterm);
		System.out.println("Result: " + result);
		System.out.println();
		
		
	}
	
	@Test
	public void leqSimp(){
		Term[] args = new Term[2];
		args[0] = mX;
		args[1] = mY;
		
		Term res = mTheory.term("<=", args);
		SMTAffineTerm smtAterm = SMTAffineTerm.create(mX);
		int rule = ProofConstants.RW_LEQ_TO_LEQ0;
		Term result = mRuleApplicator.leqSimp(smtAterm, res, rule);
		// TODO: korrektheit
		System.out.println("leqSimp");
		System.out.println("SMTAffineTerm: "+ smtAterm);
		System.out.println("res: "+ res);
		System.out.println("Result: " + result);
		System.out.println();
	}
	
	@Test
	public void desugar(){
		ConstantTerm cTerm = (ConstantTerm) mTheory.constant(1, mTheory.getSort("Int"));
		// TODO: sort real funktioniert nicht
		ConstantTerm cTerm1 = (ConstantTerm) mTheory.constant(3.0, mTheory.getSort("Int"));
		ConstantTerm cTerm2 = (ConstantTerm) mTheory.constant(1.0, mTheory.getSort("Int"));
		Term[] args = new Term[2];
		args[0] = cTerm;
		args[1] = cTerm1;
		
		Term[] origArgs = new Term[2];
		origArgs[0] = cTerm;
		origArgs[1] = cTerm1;
		
		Term[] newArgs = new Term[2];
		newArgs[0] = cTerm2;
		newArgs[1] = cTerm1;
		
		
		ApplicationTerm orig = mTheory.term("<=", args);
		System.out.println("desugar");
		Term result = mRuleApplicator.desugar(orig, origArgs, newArgs);
		
		System.out.println("Result term: " + result);
		System.out.println();
	}
	
	@Test
	public void modulo(){
		Term[] args = new Term[2];
		args[0] = mX;
		args[1] = mY;
		ApplicationTerm appTerm = mTheory.term("mod", args);
		Term res = mTheory.term("+", mX, mTheory.term("*", mTheory.term("-", mY)
				, mTheory.term("div", mX, mY)));
		
		
		Term result = mRuleApplicator.modulo(appTerm, res);
		System.out.println("modulo");
		System.out.println("appTerm: " + appTerm);
		System.out.println("res: " + res);
		System.out.println("Result: " + result);
		System.out.println();
		
	}
	
	@Test
	public void mod(){
		Term[] args = new Term[2];
		args[0] = mX;
		args[1] = mY;
		ApplicationTerm res = mTheory.term("mod", args);
		int rule = ProofConstants.RW_MODULO;
		Term result = mRuleApplicator.mod(mX, mY, res, rule);
		System.out.println("mod");
		System.out.println("Term x: " + mX);
		System.out.println("Term y: " + mY);
		System.out.println("Term res: " + res);
		System.out.println("Result: " + result);
		System.out.println();
		
	}
	
	@Test
	public void div(){
		ApplicationTerm res = mTheory.term("div", mX, mY);
		int rule = ProofConstants.RW_DIV_MONE;
		Term result = mRuleApplicator.div(mX, mY, res, rule);
		System.out.println("div");
		System.out.println("Term x: " + mX);
		System.out.println("Term y: " + mY);
		System.out.println("Term res: " + res);
		System.out.println("Result: " + result);
		System.out.println();
		
	}
	
	@Test
	public void divisible(){
		ApplicationTerm res = (ApplicationTerm) mTheory.term("div", mX, mY);
		FunctionSymbol fsym = res.getFunction();
		//Term result = mRuleApplicator.divisible(fsym, mX, res);
		System.out.println("divisible");
		System.out.println("FunctionSymbol fsym: " + fsym);
		System.out.println("Term div: " + mX);
		System.out.println("Term res: " + res);
		//System.out.println("Result: " + result);
		System.out.println();
		
	}
	
	@Test
	public void toInt(){
		// TODO: Wie toInt aufrufen
	
	}
	
	@Test
	public void to_real(){
		// TODO: Wie to_real aufrufen
	
	}
	
	@Test
	public void arrayRewrite(){
		//TODO
		mTheory.getSort("Array", mTheory.getSort("Int"), mTheory.getSort("Int"));

		Term[] args = new Term[3];
		args[0] = mA;
		args[1] = mB;
		args[2] = mC;
		//Term[] paras = new Term[3];
		//ApplicationTerm res = mTheory.term("store", args);
		//int rule = ProofConstants.RW_STORE_OVER_STORE;
		//Term result = mRuleApplicator.arrayRewrite(args, res, rule);
		System.out.println("arrayRewrite");
		//System.out.println("Result: " + result);
		System.out.println();
		
	}
	
	@Test
	public void storeRewrite(){
		System.out.println("storeRewrite");
		System.out.println();
		
	}
	
	@Test
	public void quoted(){
		System.out.println("quoted");
		System.out.println();
		
	}
	
	@Test
	public void eq(){
		Term res = mTheory.term("=", mA, mB);
		Term result1 = mRuleApplicator.eq(mB, mC, res);
		Term result2 = mRuleApplicator.eq(mA, mB, res);
		System.out.println("eq");
		System.out.println("Result 1: " + result1);
		System.out.println("Result 2: " + result2);
		System.out.println();
		
	}
	
	// TODO: test für überladenes eq
	
	@Test
	public void leq0(){
		System.out.println("leq0");
		System.out.println();
		
	}
	
	@Test
	public void intern(){
		System.out.println("intern");
		System.out.println();
		
	}
	
	@Test
	public void reflexivity(){
		Term result = mRuleApplicator.reflexivity(mA);
		System.out.println("reflexivity");
		System.out.println("Term: " + mA);
		System.out.println("Result: " + result);
		System.out.println();
		
	}
	
	@Test
	public void transitivity(){
		System.out.println("transitivity");
		
		Term statement1 = mTheory.term("=", mA, mB);
		Term statement2 = mTheory.term("=", mB, mC);
		
		Annotation[] someRule = new Annotation[1];
		someRule[0] = new Annotation(":some-rule", null);
		
		Term proofPart1 = (AnnotatedTerm) mTheory.annotatedTerm(someRule,
				statement1);
		
		Annotation[] anotherRule = new Annotation[1];
		anotherRule[0] = new Annotation(":another-rule", null);
		
		Term proofPart2 = (AnnotatedTerm) mTheory.annotatedTerm(anotherRule,
				statement2);
		
		Term proof1 = mTheory.term("@rewrite", proofPart1);
		Term proof2 = mTheory.term("@rewrite", proofPart2);
		
		Annotation[] f = new Annotation[1];
		f[0] = new Annotation(":proof", proof1);
		
		Annotation[] g = new Annotation[1];
		g[0] = new Annotation(":proof", proof2);
		
		Term t1 = (AnnotatedTerm) mTheory.annotatedTerm(f, mB);
		Term t2 = (AnnotatedTerm) mTheory.annotatedTerm(g, mC);
		
		Term result = mRuleApplicator.transitivity(t1, t2);
		
		System.out.println("First term: " + t1);
		System.out.println("Second term: " + t2);
		System.out.println("Result: " + result);
		System.out.println();
	}
	
	@Test
	public void congruence() {
		System.out.println("congruence");
		
		Term[] statementArgs = new Term[2];
		statementArgs[0] = mA;
		statementArgs[1] = mB;
		
		Term t1 = mC;
		Term t2 = mTheory.and(statementArgs);
		
		Term[] args = new Term[2];
		args[0] = t1;
		args[1] = t2;
		// (= c (and a b))
		Term congStatement = mTheory.term("=", args);
		
		Term congProof = mTheory.term("@rewrite", congStatement);
		
		Annotation[] h = new Annotation[1];
		h[0] = new Annotation(":proof", congProof);
		// (! (and a b) :proof (@rewrite (= c (and a b))))
		Term t3 = mTheory.annotatedTerm(h, t2);
		
		Term[] parameters = new Term[2];
		parameters[0] = mB;
		parameters[1] = mD;
		
		Term proof1 = mTheory.term("@refl", mA);
		Term statement = mTheory.term("=", parameters);
		
		Annotation[] someRule = new Annotation[1];
		someRule[0] = new Annotation(":some-rule", null);
		
		Annotation[] i = new Annotation[1];
		i[0] = new Annotation(":proof", proof1);
		
		// (! a :proof (@refl a))
		Term t4 = mTheory.annotatedTerm(i, mA);
		// (! (= b d) :some-rule)
		Term t5 = mTheory.annotatedTerm(someRule, statement);
		
		Term t6 = mTheory.term("@rewrite", t5);
		
		Annotation[] j = new Annotation[1];
		j[0] = new Annotation(":proof", t6);
		//(! d :proof (@rewrite (! (= b d) :some-rule)))
		Term t7 = mTheory.annotatedTerm(j, mD);
		
		Term[] substitutes = new Term[2];
		substitutes[0] = t4;
		substitutes[1] = t7;
		
		Term result = mRuleApplicator.congruence(t3, substitutes);
		System.out.println("First term: " + t3);
		for (int z = 0; z < substitutes.length; z++) {
			System.out.println("Substitutes array position " + z + ": " + 
					substitutes[z]);
		}
		System.out.println("Result: " + result);
		System.out.println();
		
	}

}
