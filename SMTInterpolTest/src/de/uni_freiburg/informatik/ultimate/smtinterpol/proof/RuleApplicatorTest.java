/**
 * 
 */
package de.uni_freiburg.informatik.ultimate.smtinterpol.proof;

import org.apache.log4j.Logger;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.JUnit4;

import de.uni_freiburg.informatik.ultimate.logic.Logics;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.Theory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.smtlib2.SMTInterpol;
import de.uni_freiburg.informatik.ultimate.smtinterpol.util.TestCaseWithLogger;

/**
 * @author Markus
 *
 */
@RunWith(JUnit4.class)
public class RuleApplicatorTest extends TestCaseWithLogger{
	
	Script mSolver;
	Term mReflA;
	
	public RuleApplicatorTest(){
		mSolver = new SMTInterpol(Logger.getRootLogger());
		mSolver.setOption(":produce-proofs", Boolean.TRUE);
		mSolver.setLogic(Logics.QF_UFLIA);
		Sort[] empty = {};
		mSolver.declareFun("a", empty, mSolver.sort("Int"));
		
		Term a = mSolver.term("a");
		RuleApplicator ruleApplicator = new RuleApplicator();
		mReflA = ruleApplicator.reflexivity(a);
	}
	
	
	
	@Test
	public void annotatedTerm(){
		System.out.println(mReflA.toString());
		
	}

}
