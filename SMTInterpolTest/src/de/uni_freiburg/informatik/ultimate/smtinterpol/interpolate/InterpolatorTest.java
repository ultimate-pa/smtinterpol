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
package de.uni_freiburg.informatik.ultimate.smtinterpol.interpolate;

import java.util.Collections;
import java.util.Set;

import org.apache.log4j.Logger;
import org.junit.Assert;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.JUnit4;

import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.smtinterpol.convert.Clausifier;
import de.uni_freiburg.informatik.ultimate.smtinterpol.convert.Clausifier.CCTermBuilder;
import de.uni_freiburg.informatik.ultimate.smtinterpol.convert.EqualityProxy;
import de.uni_freiburg.informatik.ultimate.smtinterpol.convert.SMTAffineTerm;
import de.uni_freiburg.informatik.ultimate.smtinterpol.convert.SharedTerm;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.Clause;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.Literal;
import de.uni_freiburg.informatik.ultimate.smtinterpol.proof.LeafNode;
import de.uni_freiburg.informatik.ultimate.smtinterpol.smtlib2.SMTInterpol;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.cclosure.CCEquality;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.linar.LAEquality;
import de.uni_freiburg.informatik.ultimate.smtinterpol.util.TestCaseWithLogger;

@RunWith(JUnit4.class)
public class InterpolatorTest extends TestCaseWithLogger {
	SMTInterpol mSolver;
	Clausifier mClausifier;
	Interpolator mInterpolator;
	
	Sort mReal;
	Term mA, mB, mS;
	
	public InterpolatorTest() {
		mSolver = new SMTInterpol(Logger.getRootLogger());
		mSolver.setLogic("QF_UFLRA");
		mReal = mSolver.sort("Real");
		mSolver.declareFun("a", new Sort[0], mReal);
		mSolver.declareFun("b", new Sort[0], mReal);
		mSolver.declareFun("s", new Sort[0], mReal);
		mClausifier = mSolver.getClausifier();
		
		mA = mSolver.term("a");
		mB = mSolver.term("b");
		mS = mSolver.term("s");
	}
	
	public void doTestEq(boolean ccswap, boolean abswap, 
			boolean clauseswap, boolean litswap,
			boolean doubleab, boolean addconst, boolean addvar) {
		addvar = false;
		Term a = this.mA;
		Term b = this.mB;
		SharedTerm sa = mClausifier.getSharedTerm(a);
		SharedTerm sb = mClausifier.getSharedTerm(b);
		if (doubleab || addconst || addvar) {
			SMTAffineTerm aterm = SMTAffineTerm.create(a);
			SMTAffineTerm bterm = SMTAffineTerm.create(b);
			if (doubleab) {
				aterm = aterm.mul(Rational.TWO);
				bterm = bterm.mul(Rational.TWO);
			}
			if (addvar) {
				aterm = aterm.add(SMTAffineTerm.create(mS));
				bterm = bterm.add(SMTAffineTerm.create(mS));
			}
			if (addconst) {
				aterm = aterm.add(Rational.TWO);
				bterm = bterm.add(Rational.TWO);
			}
			sa = mClausifier.getSharedTerm(aterm);
			sb = mClausifier.getSharedTerm(bterm);
		}
		CCTermBuilder builder = mClausifier.new CCTermBuilder();
		sa.shareWithLinAr(); builder.convert(sa.getTerm());
		sb.shareWithLinAr(); builder.convert(sb.getTerm());
		EqualityProxy eq = sa.createEquality(sb);
		Assert.assertNotSame(EqualityProxy.getFalseProxy(), eq);
		Assert.assertNotSame(EqualityProxy.getTrueProxy(), eq);
		CCEquality cceq = ccswap
				? eq.createCCEquality(sa, sb) : eq.createCCEquality(sb, sa);
		LAEquality laeq = cceq.getLASharedData();
		Literal[] lits = 
		    clauseswap ? (litswap ? new Literal[] { cceq.negate(), laeq }
		                          : new Literal[] { laeq, cceq.negate() })
	                   : (litswap ? new Literal[] { laeq.negate(), cceq }
	                   			  : new Literal[] { cceq, laeq.negate() });

		Clause clause = new Clause(lits);
		clause.setProof(new LeafNode(LeafNode.EQ, null));
		Set<String> empty = Collections.emptySet();
		@SuppressWarnings("unchecked")
		Set<String>[] partition = new Set[] { empty, empty };
		mInterpolator = 
			new Interpolator(mSolver.getLogger(), mSolver.getTheory(), 
					partition, mClausifier);
		if (abswap) {
			mInterpolator.addOccurrence(sb, 0);
			mInterpolator.addOccurrence(sa, 1);
		} else {
			mInterpolator.addOccurrence(sa, 0);
			mInterpolator.addOccurrence(sb, 1);
		}
		Interpolant[] interpolants = mInterpolator.interpolate(clause);
		TermVariable ccVar = mInterpolator.getLiteralInfo(cceq).getMixedVar();
		TermVariable laVar = mInterpolator.getLiteralInfo(laeq).getMixedVar();
		Term var;
		InterpolatorAffineTerm summands = new InterpolatorAffineTerm();
		if (clauseswap) {
			Rational factor = Rational.ONE;
			if (doubleab)
				factor = Rational.TWO.inverse();
			if (abswap)
				factor = factor.negate();

			summands.add(factor, ccVar);
			if (addvar)
				summands.add(factor.negate(), mSolver.term("s"));
			if (addconst) {
				Rational offset = factor.mul(Rational.TWO).negate();
				summands.add(offset);
			}
			var = laVar;
		} else {
			Rational factor = Rational.ONE;
			if (doubleab)
				factor = Rational.TWO;
			if (abswap)
				factor = factor.negate();
			if (addvar)
				summands.add(Rational.ONE, mSolver.term("s"));
			summands.add(factor, laVar);
			if (addconst) {
				Rational offset = Rational.TWO;
				summands.add(offset);
			}
			var = ccVar;
		}
		Term rhs = summands.toSMTLib(mSolver.getTheory(), false);
		Term expected = mSolver.term("=", var, rhs);
		Assert.assertSame(expected, interpolants[0].mTerm);
	}

	@Test
	public void testEq() {
		for (int i = 0; i < 128; i++)// NOCHECKSTYLE
			doTestEq((i&1) != 0, (i&2) != 0, (i&4) != 0, (i&8) != 0,// NOCHECKSTYLE
					(i&16) != 0, (i&32) != 0, (i& 64) != 0);// NOCHECKSTYLE
	}
	
}
