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
package de.uni_freiburg.informatik.ultimate.logic;

import java.util.Arrays;

import org.junit.Test;

import de.uni_freiburg.informatik.ultimate.logic.FormulaUnLet;
import de.uni_freiburg.informatik.ultimate.logic.FormulaUnLet.UnletType;
import de.uni_freiburg.informatik.ultimate.logic.FunctionSymbol;
import de.uni_freiburg.informatik.ultimate.logic.LetTerm;
import de.uni_freiburg.informatik.ultimate.logic.Logics;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.logic.Theory;
import junit.framework.TestCase;

public class UnfletTest extends TestCase {
	
	Theory mTheory = new Theory(Logics.AUFLIRA);
	
	Sort mIntSort = mTheory.getSort("Int");
	Sort[] mInt2 = arr(mIntSort, mIntSort);
	TermVariable mX = mTheory.createTermVariable("x", mIntSort);
	TermVariable mY = mTheory.createTermVariable("y", mIntSort);
	TermVariable mZ = mTheory.createTermVariable("z", mIntSort);
	
	Term mNum1 = mTheory.numeral("1");
	Term mNum2 = mTheory.numeral("2");
	FunctionSymbol mPlus = mTheory.getFunction("+", mInt2); 
	
	Term mSublet = mTheory.let(mX, mNum1, mX);

	FormulaUnLet mUnletter = new FormulaUnLet();
	FormulaUnLet mUnletterLazy = new FormulaUnLet(UnletType.LAZY);
	FormulaUnLet mUnletterExpand =
			new FormulaUnLet(UnletType.EXPAND_DEFINITIONS);
	
	@SafeVarargs
	private final <E> E[] arr(E... vals) { return vals; }
	
	@Test
	public void test() {
		Term letTerm = mTheory.let(arr(mX, mY), arr(mNum1, mNum2),
				mTheory.term(mPlus, mX, mY));
		assertEquals("(let ((x 1) (y 2)) (+ x y))", letTerm.toStringDirect());
		assertEquals("(+ 1 2)", mUnletter.unlet(letTerm).toStringDirect());
	}
	
	@Test
	public void testScope() {
		Term letTerm = mTheory.let(mX, mNum2, 
				mTheory.term(mPlus, mTheory.let(mX, mNum1, mX), mX));
		assertEquals("(let ((x 2)) (+ (let ((x 1)) x) x))",
				letTerm.toStringDirect());
		assertEquals("(+ 1 2)",
				mUnletter.unlet(letTerm).toStringDirect());
		assertEquals("(+ 1 x)",
				mUnletter.unlet(((LetTerm) letTerm).getSubTerm()).
					toStringDirect());
		assertTrue(Arrays.equals(new TermVariable[] {mX}, 
				mUnletter.unlet(((LetTerm) letTerm).getSubTerm()).
					getFreeVars()));
		
		letTerm = mTheory.let(arr(mX, mY), arr(mY, mX),
				mTheory.term(mPlus, mX, mY));
		assertEquals("(let ((x y) (y x)) (+ x y))", letTerm.toStringDirect());
		assertEquals("(+ y x)", mUnletter.unlet(letTerm).toStringDirect());

		letTerm = mTheory.let(mX, mY,
				mTheory.let(mY, mX, mTheory.term(mPlus, mX, mY)));
		assertEquals("(let ((x y)) (let ((y x)) (+ x y)))",
				letTerm.toStringDirect());
		assertEquals("(+ y y)", mUnletter.unlet(letTerm).toStringDirect());
		// This test is broken: the lazy semantics would require non-termination
		//assertEquals("(+ x y)", unletterLazy.unlet(letTerm).toStringDirect());
	}
	
	@Test
	public void testLazy() {
		Term letTerm = mTheory.let(mX, mY, mTheory.let(mY, mNum1, mX));
		assertEquals("(let ((x y)) (let ((y 1)) x))", letTerm.toStringDirect());
		assertEquals("y", mUnletter.unlet(letTerm).toStringDirect());
		assertEquals("1", mUnletterLazy.unlet(letTerm).toStringDirect());
	}
	
	@Test
	public void testQuant() {
		Term letTerm = mTheory.let(mX, mY,
				mTheory.exists(arr(mX), mTheory.equals(mX, mY)));
		assertEquals("(let ((x y)) (exists ((x Int)) (= x y)))", 
				letTerm.toStringDirect());
		assertEquals("(exists ((x Int)) (= x y))", 
				mUnletter.unlet(letTerm).toStringDirect());

		letTerm = mTheory.let(arr(mX,mY), arr(mY,mZ), 
				mTheory.exists(arr(mX), mTheory.equals(mX, mY)));
		assertEquals("(let ((x y) (y z)) (exists ((x Int)) (= x y)))", 
				letTerm.toStringDirect());
		assertEquals("(exists ((x Int)) (= x z))", 
				mUnletter.unlet(letTerm).toStringDirect());
	
		letTerm = mTheory.let(mY, mX,
				mTheory.exists(arr(mX), mTheory.equals(mX, mY)));
		assertEquals("(let ((y x)) (exists ((x Int)) (= x y)))", 
				letTerm.toStringDirect());
		assertEquals("(exists ((.unlet.0 Int)) (= .unlet.0 x))", 
				mUnletter.unlet(letTerm).toStringDirect());

		letTerm = mTheory.let(arr(mX,mY), arr(mY,mZ), 
				mTheory.exists(arr(mY), mTheory.equals(mX, mY)));
		assertEquals("(let ((x y) (y z)) (exists ((y Int)) (= x y)))", 
				letTerm.toStringDirect());
		Term unlet = mUnletter.unlet(letTerm);
		String varname =
				((QuantifiedFormula) unlet).getVariables()[0].toStringDirect();
		assertEquals(".unlet.", varname.substring(0, 7));// NOCHECKSTYLE
		assertEquals("(exists ((" + varname + " Int)) (= y " + varname + "))", 
				unlet.toStringDirect());
	}

	@Test
	public void testAnnotation() {
		Term letTerm = mTheory.let(mX, mY, 
				mTheory.annotatedTerm(
						arr(new Annotation(":named", "foo")), mX));
		assertEquals("(let ((x y)) (! x :named foo))", 
				letTerm.toStringDirect());
		assertEquals("(! y :named foo)", 
				mUnletter.unlet(letTerm).toStringDirect());
		
		letTerm = mTheory.let(mX, mZ, 
				mTheory.exists(arr(mY), 
					mTheory.annotatedTerm(
							arr(new Annotation(":pattern",
									mTheory.term(mPlus, mX, mY))), 
							mTheory.equals(
									mTheory.term(mPlus, mX, mY), mNum2))));
		assertEquals("(let ((x z)) (exists ((y Int)) (! (= (+ x y) 2) :pattern (+ x y))))",// NOCHECKSTYLE 
				letTerm.toStringDirect());
		assertEquals("(exists ((y Int)) (! (= (+ z y) 2) :pattern (+ z y)))", 
				mUnletter.unlet(letTerm).toStringDirect());

		letTerm = mTheory.let(mX, mZ, 
				mTheory.exists(arr(mY), 
					mTheory.annotatedTerm(arr(new Annotation(":pattern", 
							arr(mTheory.term(mPlus, mX, mY),
									mTheory.term(mPlus, mY, mX)))), 
							mTheory.equals(
									mTheory.term(mPlus, mX, mY), mNum2))));
		assertEquals("(let ((x z)) (exists ((y Int)) (! (= (+ x y) 2) :pattern ((+ x y) (+ y x)))))",// NOCHECKSTYLE 
				letTerm.toStringDirect());
		assertEquals("(exists ((y Int)) (! (= (+ z y) 2) :pattern ((+ z y) (+ y z))))", // NOCHECKSTYLE
				mUnletter.unlet(letTerm).toStringDirect());
	}

	@Test
	public void testCache() {
		Term[] deepTerm = new Term[100];// NOCHECKSTYLE
		deepTerm[0] = mX;
		for (int i = 1; i < 100; i++)// NOCHECKSTYLE
			deepTerm[i] = mTheory.term(mPlus, deepTerm[i - 1], deepTerm[i - 1]);
		int depth = 0;
		Term unlet = mUnletter.unlet(mTheory.let(mX, mY, deepTerm[99]));// NOCHECKSTYLE
		// do not even think of calling toStringDirect here...
		while ((unlet instanceof ApplicationTerm)) {
			ApplicationTerm app = (ApplicationTerm) unlet; 
			assertEquals(mPlus, app.getFunction());
			assertEquals(app.getParameters()[0], app.getParameters()[1]);
			unlet = app.getParameters()[0];
			depth++;
		}
		assertEquals(mY, unlet);
		assertEquals(99, depth);// NOCHECKSTYLE

		Term plusxy = mTheory.term(mPlus, mX, mY);
		
		Term letTerm = mTheory.let(mX, mZ, mTheory.equals(
				plusxy, mTheory.let(mX, mY, plusxy)));
		assertEquals("(let ((x z)) (= (+ x y) (let ((x y)) (+ x y))))", 
				letTerm.toStringDirect());
		assertEquals("(= (+ z y) (+ y y))", 
				mUnletter.unlet(letTerm).toStringDirect());
		letTerm = mTheory.equals(mTheory.let(mX, mZ, plusxy),
				mTheory.let(mX, mY, plusxy));
		assertEquals("(= (let ((x z)) (+ x y)) (let ((x y)) (+ x y)))", 
				letTerm.toStringDirect());
		assertEquals("(= (+ z y) (+ y y))", 
				mUnletter.unlet(letTerm).toStringDirect());
		letTerm = mTheory.equals(plusxy, mTheory.let(mX, mY, plusxy));
		assertEquals("(= (+ x y) (let ((x y)) (+ x y)))", 
				letTerm.toStringDirect());
		assertEquals("(= (+ x y) (+ y y))", 
				mUnletter.unlet(letTerm).toStringDirect());
	}
	
	@Test
	public void testExpand() {
		Term def = mTheory.term(mPlus, mX, mY);
		FunctionSymbol plusdef =
				mTheory.defineFunction("plus", arr(mX, mY), def);
		Term defed = mTheory.term(plusdef, mNum1, mNum2);
		assertEquals("(plus 1 2)", defed.toStringDirect());
		assertEquals("(+ 1 2)", mUnletterExpand.unlet(defed).toStringDirect());
	}
}
