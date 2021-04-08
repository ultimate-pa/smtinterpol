package de.uni_freiburg.informatik.ultimate.smtinterpol.theory.bitvector;

import org.junit.After;
import org.junit.Assert;
import org.junit.Before;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.JUnit4;

import de.uni_freiburg.informatik.ultimate.logic.Logics;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.smtinterpol.DefaultLogger;
import de.uni_freiburg.informatik.ultimate.smtinterpol.smtlib2.SMTInterpol;

/**
 *
 * @author Max Barth
 */
@RunWith(JUnit4.class)
public class BitvectorTest {

	private SMTInterpol mSolver;

	private Term a;
	private Term b;
	private Term c;
	private Term x;
	private Term y;
	private Term z;
	private Term u;
	private Term v;
	private Term w;
	private Term p;
	private Term q;
	private Term p2;
	private Term q2;
	private Term p3;
	private Term q3;
	private Term p4;
	private Term q4;
	private Term p7;
	private Term p8;

	@Before
	public void setUp() throws Exception {
		mSolver = new SMTInterpol(new DefaultLogger());
		mSolver.setOption(":produce-models", Boolean.FALSE);
		mSolver.setLogic(Logics.QF_BV);
		final Sort bv1 = mSolver.getTheory().getSort("BitVec", new String[] { "1" });
		final Sort bv2 = mSolver.getTheory().getSort("BitVec", new String[] { "2" });
		final Sort bv3 = mSolver.getTheory().getSort("BitVec", new String[] { "3" });
		final Sort bv4 = mSolver.getTheory().getSort("BitVec", new String[] { "4" });
		final Sort bv7 = mSolver.getTheory().getSort("BitVec", new String[] { "7" });
		final Sort bv8 = mSolver.getTheory().getSort("BitVec", new String[] { "8" });
		final Sort bv12 = mSolver.getTheory().getSort("BitVec", new String[] { "12" });
		final Sort bv16 = mSolver.getTheory().getSort("BitVec", new String[] { "16" });
		final Sort bv32 = mSolver.getTheory().getSort("BitVec", new String[] { "32" });

		mSolver.declareFun("x", Script.EMPTY_SORT_ARRAY, bv16);
		mSolver.declareFun("y", Script.EMPTY_SORT_ARRAY, bv16);
		mSolver.declareFun("z", Script.EMPTY_SORT_ARRAY, bv16);
		mSolver.declareFun("a", Script.EMPTY_SORT_ARRAY, bv16);
		mSolver.declareFun("b", Script.EMPTY_SORT_ARRAY, bv16);
		mSolver.declareFun("c", Script.EMPTY_SORT_ARRAY, bv16);

		mSolver.declareFun("u", Script.EMPTY_SORT_ARRAY, bv32);
		mSolver.declareFun("v", Script.EMPTY_SORT_ARRAY, bv32);
		mSolver.declareFun("w", Script.EMPTY_SORT_ARRAY, bv32);

		mSolver.declareFun("p", Script.EMPTY_SORT_ARRAY, bv1);
		mSolver.declareFun("q", Script.EMPTY_SORT_ARRAY, bv1);
		mSolver.declareFun("p2", Script.EMPTY_SORT_ARRAY, bv2);
		mSolver.declareFun("q2", Script.EMPTY_SORT_ARRAY, bv2);
		mSolver.declareFun("p3", Script.EMPTY_SORT_ARRAY, bv3);
		mSolver.declareFun("q3", Script.EMPTY_SORT_ARRAY, bv3);
		mSolver.declareFun("p4", Script.EMPTY_SORT_ARRAY, bv4);
		mSolver.declareFun("q4", Script.EMPTY_SORT_ARRAY, bv4);
		mSolver.declareFun("p8", Script.EMPTY_SORT_ARRAY, bv8);
		mSolver.declareFun("p7", Script.EMPTY_SORT_ARRAY, bv7);

		x = mSolver.term("x");
		y = mSolver.term("y");
		z = mSolver.term("z");
		a = mSolver.term("a");
		b = mSolver.term("b");
		c = mSolver.term("c");

		u = mSolver.term("u");
		v = mSolver.term("v");
		w = mSolver.term("w");

		p = mSolver.term("p");
		q = mSolver.term("q");
		p2 = mSolver.term("p2");
		q2 = mSolver.term("q2");
		p3 = mSolver.term("p3");
		q3 = mSolver.term("q3");
		p4 = mSolver.term("p4");
		q4 = mSolver.term("q4");
		p7 = mSolver.term("p7");
		p8 = mSolver.term("p8");

	}

	@After
	public void tearDown() throws Exception {
		mSolver.exit();
		mSolver = null;
	}

	@Test
	public void select() {
		mSolver.resetAssertions();
		// final Term consTerm = mSolver.term("(_ bv 4 4)");
		final String[] asd = new String[2];
		asd[0] = "7";
		asd[1] = "5";
		final Term consTerm1 = mSolver.binary("#b00100000");
		final Term consTerm2 = mSolver.binary("#b00100010");
		final Term term1 = mSolver.term("extract", asd, null, consTerm1);
		final Term term2 = mSolver.term("extract", asd, null, consTerm2);
		final Term input = mSolver.term("=", term1, term2);
		mSolver.assertTerm(input);
		final LBool isSat = mSolver.checkSat();
		Assert.assertSame(LBool.SAT, isSat);
	}

	@Test
	public void selectPropagation() {
		mSolver.resetAssertions();
		final String[] idx = new String[2];
		idx[0] = "5";
		idx[1] = "3";
		final Term consTerm1 = mSolver.binary("#b1111");
		final Term consTerm2 = mSolver.binary("#b0000");
		final Term term1 = mSolver.term("extract", idx, null, mSolver.term("concat", consTerm1, consTerm2));
		final Term input1 = mSolver.term("=", term1, p3);
		mSolver.assertTerm(input1);
		final String[] idx2 = new String[2];
		idx2[0] = "5";
		idx2[1] = "2";
		final String[] idx3 = new String[2];
		idx3[0] = "2";
		idx3[1] = "1";
		final Term term2 =
				mSolver.term("extract", idx3, null, mSolver.term("extract", idx2, null, mSolver.binary("#b0100100")));
		final Term input2 = mSolver.term("=", term2, p2);
		mSolver.assertTerm(input2);
		final LBool isSat = mSolver.checkSat();
		Assert.assertSame(LBool.SAT, isSat);
	}

	@Test
	public void bvConstPatter() {
		mSolver.resetAssertions();
		// final Term consTerm = mSolver.term("(_ bv 4 4)");
		final String[] asd = new String[2];
		asd[0] = "2";
		asd[1] = "1";
		final String[] constindices = new String[1];
		constindices[0] = "4";
		// final FunctionSymbol fs = mSolver.getTheory().getFunctionWithResult("bv", constindices, null, null);
		final Term consTerm = mSolver.term("bv3", constindices, null);
		final Term consTerm2 = mSolver.binary("#b0011");
		final Term input = mSolver.term("=", consTerm, consTerm2);
		mSolver.assertTerm(input);
		final LBool isSat = mSolver.checkSat();
		Assert.assertSame(LBool.SAT, isSat);

	}

	@Test
	public void shiftConst() {
		// {bvshl, bvlshr}
		mSolver.resetAssertions();
		final Term consTerm = mSolver.binary("#b1001");
		// mSolver.getTheory().getFunctionWithResult("(_ bv 4 4)");
		final String[] asd = new String[2];
		asd[0] = "1";
		asd[1] = "1";
		final Term result = mSolver.term("extract", asd, null, consTerm);
		System.out.println(result.getSort().getIndexedName());

		final Term consTerm2 = mSolver.binary("#b0010");
		final Term consTerm3 = mSolver.binary("#b0100");

		final Term input = mSolver.term("and",
				mSolver.term("=", mSolver.term("bvshl", consTerm, consTerm2), consTerm3),
				mSolver.term("=", mSolver.term("bvlshr", consTerm, consTerm2), consTerm2),
				mSolver.term("=", mSolver.term("bvshl", mSolver.binary("#b00110011"), mSolver.binary("#b00000010")),
						mSolver.binary("#b11001100")),
				mSolver.term("=", mSolver.term("bvlshr", mSolver.binary("#b00110011"), mSolver.binary("#b00000010")),
						mSolver.binary("#b00001100")));

		mSolver.assertTerm(input);
		final LBool isSat = mSolver.checkSat();
		Assert.assertSame(LBool.SAT, isSat);

	}

	@Test
	public void functionConst() {
		// {bvand, bvor, bvadd, bvmul, bvudiv, bvurem}
		mSolver.resetAssertions();

		final Term consTerm = mSolver.binary("#b0001");
		final Term consTerm2 = mSolver.binary("#b0010"); // "(_ bv2 4)"
		final Term consTerm3 = mSolver.hexadecimal("#x3");
		final Term input = mSolver.term("and",
				mSolver.term("=", mSolver.term("bvadd", consTerm, consTerm), consTerm2),
				mSolver.term("=", mSolver.term("bvmul", consTerm, consTerm), consTerm),
				mSolver.term("=", mSolver.term("bvudiv", consTerm2, consTerm), consTerm2),
				mSolver.term("=", mSolver.term("concat", consTerm, mSolver.term("bvadd", consTerm2, consTerm)),
						mSolver.term("concat", consTerm, consTerm3)),
				mSolver.term("=", mSolver.term("bvand", consTerm2, consTerm3), consTerm2),
				mSolver.term("=", mSolver.term("bvor", consTerm, consTerm2), consTerm3),
				mSolver.term("=", mSolver.term("bvurem", consTerm3, consTerm2), consTerm),
				mSolver.term("=", mSolver.term("bvnot", consTerm3), consTerm),
				mSolver.term("=", mSolver.term("bvneg", consTerm), consTerm)
				);
		mSolver.assertTerm(input);
		final LBool isSat = mSolver.checkSat();
		Assert.assertSame(LBool.UNSAT, isSat);

	}

	@Test
	public void bvultTransitivity() {
		mSolver.resetAssertions();
		final Term consTerm = mSolver.binary("#b0001");

		final Term consTerm1 = mSolver.binary("#b1001");
		final Term input =
				mSolver.term("and",
						mSolver.term("bvult", consTerm, q4),
						mSolver.term("bvult", q2, p2),
						mSolver.term("or",
								mSolver.term("bvult", q4, p4), mSolver.term("bvult", q4, consTerm)));
		mSolver.assertTerm(input);
		final LBool isunSat = mSolver.checkSat();
		Assert.assertSame(LBool.SAT, isunSat);
	}

	@Test
	public void relationConst1() {
		mSolver.resetAssertions();
		final Term consTerm = mSolver.binary("#b0001");
		final Term consTerm1 = mSolver.binary("#b1001");
		final Term input =
				mSolver.term("and",
						mSolver.term("=", consTerm, consTerm),
						mSolver.term("bvult", consTerm, consTerm1),
						mSolver.term("bvule", consTerm, consTerm),
						mSolver.term("bvugt", consTerm1, consTerm),
						mSolver.term("bvuge", consTerm, consTerm));
		mSolver.assertTerm(input);
		final LBool isunSat = mSolver.checkSat();
		Assert.assertSame(LBool.SAT, isunSat);
	}

	@Test
	public void relationConst2() {
		mSolver.resetAssertions();
		final String[] constindices = new String[1];
		constindices[0] = "4";
		// final FunctionSymbol fs = mSolver.getTheory().getFunctionWithResult("bv", constindices, null, null);
		final Term consTerm = mSolver.term("bv3", constindices, null);
		final Term consTerm1 = mSolver.term("bv4", constindices, null);
		final Term input =
				mSolver.term("and",
						mSolver.term("bvslt", consTerm1, consTerm),
						mSolver.term("bvsle", consTerm, consTerm),
						mSolver.term("bvsgt", consTerm, consTerm1));
		mSolver.assertTerm(input);
		final LBool isunSat = mSolver.checkSat();
		Assert.assertSame(LBool.UNSAT, isunSat);
	}


	@Test
	public void relationConst3() {
		mSolver.resetAssertions();
		final Term consTerm = mSolver.binary("#b0001");
		final Term consTerm1 = mSolver.binary("#b1001");
		final Term input =
				mSolver.term("and",
						mSolver.term("bvslt", consTerm1, consTerm),
						mSolver.term("bvsle", p4, p4),
						mSolver.term("bvsgt", consTerm, consTerm1));
		// mSolver.term("bvsge", consTerm, consTerm);
		mSolver.assertTerm(input);
		final LBool isunSat = mSolver.checkSat();
		Assert.assertSame(LBool.SAT, isunSat);
	}

	@Test
	public void relationSignedConst() {
		mSolver.resetAssertions();
		final Term consTerm = mSolver.binary("#b0001");
		final Term input =
				mSolver.term("bvslt", consTerm, consTerm);
		mSolver.assertTerm(input);
		final LBool isunSat = mSolver.checkSat();
		Assert.assertSame(LBool.UNSAT, isunSat);
	}
	@Test
	public void divZero() {
		final Term consTerm15 = mSolver.hexadecimal("#xF");
		final Term consTerm0 = mSolver.binary("#b0000");
		final Term consTerm3 = mSolver.binary("#b0011");
		mSolver.resetAssertions();
		final Term input = mSolver.term("=", mSolver.term("bvudiv", consTerm3, consTerm0), consTerm15);
		mSolver.assertTerm(input);
		final LBool isSat = mSolver.checkSat();
		Assert.assertSame(LBool.SAT, isSat);
	}

	@Test
	public void bitVecDivSat1() {
		final Term consTerm0 = mSolver.binary("#b0");
		final Term consTerm3 = mSolver.binary("#b1");
		mSolver.resetAssertions();
		final Term input = mSolver.term("and",
				mSolver.term("=", mSolver.term("bvudiv", consTerm3, p), consTerm0),
				mSolver.term("=", consTerm3, p));
		mSolver.assertTerm(input);
		final LBool isSat = mSolver.checkSat();
		Assert.assertSame(LBool.UNSAT, isSat);
	}

	@Test
	public void bitVecDivUNSat1() {
		mSolver.resetAssertions();
		final Term input = mSolver.term("and",
				mSolver.term("=", mSolver.term("bvudiv", mSolver.binary("#b100"), p3), mSolver.binary("#b010")),
				mSolver.term("=", mSolver.binary("#b001"), p3));
		mSolver.assertTerm(input);
		final LBool isSat = mSolver.checkSat();
		Assert.assertSame(LBool.UNSAT, isSat);
	}

	@Test
	public void bitVecRemSat1() {
		mSolver.resetAssertions();
		final Term input = mSolver.term("and",
				mSolver.term("=", mSolver.term("bvurem", mSolver.binary("#b101"), p3), mSolver.binary("#b001")),
				mSolver.term("=", mSolver.binary("#b010"), p3));
		mSolver.assertTerm(input);
		final LBool isSat = mSolver.checkSat();
		Assert.assertSame(LBool.SAT, isSat);
	}

	@Test
	public void bitVecRemUNSat1() {
		mSolver.resetAssertions();
		final Term input = mSolver.term("and",
				mSolver.term("=", mSolver.term("bvurem", mSolver.binary("#b100"), p3), mSolver.binary("#b001")),
				mSolver.term("=", mSolver.binary("#b010"), p3));
		mSolver.assertTerm(input);
		final LBool isSat = mSolver.checkSat();
		Assert.assertSame(LBool.UNSAT, isSat);
	}

	@Test
	public void bitVecCClosureBvult() {
		// x < y::z, ¬(x < w), w = y:: z
		mSolver.resetAssertions();
		final Term input =mSolver.term("and",
				mSolver.term("=", w, mSolver.term("concat", y, z)),
				mSolver.term("not", mSolver.term("bvult", u, w)),
				mSolver.term("bvult", u, mSolver.term("concat", y, z))

				);
		mSolver.assertTerm(input);
		final LBool isSat = mSolver.checkSat();
		Assert.assertSame(LBool.UNSAT, isSat);
	}

	@Test
	public void bitVecCClosure() {
		mSolver.resetAssertions();
		final Term input = mSolver.term("and",
				mSolver.term("=", mSolver.term("concat", y, z), w),
				mSolver.term("not", mSolver.term("=", u, w)),
				mSolver.term("=", u, mSolver.term("concat", y, z)));
		mSolver.assertTerm(input);
		final LBool isSat = mSolver.checkSat();
		Assert.assertSame(LBool.UNSAT, isSat);
	}

	// @Test
	public void eqConcatMatch() {
		mSolver.resetAssertions();
		final Term input = mSolver.term("=", mSolver.term("concat", y, z), mSolver.term("concat", x, c),
				mSolver.term("concat", a, b));
		mSolver.assertTerm(input);
		final LBool isSat = mSolver.checkSat();
		Assert.assertSame(LBool.SAT, isSat);
	}

	@Test
	public void eqNoMatch() {
		mSolver.resetAssertions();
		final Term input = mSolver.term("and",
				mSolver.term("=", mSolver.term("concat", p4, q3), p7),
				mSolver.term("=", mSolver.term("concat", p2, q2), mSolver.term("concat", p, q3)));
		mSolver.assertTerm(input);
		final LBool isSat = mSolver.checkSat();
		Assert.assertSame(LBool.SAT, isSat);
	}

	@Test
	public void eqConst() {
		mSolver.resetAssertions();
		final Term input = mSolver.term("and",
				mSolver.term("=", mSolver.binary("#b0001"), mSolver.binary("#b0001"), mSolver.binary("#b0001")),
				mSolver.term("=", mSolver.term("concat", y, z), mSolver.term("concat", y, z)));
		mSolver.assertTerm(input);
		final LBool isSat = mSolver.checkSat();
		Assert.assertSame(LBool.SAT, isSat);
	}

	@Test
	public void concatConstSimp() {
		mSolver.resetAssertions();
		final Term input = mSolver.term("=", mSolver.binary("#b01110100"),
				mSolver.term("concat", mSolver.binary("#b0111"), mSolver.binary("#b0100")));
		mSolver.assertTerm(input);
		final LBool isSat = mSolver.checkSat();
		Assert.assertSame(LBool.SAT, isSat);
	}

	@Test
	public void concatBitBlast() {

		mSolver.resetAssertions();
		final Term input = mSolver.term("and", mSolver.term("=", mSolver.binary("#b01"),
				mSolver.term("concat", p, mSolver.binary("#b1"))),
				mSolver.term("=", p, mSolver.binary("#b1")));
		mSolver.assertTerm(input);
		final LBool isSat = mSolver.checkSat();
		Assert.assertSame(LBool.UNSAT, isSat);
	}

	@Test
	public void extractBitBlast() {
		mSolver.resetAssertions();

		final String[] indices = new String[2];
		indices[0] = "2";
		indices[1] = "1";
		final String[] indices2 = new String[2];
		indices2[0] = "3";
		indices2[1] = "2";
		final String[] indices3 = new String[2];
		indices3[0] = "1";
		indices3[1] = "0";
		final Term input =
				mSolver.term("and", mSolver.term("=", p2,
						mSolver.term("extract", indices3, null, p4)),
						mSolver.term("=", mSolver.term("extract", indices, null, p4),
								mSolver.term("extract", indices3, null, p4)),
						mSolver.term("=", mSolver.term("extract", indices, null, p4),
								mSolver.term("extract", indices2, null, p4)));

		mSolver.assertTerm(input);
		final LBool isSat = mSolver.checkSat();
		Assert.assertSame(LBool.SAT, isSat);
	}

	@Test
	public void bitVecLayerOne() {
		// x < y::z, ¬(x < w), w = y:: z
		mSolver.resetAssertions();
		final Term input = mSolver.term("and", mSolver.term("bvult", u, mSolver.term("concat", y, z)),
				mSolver.term("=", mSolver.term("concat", y, z), w), mSolver.term("not", mSolver.term("bvult", u, w)));
		mSolver.assertTerm(input);
		final LBool isUnSat = mSolver.checkSat();
		Assert.assertSame(LBool.UNSAT, isUnSat);
	}

	@Test
	public void bitVecLeftShiftSAT() {
		mSolver.resetAssertions();
		final Term input = mSolver.term("=", mSolver.term("bvshl", q3, p3), mSolver.binary("#b100"));
		mSolver.assertTerm(input);
		final LBool isUnSat = mSolver.checkSat();
		Assert.assertSame(LBool.SAT, isUnSat);
		mSolver.reset();
	}


	@Test
	public void bitVec1() {
		mSolver.resetAssertions();
		final Term input =
				mSolver.term("and", mSolver.term("=", mSolver.term("bvadd", p2, mSolver.binary("#b00")), q2),
						mSolver.term("or", mSolver.term("=", mSolver.term("bvadd", p2, mSolver.binary("#b11")), q2),
								mSolver.term("=", mSolver.term("bvadd", p2, mSolver.binary("#b01")), q2)));
		mSolver.assertTerm(input);
		final LBool isUnSat = mSolver.checkSat();
		Assert.assertSame(LBool.UNSAT, isUnSat);
		mSolver.reset();
	}

	@Test
	public void bitVecBvComp() {
		mSolver.resetAssertions();
		final Term input = mSolver.term("=", mSolver.term("bvcomp", x, y),
				mSolver.binary("#b1"));
		mSolver.assertTerm(input);
		final LBool isUnSat = mSolver.checkSat();
		Assert.assertSame(LBool.SAT, isUnSat);
		mSolver.reset();
	}

	@Test
	public void bitVecRepeat() {
		mSolver.resetAssertions();
		final String[] indices = new String[1];
		indices[0] = "4";
		final Term input =
				mSolver.term("=", mSolver.binary("#b1100110011001100"),
						mSolver.term("repeat", indices, null, mSolver.binary("#b1100")));

		mSolver.assertTerm(input);
		final LBool isUnSat = mSolver.checkSat();
		Assert.assertSame(LBool.SAT, isUnSat);
		mSolver.reset();
	}

	@Test
	public void bitVecSignExtend() {
		mSolver.resetAssertions();
		final String[] indices = new String[1];
		indices[0] = "4";
		final Term input =
				mSolver.term("=", mSolver.binary("#b11111100"),
						mSolver.term("sign_extend", indices, null, mSolver.binary("#b1100")));

		mSolver.assertTerm(input);
		final LBool isUnSat = mSolver.checkSat();
		Assert.assertSame(LBool.SAT, isUnSat);
		mSolver.reset();
	}

	@Test
	public void bitVecZeroExtend() {
		mSolver.resetAssertions();
		final String[] indices = new String[1];
		indices[0] = "4";
		final Term input =
				mSolver.term("=", mSolver.binary("#b00001100"),
						mSolver.term("zero_extend", indices, null, mSolver.binary("#b1100")));

		mSolver.assertTerm(input);
		final LBool isUnSat = mSolver.checkSat();
		Assert.assertSame(LBool.SAT, isUnSat);
		mSolver.reset();
	}

	@Test
	public void bitVecRotateLeft() {
		mSolver.resetAssertions();
		final String[] indices = new String[1];
		indices[0] = "2";
		final Term input =
				mSolver.term("=", mSolver.binary("#b0011"),
						mSolver.term("rotate_left", indices, null, mSolver.binary("#b1100")));

		mSolver.assertTerm(input);
		final LBool isUnSat = mSolver.checkSat();
		Assert.assertSame(LBool.SAT, isUnSat);
		mSolver.reset();
	}

	@Test
	public void bitVecRotateRight() {
		mSolver.resetAssertions();
		final String[] indices = new String[1];
		indices[0] = "2";
		final Term input =
				mSolver.term("=", mSolver.binary("#b0011"),
						mSolver.term("rotate_right", indices, null, mSolver.binary("#b1100")));

		mSolver.assertTerm(input);
		final LBool isUnSat = mSolver.checkSat();
		Assert.assertSame(LBool.SAT, isUnSat);
		mSolver.reset();
	}

	@Test
	public void bitVecBvSDIV() {
		mSolver.resetAssertions();
		final Term input = mSolver.term("=", mSolver.term("bvsdiv", mSolver.binary("#b1100"), mSolver.binary("#b0010")),
				mSolver.binary("#b1010"));
		mSolver.assertTerm(input);
		final LBool isUnSat = mSolver.checkSat();
		Assert.assertSame(LBool.SAT, isUnSat);
		mSolver.reset();
	}
	@Test
	public void bitVecBvSMOD() {
		mSolver.resetAssertions();
		final Term input = mSolver.term("=", mSolver.term("bvsmod", mSolver.binary("#b0101"), mSolver.binary("#b0010")),
				mSolver.binary("#b0001"));
		mSolver.assertTerm(input);
		final LBool isUnSat = mSolver.checkSat();
		Assert.assertSame(LBool.SAT, isUnSat);
		mSolver.reset();
	}

	@Test
	public void bitVec2() {
		mSolver.resetAssertions();
		final Term input = mSolver.term("and", mSolver.term("=", mSolver.binary("#b1000"), p4),
				mSolver.term("or", mSolver.term("not", mSolver.term("=", mSolver.binary("#b1011"), p4)),
						mSolver.term("=", mSolver.binary("#b1001"), p4)));
		mSolver.assertTerm(input);
		final LBool isUnSat = mSolver.checkSat();
		Assert.assertSame(LBool.SAT, isUnSat);
		mSolver.reset();
	}

	// (= (concat (ite (not (= (_ bv0 1) (_ bv1 1))) (_ bv1 1) (_ bv0 1)) (_ bv0 1)) (_ bv2 2))
	@Test
	public void bitVec3() {
		mSolver.resetAssertions();
		final String[] constindices = new String[1];
		constindices[0] = "1";
		final String[] constindices2 = new String[1];
		constindices2[0] = "2";

		final Term input = mSolver.term("=", mSolver.term("concat",
				mSolver.term("ite", mSolver.term("not", mSolver.term("=", mSolver.term("bv0", constindices, null),
						p)),
						mSolver.term("bv1", constindices, null), mSolver.term("bv0", constindices, null)),
				mSolver.term("bv0", constindices, null)),
				mSolver.term("bv2", constindices2, null));
		mSolver.assertTerm(input);
		final LBool isUnSat = mSolver.checkSat();
		Assert.assertSame(LBool.SAT, isUnSat);
		mSolver.reset();
	}

	@Test
	public void bitVec4() {
		mSolver.resetAssertions();
		final String[] constindices = new String[1];
		constindices[0] = "1";
		final String[] constindices2 = new String[1];
		constindices2[0] = "2";

		final Term input = mSolver.term("not", mSolver.term("=", mSolver.term("concat",
				mSolver.term("bv1", constindices, null), mSolver.term("bv0", constindices, null)),
				mSolver.term("bv6", constindices2, null)));
		mSolver.assertTerm(input);
		final LBool isUnSat = mSolver.checkSat();
		Assert.assertSame(LBool.UNSAT, isUnSat);
		mSolver.reset();
	}

	@Test
	public void bvand() {
		mSolver.resetAssertions();
		final Term input = mSolver.term("=", mSolver.term("bvnand",
				mSolver.binary("#b11110010"), p8),
				mSolver.binary("#b11001101"));

		mSolver.assertTerm(input);
		final LBool isUnSat = mSolver.checkSat();
		Assert.assertSame(LBool.SAT, isUnSat);
		mSolver.reset();
	}

	@Test
	public void bvor() {
		mSolver.resetAssertions();
		final Term input = mSolver.term("=", mSolver.term("bvor",
				mSolver.binary("#b11000010"), p8),
				mSolver.binary("#b11110010"));
		mSolver.assertTerm(input);
		final LBool isUnSat = mSolver.checkSat();
		Assert.assertSame(LBool.SAT, isUnSat);
		mSolver.reset();
	}

	@Test
	public void bitVecLeftShiftUNSATOptimization() {
		mSolver.resetAssertions();
		final Term input = mSolver.term("=", mSolver.binary("#b00000001"),
				mSolver.term("bvshl", p8, mSolver.binary("#b00001000")));
		mSolver.assertTerm(input);
		final LBool isUnSat = mSolver.checkSat();
		Assert.assertSame(LBool.UNSAT, isUnSat);
		mSolver.reset();
	}

	@Test
	public void bitVecLeftShiftSATOptimization() {
		mSolver.resetAssertions();
		final Term input = mSolver.term("=", mSolver.binary("#b10000000"),
				mSolver.term("bvshl", p8, mSolver.binary("#b00000111")));
		mSolver.assertTerm(input);
		final LBool isUnSat = mSolver.checkSat();
		Assert.assertSame(LBool.SAT, isUnSat);
		mSolver.reset();
	}
	@Test
	public void bitVecLeftShiftSAT2() {
		// Check ob optimization for constat correct in all cases
		mSolver.resetAssertions();
		final Term input = mSolver.term("and", mSolver.term("=", mSolver.binary("#b000"),
				mSolver.term("bvshl", p3, mSolver.binary("#b111"))), mSolver.term("=", p3, mSolver.binary("#b010")));
		mSolver.assertTerm(input);
		final LBool isUnSat = mSolver.checkSat();
		Assert.assertSame(LBool.SAT, isUnSat);
		mSolver.reset();
	}

	@Test
	public void bitVecSmallShiftUNSAT() {
		mSolver.resetAssertions();
		final Term input = mSolver.term("and", mSolver.term("=", mSolver.binary("#b10"),
				mSolver.term("bvshl", p2, mSolver.binary("#b01"))), mSolver.term("=", p2, mSolver.binary("#b00")));
		mSolver.assertTerm(input);
		final LBool isUnSat = mSolver.checkSat();
		Assert.assertSame(LBool.UNSAT, isUnSat);
		mSolver.reset();
	}

	@Test
	public void bitVecRightShiftUNSAT() {
		mSolver.resetAssertions();
		final Term input = mSolver.term("and", mSolver.term("=", mSolver.binary("#b0010"),
				mSolver.term("bvlshr", p4, mSolver.binary("#b0010"))), mSolver.term("=", p4, mSolver.binary("#b0100")));
		mSolver.assertTerm(input);
		final LBool isUnSat = mSolver.checkSat();
		Assert.assertSame(LBool.UNSAT, isUnSat);
		mSolver.reset();
	}

	@Test
	public void bitVecSmallRightShiftSAT() {
		// Check ob optimization for constat correct in all cases
		mSolver.resetAssertions();
		final Term input = mSolver.term("and", mSolver.term("=", mSolver.binary("#b0001"),
				mSolver.term("bvlshr", p4, mSolver.binary("#b0011"))), mSolver.term("=", p4, mSolver.binary("#b1000")));
		mSolver.assertTerm(input);
		final LBool isUnSat = mSolver.checkSat();
		Assert.assertSame(LBool.SAT, isUnSat);
		mSolver.reset();
	}

	@Test
	public void bitVecSmallRightShiftUNSATBUG() {
		// Check ob optimization for constat correct in all cases
		mSolver.resetAssertions();
		final Term input = mSolver.term("and", mSolver.term("=", mSolver.binary("#b0010"),
				mSolver.term("bvlshr", p4, mSolver.binary("#b0011"))), mSolver.term("=", p4, mSolver.binary("#b1000")));
		mSolver.assertTerm(input);
		final LBool isUnSat = mSolver.checkSat();
		Assert.assertSame(LBool.UNSAT, isUnSat);
		mSolver.reset();
	}
	@Test
	public void bitVecSmallRightShiftSAT1() {
		// Check ob optimization for constat correct in all cases
		mSolver.resetAssertions();
		final Term input = mSolver.term("and", mSolver.term("=", mSolver.binary("#b0100"),
				mSolver.term("bvlshr", p4, mSolver.binary("#b0001"))), mSolver.term("=", p4, mSolver.binary("#b1000")));
		mSolver.assertTerm(input);
		final LBool isUnSat = mSolver.checkSat();
		Assert.assertSame(LBool.SAT, isUnSat);
		mSolver.reset();
	}

	@Test
	public void bitVecSmallRightShiftUNSAT2() {
		// Check ob optimization for constat correct in all cases
		mSolver.resetAssertions();
		final Term input = mSolver.term("and", mSolver.term("=", mSolver.binary("#b0000"),
				mSolver.term("bvlshr", p4, mSolver.binary("#b0001"))), mSolver.term("=", p4, mSolver.binary("#b0100")));
		mSolver.assertTerm(input);
		final LBool isUnSat = mSolver.checkSat();
		Assert.assertSame(LBool.UNSAT, isUnSat);
		mSolver.reset();
	}
	@Test
	public void bitVecSmallRightShiftUNSAT3() {
		// Check ob optimization for constat correct in all cases
		mSolver.resetAssertions();
		final Term input = mSolver.term("and", mSolver.term("=", mSolver.binary("#b0000"),
				mSolver.term("bvlshr", p4, mSolver.binary("#b0000"))), mSolver.term("=", p4, mSolver.binary("#b1111")));
		mSolver.assertTerm(input);
		final LBool isUnSat = mSolver.checkSat();
		Assert.assertSame(LBool.UNSAT, isUnSat);
		mSolver.reset();
	}

	@Test
	public void bitVecSmallRightShiftSAT3() {
		// Check ob optimization for constat correct in all cases
		mSolver.resetAssertions();
		final Term input = mSolver.term("and", mSolver.term("=", mSolver.binary("#b0000"),
				mSolver.term("bvlshr", p4, mSolver.binary("#b1111"))), mSolver.term("=", p4, mSolver.binary("#b1111")));
		mSolver.assertTerm(input);
		final LBool isUnSat = mSolver.checkSat();
		Assert.assertSame(LBool.SAT, isUnSat);
		mSolver.reset();
	}
	@Test
	public void bitVecSmallLeftShiftUNSAT2() {
		// Check ob optimization for constat correct in all cases
		mSolver.resetAssertions();
		final Term input = mSolver.term("and", mSolver.term("=", mSolver.binary("#b000"),
				mSolver.term("bvshl", p3, mSolver.binary("#b001"))), mSolver.term("=", p3, mSolver.binary("#b010")));
		mSolver.assertTerm(input);
		final LBool isUnSat = mSolver.checkSat();
		Assert.assertSame(LBool.UNSAT, isUnSat);
		mSolver.reset();
	}
	@Test
	public void bitVecSmallShiftSAT() {
		// Check ob optimization for constat correct in all cases
		mSolver.resetAssertions();
		final Term input = mSolver.term("and", mSolver.term("=", mSolver.binary("#b00"),
				mSolver.term("bvshl", p2, mSolver.binary("#b00"))), mSolver.term("=", p2, mSolver.binary("#b00")));
		mSolver.assertTerm(input);
		final LBool isUnSat = mSolver.checkSat();
		Assert.assertSame(LBool.SAT, isUnSat);
		mSolver.reset();
	}

	@Test
	public void bitVecAddSAT1() {
		mSolver.resetAssertions();
		final Term input =
				mSolver.term("=", mSolver.binary("#b010"),
						mSolver.term("bvadd", p3, q3));
		mSolver.assertTerm(input);
		final LBool isSat = mSolver.checkSat();
		Assert.assertSame(LBool.SAT, isSat);
		mSolver.reset();
	}

	@Test
	public void bitVecAddSAT2() {
		mSolver.resetAssertions();
		final Term input =
				mSolver.term("and", mSolver.term("=", mSolver.binary("#b00"),
						mSolver.term("bvadd", p2, mSolver.binary("#b00"))),
						mSolver.term("=", p2, mSolver.binary("#b00")));
		mSolver.assertTerm(input);
		final LBool isSat = mSolver.checkSat();
		Assert.assertSame(LBool.SAT, isSat);
		mSolver.reset();
	}

	@Test
	public void bitVecAddSAT3() {
		mSolver.resetAssertions();
		final Term input =
				mSolver.term("=", mSolver.binary("#b11"),
						mSolver.term("bvadd", p2, mSolver.binary("#b01")));
		mSolver.assertTerm(input);
		final LBool isSat = mSolver.checkSat();
		Assert.assertSame(LBool.SAT, isSat);
		mSolver.reset();
	}
	@Test
	public void bitVecAddSAT4() {
		mSolver.resetAssertions();
		final Term input =
				mSolver.term("=", mSolver.binary("#b100"),
						mSolver.term("bvadd", p3, mSolver.binary("#b010")));
		mSolver.assertTerm(input);
		final LBool isSat = mSolver.checkSat();
		Assert.assertSame(LBool.SAT, isSat);
		mSolver.reset();
	}

	@Test
	public void bitVecAdd2UNSAT() {
		mSolver.resetAssertions();
		final Term input = mSolver.term("and", mSolver.term("=", mSolver.binary("#b10"),
				mSolver.term("bvadd", p2, mSolver.binary("#b10"))),
				mSolver.term("=", mSolver.binary("#b11"),
						mSolver.term("bvadd", p2, mSolver.binary("#b01"))));
		mSolver.assertTerm(input);
		final LBool isSat = mSolver.checkSat();
		Assert.assertSame(LBool.UNSAT, isSat);
		mSolver.reset();
	}
	@Test
	public void bitVecAdd2SAT() {
		mSolver.resetAssertions();
		final Term input = mSolver.term("and", mSolver.term("=", mSolver.binary("#b10"), p2),
				mSolver.term("=", mSolver.binary("#b11"),
						mSolver.term("bvadd", p2, mSolver.binary("#b01"))));
		mSolver.assertTerm(input);
		final LBool isSat = mSolver.checkSat();
		Assert.assertSame(LBool.SAT, isSat);
		mSolver.reset();
	}

	@Test
	public void bitVecMulUNSAT() {
		mSolver.resetAssertions();
		final Term input =
				mSolver.term("=", mSolver.term("bvmul", p4, mSolver.binary("#b0010")), mSolver.binary("#b1001"));
		mSolver.assertTerm(input);
		final LBool isUnSat = mSolver.checkSat();
		Assert.assertSame(LBool.UNSAT, isUnSat);
		mSolver.reset();
	}

	@Test
	public void bitVecMulSAT() {
		mSolver.resetAssertions();
		final Term input =
				mSolver.term("=", mSolver.term("bvmul", p3, mSolver.binary("#b010")), mSolver.binary("#b100"));
		mSolver.assertTerm(input);
		final LBool isUnSat = mSolver.checkSat();
		Assert.assertSame(LBool.SAT, isUnSat);
		mSolver.reset();
	}

	@Test
	public void bitVecMulSATZero() {
		mSolver.resetAssertions();
		final Term input =
				mSolver.term("=", mSolver.term("bvmul", p3, mSolver.binary("#b000")), mSolver.binary("#b000"));
		mSolver.assertTerm(input);
		final LBool isUnSat = mSolver.checkSat();
		Assert.assertSame(LBool.SAT, isUnSat);
		mSolver.reset();
	}

	@Test
	public void bitVecMulUNSAT2() {
		mSolver.resetAssertions();
		final Term input = mSolver.term("and",
				mSolver.term("=", mSolver.term("bvmul", p4, mSolver.binary("#b0010")), mSolver.binary("#b0100")),
				mSolver.term("=", p4, mSolver.binary("#b0000")));
		mSolver.assertTerm(input);
		final LBool isUnSat = mSolver.checkSat();
		Assert.assertSame(LBool.UNSAT, isUnSat);
		mSolver.reset();
	}

	@Test
	public void bitVecNegation() {
		mSolver.resetAssertions();
		final Term input = mSolver.term("and",
				mSolver.term("=", mSolver.term("bvneg", p4), mSolver.binary("#b1111")),
				mSolver.term("=", p4, mSolver.binary("#b0111")));
		mSolver.assertTerm(input);
		final LBool isUnSat = mSolver.checkSat();
		Assert.assertSame(LBool.SAT, isUnSat);
		mSolver.reset();
	}

	@Test
	public void bitVecNotAtom() {
		mSolver.resetAssertions();
		final Term input = mSolver.term("and",
				mSolver.term("=", p2, mSolver.binary("#b11")),
				mSolver.term("not", mSolver.term("=", p2, mSolver.binary("#b11"))));
		mSolver.assertTerm(input);
		final LBool isUnSat = mSolver.checkSat();
		Assert.assertSame(LBool.UNSAT, isUnSat);
		mSolver.reset();
	}

	@Test
	public void bitVecBVULTAtom() {
		mSolver.resetAssertions();
		// p4 = 0000
		final Term input = mSolver.term("and",
				mSolver.term("bvult", p4, mSolver.binary("#b0011")),
				mSolver.term("not", mSolver.term("=", p4, mSolver.binary("#b0001"))),
				mSolver.term("not", mSolver.term("=", p4, mSolver.binary("#b0010"))));
		mSolver.assertTerm(input);
		final LBool isUnSat = mSolver.checkSat();
		Assert.assertSame(LBool.SAT, isUnSat);
		mSolver.reset();
	}

	@Test
	public void bitVecBVULTAtom2() {
		mSolver.resetAssertions();
		final Term input = mSolver.term("and",
				mSolver.term("bvult", mSolver.binary("#b0111"), p4),
				mSolver.term("not", mSolver.term("=", p4, mSolver.binary("#b1000"))));
		mSolver.assertTerm(input);
		final LBool isUnSat = mSolver.checkSat();
		Assert.assertSame(LBool.SAT, isUnSat);
		mSolver.reset();
	}

	@Test
	public void bitVecSub1() {
		mSolver.resetAssertions();
		final Term input = mSolver.term("and",
				mSolver.term("=", mSolver.term("bvsub", mSolver.binary("#b0111"), p4), mSolver.binary("#b0001")),
				mSolver.term("=", p4, mSolver.binary("#b0110")));
		mSolver.assertTerm(input);
		final LBool isUnSat = mSolver.checkSat();
		Assert.assertSame(LBool.SAT, isUnSat);
		mSolver.reset();
	}

	@Test
	public void bitVecANDBitMask() {
		mSolver.resetAssertions();
		final Term input = mSolver.term("and",
				mSolver.term("=", mSolver.binary("#b1111"), mSolver.term("bvand", p4, mSolver.binary("#b0110"))),
				mSolver.term("=", p4, mSolver.binary("#b0011")));
		mSolver.assertTerm(input);
		final LBool isUnSat = mSolver.checkSat();
		Assert.assertSame(LBool.UNSAT, isUnSat);
		mSolver.reset();
	}

	@Test
	public void bitVecORBitMask() {
		mSolver.resetAssertions();
		final Term input = mSolver.term("and",
				mSolver.term("=", mSolver.binary("#b1110"), mSolver.term("bvor", p4, mSolver.binary("#b0110"))),
				mSolver.term("=", p4, mSolver.binary("#b0001")),
				mSolver.term("=", mSolver.binary("#b0001"), mSolver.binary("#b0001")));
		mSolver.assertTerm(input);
		final LBool isUnSat = mSolver.checkSat();
		Assert.assertSame(LBool.UNSAT, isUnSat);
		mSolver.reset();
	}
}