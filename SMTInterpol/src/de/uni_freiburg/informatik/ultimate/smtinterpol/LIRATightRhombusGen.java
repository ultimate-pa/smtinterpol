package de.uni_freiburg.informatik.ultimate.smtinterpol;

import java.io.FileNotFoundException;
import java.io.PrintWriter;
import java.math.BigInteger;

import de.uni_freiburg.informatik.ultimate.logic.Rational;

public class LIRATightRhombusGen {

	private static void printRational(PrintWriter out, Rational r) {
		if (r.isIntegral())
			out.print(r.numerator());
		else {
			out.print("(/ ");
			out.print(r.numerator());
			out.print(' ');
			out.print(r.denominator());
			out.print(")");
		}
	}

	private final static Rational EPSILON = Rational.valueOf(1, 1000000000);

	private static void writeBenchmarkHead(PrintWriter out, Rational xcoeff,
			Rational ycoeff, Rational scale) {
		out.println("(set-info :category \"crafted\")");
		out.println("(set-logic QF_LIRA)");
		out.println("(declare-fun x () Int)");
		out.println("(declare-fun y () Real)");
		out.println("(declare-fun z () Int)");
		out.println("(assert (and");
		out.print("\t(<= 0 (- (* ");
		printRational(out, xcoeff);
		out.print(" x) (* ");
		printRational(out, ycoeff.add(Rational.ONE));
		out.println(" y)))");
		out.print("\t(<= (- (* ");
		printRational(out, xcoeff);
		out.print(" x) (* ");
		printRational(out, ycoeff.add(Rational.ONE));
		out.print(" y)) ");
		printRational(out, scale.sub(Rational.ONE));
		out.println(")");
		out.print("\t(<= 1 (- (* ");
		printRational(out, xcoeff.add(Rational.ONE));
		out.print(" x) (* ");
		printRational(out, ycoeff);
		out.println(" y)))");
		out.print("\t(<= (- (* ");
		printRational(out, xcoeff.add(Rational.ONE));
		out.print(" x) (* ");
		printRational(out, ycoeff);
		out.print(" y)) ");
		printRational(out, scale);
		out.println(")))");
		out.println("(assert (<= 0 (- y z)))");
	}

	private static void writeSatBenchmark(Rational xcoeff, Rational ycoeff,
			Rational scale, Rational mindiff, String x, String y, String s)
					throws FileNotFoundException {
		PrintWriter out = new PrintWriter("tightrhombus-lira-" + x + "-" + y + "-" + s + "-sat.smt2");
		out.println("(set-info :souce |A tight rhombus that only contains a few solutions.  This benchmark is designed to be hard for cut engines.\n"
				+ "Authors: The SMTInterpol team|)");
		out.println("(set-info :status sat)");
		writeBenchmarkHead(out, xcoeff, ycoeff, scale);
		out.print("(assert (<= (- y z) ");
		printRational(out, mindiff);
		out.println("))");
		out.println("(check-sat)");
		out.println("(exit)");
		out.flush();
		out.close();
	}

	private static void writeUnsatBenchmark(Rational xcoeff, Rational ycoeff,
			Rational scale, Rational mindiff, String x, String y, String s)
					throws FileNotFoundException {
		PrintWriter out = new PrintWriter("tightrhombus-lira-" + x + "-" + y + "-" + s + "-unsat.smt2");
		out.println("(set-info :souce |A tight rhombus without solutions.  This benchmark is designed to be hard for cut engines.\n"
				+ "Authors: The SMTInterpol team|)");
		out.println("(set-info :status unsat)");
		writeBenchmarkHead(out, xcoeff, ycoeff, scale);
		out.print("(assert (<= (- y z) (- ");
		printRational(out, mindiff);
		out.print(" ");
		printRational(out, EPSILON);
		out.println(")))");
		out.println("(check-sat)");
		out.println("(exit)");
		out.flush();
		out.close();
	}

	public static void main(String[] args) throws FileNotFoundException {
		if (args.length < 3) {
			System.err.println("USAGE: LIRATightRhombusGen <xval> <yval> <scale>");
			System.exit(0);
		}
		BigInteger xval = new BigInteger(args[0]);
		BigInteger yval = new BigInteger(args[1]);
		int iscale = Integer.parseInt(args[2]);
		final Rational TEN = Rational.valueOf(10, 1);
		Rational scale = TEN;
		for (int i = 0; i < iscale; ++i)
			scale = scale.mul(TEN);
		Rational xcoeff = Rational.valueOf(xval, BigInteger.ONE).mul(scale);
		Rational ycoeff = Rational.valueOf(yval, BigInteger.ONE).mul(scale);
		Rational xelimcoeff =
				xcoeff.add(ycoeff).add(Rational.ONE).div(ycoeff).div(
						ycoeff.add(Rational.ONE));
		Rational xlower = ycoeff.inverse().sub(scale.sub(Rational.ONE).div(
				ycoeff.add(Rational.ONE))).div(xelimcoeff).ceil();
		Rational xupper = scale.div(ycoeff).div(xelimcoeff).floor();
		System.err.println("xlower = " + xlower);
		System.err.println("xupper = " + xupper);
		Rational mindiff = Rational.POSITIVE_INFINITY;
		for (Rational i = xlower; i.compareTo(xupper) <= 0; i = i.add(Rational.ONE)) {
			Rational ymax1 = xcoeff.div(ycoeff.add(Rational.ONE)).mul(i);
			Rational ymax2 = xcoeff.add(Rational.ONE).div(ycoeff).mul(i).sub(ycoeff.inverse());
			Rational ymax = ymax1.compareTo(ymax2) <= 0 ? ymax1 : ymax2;
			Rational diff = ymax.sub(ymax.floor());
			if (diff.compareTo(mindiff) < 0)
				mindiff = diff;
			Rational ymin1 = xcoeff.div(ycoeff.add(Rational.ONE)).mul(i).sub(scale.sub(Rational.ONE).div(ycoeff.add(Rational.ONE)));
			Rational ymin2 = xcoeff.add(Rational.ONE).div(ycoeff).mul(i).sub(scale.div(ycoeff));
			Rational ymin = ymin1.compareTo(ymin2) > 0 ? ymin1 : ymin2;
			diff = ymin.sub(ymin.floor());
			if (diff.compareTo(mindiff) < 0)
				mindiff = diff;
		}
		System.err.println("mindiff = " + mindiff);
		writeSatBenchmark(xcoeff, ycoeff, scale, mindiff, args[0], args[1], args[2]);
		writeUnsatBenchmark(xcoeff, ycoeff, scale, mindiff, args[0], args[1], args[2]);
	}

}
