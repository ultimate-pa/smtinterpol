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
package de.uni_freiburg.informatik.ultimate.smtinterpol;

import java.io.File;
import java.io.FileNotFoundException;
import java.io.PrintWriter;
import java.math.BigDecimal;
import java.math.BigInteger;
import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.Random;

import org.apache.log4j.ConsoleAppender;
import org.apache.log4j.Level;
import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.ConstantTerm;
import de.uni_freiburg.informatik.ultimate.logic.FormulaUnLet;
import de.uni_freiburg.informatik.ultimate.logic.LetTerm;
import de.uni_freiburg.informatik.ultimate.logic.Logics;
import de.uni_freiburg.informatik.ultimate.logic.NoopScript;
import de.uni_freiburg.informatik.ultimate.logic.PrintTerm;
import de.uni_freiburg.informatik.ultimate.logic.SMTLIBException;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermTransformer;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.smtinterpol.smtlib2.ParseEnvironment;
import de.uni_freiburg.informatik.ultimate.smtinterpol.smtlib2.SMTInterpol;

public class LIRAGenerator {
	
	private static final String DIRNAME = "lira";
	private static final String DIRNAME_BIASED = "lirabiased";
	private static final String TIMEOUTVAL = "300000";
	private static final boolean BIASED = System.getProperty("BIASED") != null;
	private static final int QUANTILE = 5;
	private static final int ROUNDS = 10;
	
	private static class DeclareFun {
		private final String mFunName;
		private String mSort;
		public DeclareFun(String funName, Sort sort) {
			mFunName = funName;
			mSort = sort.getName();
		}
		public void dump(PrintWriter writer) {
			writer.print("(declare-fun ");
			writer.print(mFunName);
			writer.print(" () ");
			writer.print(mSort);
			writer.println(')');
		}
		public void toSolver(SMTInterpol solver) {
			solver.declareFun(mFunName, new Sort[0], solver.sort(mSort));
		}
		public boolean tryToggle() {
			if (mSort.equals("Int")) {
				mSort = "Real";
				return true;
			}
			return false;
		}
		public void untoggle() {
			mSort = "Int";
		}
	}
	
	private static class ParseScript extends NoopScript {
		private final List<DeclareFun> mFuns = new ArrayList<DeclareFun>();
		private Term mAssertion;
		public ParseScript() {
			super.setLogic(Logics.QF_LIRA);
		}
		@Override
		public void setLogic(Logics ignored) {}
		@Override
		public void declareFun(String fun, Sort[] paramSorts, Sort resultSort)
				throws SMTLIBException {
			super.declareFun(fun, paramSorts, resultSort);
			mFuns.add(new DeclareFun(fun, resultSort));
		}
		@Override
		public LBool assertTerm(Term term) throws SMTLIBException {
			mAssertion = new FormulaUnLet().unlet(term);
			return super.assertTerm(term);
		}
		public List<DeclareFun> getFuns() {
			return mFuns;
		}
		public Term getAssertion() {
			return mAssertion;
		}
	}
	
	private static class TermCopier extends TermTransformer {

		private final SMTInterpol mSolver;
		
		public TermCopier(SMTInterpol solver) {
			mSolver = solver;
		}

		@Override
		public void convertApplicationTerm(ApplicationTerm appTerm,
				Term[] newArgs) {
			setResult(mSolver.term(appTerm.getFunction().getName(), newArgs));
		}

		@Override
		public void postConvertLet(LetTerm oldLet, Term[] newValues,
				Term newBody) {
			TermVariable[] oldvars = oldLet.getVariables();
			TermVariable[] vars = new TermVariable[oldvars.length];
			for (int i = 0; i < oldvars.length; ++i) {
				vars[i] = mSolver.variable(oldvars[i].getName(),
						mSolver.sort(oldvars[i].getSort().getName()));
			}
			setResult(mSolver.let(vars, newValues, newBody));
		}

		@Override
		protected void convert(Term term) {
			if (term instanceof ConstantTerm) {
				ConstantTerm ct = (ConstantTerm) term;
				if (ct.getValue() instanceof BigInteger)
					setResult(mSolver.numeral((BigInteger) ct.getValue()));
				else
					setResult(mSolver.decimal((BigDecimal) ct.getValue()));
			} else if (term instanceof TermVariable) {
				TermVariable tv = (TermVariable) term;
				setResult(mSolver.variable(tv.getName(), mSolver.sort(tv.getSort().getName())));
			} else
				super.convert(term);
		}
		
	}

	private static void dump(List<DeclareFun> funs, Term assertion, String outfile) throws FileNotFoundException {
		PrintWriter pw = new PrintWriter(outfile);
		pw.println("(set-logic QF_LIRA)");
		for (DeclareFun fun : funs) {
			fun.dump(pw);
		}
		pw.print("(assert ");
		new PrintTerm().append(pw, assertion);
		pw.println(")");
		pw.println("(check-sat)");
		pw.println("(exit)");
		pw.flush();
		pw.close();
	}

	private static LBool test(List<DeclareFun> funs, Term assertion) {
		Logger.getRootLogger().addAppender(new ConsoleAppender());
		Logger.getRootLogger().setLevel(Level.FATAL);
		SMTInterpol solver = new SMTInterpol(Logger.getRootLogger());
		solver.setOption(":timeout", TIMEOUTVAL);
		solver.setLogic(Logics.QF_LIRA);
		for (DeclareFun fun : funs) {
			fun.toSolver(solver);
		}
		Term solverterm = new TermCopier(solver).transform(assertion);
		solver.assertTerm(solverterm);
		return solver.checkSat();
	}

	public static void main(String[] args) throws FileNotFoundException {
		File liradir = new File(BIASED ? DIRNAME_BIASED : DIRNAME);
		if (!liradir.exists() && !liradir.mkdir()) {
			System.err.println("Could not create lira dir");
			System.exit(1);
		}
		Random rnd = new Random();
		for (String infile : args) {
			System.err.println("Modifying " + infile);
			String outfile = null;
			ParseScript ps = new ParseScript();
			ParseEnvironment pe = new ParseEnvironment(ps) {
				@Override
				public void printSuccess() {
					// Disable output
				}
				@Override
				public void printValues(Map<Term, Term> values) {
					// Disable output
				}
				@Override
				public void printResponse(Object response) {
					// Disable output
				}
				@Override
				public void printInfoResponse(String info, Object response) {
					// Disable output
				}
				@Override
				public void printTermResponse(Term[] response) {
					// Disable output
				}
			};
			pe.parseScript(infile);
			if (BIASED) {
				int sat = 0;
				int unsat = 0;
				int unknown = 0;
				int mod = 0;
				for (DeclareFun fun : ps.getFuns()) {
					if (fun.tryToggle()) {
						++mod;
						System.err.print("Trying " + fun.mFunName + "...");
						if (mod != ps.getFuns().size()) {
							LBool issat = test(ps.getFuns(), ps.getAssertion());
							if (issat == LBool.SAT) {
								outfile = DIRNAME_BIASED + File.separatorChar +
										infile.substring(0, infile.length() - 4) + 
										"-b-" + sat++ + ".smt2";
							} else if (issat == LBool.UNSAT) {
								System.err.println("\tsuccess");
								outfile = DIRNAME_BIASED + File.separatorChar +
										infile.substring(0, infile.length() - 4) +
										"-a-" + unsat++ + ".smt2";
							} else {
								outfile = DIRNAME_BIASED + File.separatorChar +
										infile.substring(0, infile.length() - 4) +
										"-c-" + unknown++ + ".smt2";
							}
							dump(ps.getFuns(), ps.getAssertion(), outfile);
							if (issat != LBool.UNSAT) {
								--mod;
								fun.untoggle();
								System.err.println("\tfailure");
							}
						}
					}
				}
			} else {
				// unbiased version
				List<DeclareFun> funs = ps.getFuns();
				int treshhold = funs.size() / QUANTILE;
				for (int i = 0; i < ROUNDS; ++i) {
					System.err.print(i);
					int j = 0;
					while (j < treshhold) {
						int idx = rnd.nextInt(funs.size());
						if (funs.get(idx).tryToggle())
							++j;
					}
					dump(funs, ps.getAssertion(), DIRNAME + File.separatorChar +
							infile.substring(0, infile.length() - 4) + i + ".smt2");
					for (DeclareFun fun : funs) {
						fun.untoggle();
					}
				}
			}
		}
	}

}
