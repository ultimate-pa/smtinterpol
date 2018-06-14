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
package de.uni_freiburg.informatik.ultimate.smtinterpol.cartabs;

import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileReader;
import java.io.IOException;
import java.io.InputStreamReader;
import java.io.PrintWriter;
import java.io.Reader;
import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Deque;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Locale;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.logic.PrintTerm;
import de.uni_freiburg.informatik.ultimate.logic.QuotedObject;
import de.uni_freiburg.informatik.ultimate.logic.SMTLIBException;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.smtinterpol.Config;
import de.uni_freiburg.informatik.ultimate.smtinterpol.option.FrontEndOptions;
import de.uni_freiburg.informatik.ultimate.smtinterpol.option.LongOption;
import de.uni_freiburg.informatik.ultimate.smtinterpol.option.OptionMap;
import de.uni_freiburg.informatik.ultimate.smtinterpol.smtlib2.ExitHook;
import de.uni_freiburg.informatik.ultimate.smtinterpol.util.MySymbolFactory;

public class ParseEnvironment {
	final Script      mScript;
	private File mCwd = null;
	// What to do when script exits
	private ExitHook mExitHook;
	// Initialize this lazily.
	private Deque<Long> mTiming;

	private final FrontEndOptions mOptions;
	
	private Lexer mLexer = null;
	private boolean mVersion25 = true;

	private LongOption mCartAbsNumber;
	private Map<String, TermVariable> mGlobals = new LinkedHashMap<String, TermVariable>();
	private Map<String, TermVariable> mPrimedGlobals = new LinkedHashMap<String, TermVariable>();
	private Map<String, TermVariable> mLocals = new LinkedHashMap<String, TermVariable>();
	private Map<String, TermVariable> mPrimedLocals = new LinkedHashMap<String, TermVariable>();
	private Map<String, TermVariable> mOtherLocals = new LinkedHashMap<String, TermVariable>();
	private Map<String, TermVariable> mPrimedOtherLocals = new LinkedHashMap<String, TermVariable>();
	private String mInvariant = null;

	public ParseEnvironment(Script script, OptionMap options) {
		this(script, null, options);
	}
	
	public ParseEnvironment(Script script, ExitHook exit,
			OptionMap options) {
		mScript = script;
		mExitHook = exit;
		mOptions = options.getFrontEndOptions();
		if (!mOptions.isFrontEndActive()) {
			throw new IllegalArgumentException("Front End not active!");
		}
		mCartAbsNumber = new LongOption(2, true, "number of components in the cartesian abstraction");
		options.addOption(":cartesian-abstraction", mCartAbsNumber);
	}
	
	public Script getScript() {
		return mScript;
	}

	static boolean convertSexp(StringBuilder sb, Object o, int level) {
		if (o instanceof Object[]) {
			if (Config.RESULTS_ONE_PER_LINE && level > 0) {
				sb.append(System.getProperty("line.separator"));
				for (int i = 0; i < level; ++i) {
					sb.append(' ');
				}
			}
			sb.append('(');
			final Object[] array = (Object[])o;
			boolean subarray = false;
			String sep = "";
			for (final Object el : array) {
				sb.append(sep);
				subarray |= convertSexp(sb, el, level + Config.INDENTATION);
				sep = " ";
			}
			if (subarray && Config.RESULTS_ONE_PER_LINE) {
				sb.append(System.getProperty("line.separator"));
				for (int i = 0; i < level; ++i) {
					sb.append(' ');
				}
			}
			sb.append(')');
			return true;
		} else {
			sb.append(o);
		}
		return false;
	}
	
	public void parseScript(String filename) throws SMTLIBException {
		final File oldcwd = mCwd;
		Reader reader = null;
		boolean closeReader = false;
		try {
			if (filename.equals("<stdin>")) {
				reader = new InputStreamReader(System.in);
			} else {
				File script = new File(filename);
				if (!script.isAbsolute()) {
					script = new File(mCwd, filename);
				}
				mCwd = script.getParentFile();
				try {
					reader = new FileReader(script);
					closeReader = true;
				} catch (final FileNotFoundException ex) {
					throw new SMTLIBException("File not found: " + filename);
				}
			}
			parseStream(reader, filename);
		} finally {
			mCwd = oldcwd;
			if (closeReader) {
				try {
					reader.close();
				} catch (final IOException ex) {
				}
			}
		}
	}
	
	public void parseStream(Reader reader, String streamname)
	    throws SMTLIBException {
		final MySymbolFactory symfactory = new MySymbolFactory();
		final Lexer last = mLexer;
		mLexer = new Lexer(reader);
		mLexer.setSymbolFactory(symfactory);
		final Parser parser = new Parser(mLexer, symfactory);
		parser.setFileName(streamname);
		parser.setParseEnvironment(this);
		try {
			parser.parse();
		} catch (final Exception ex) {
			System.err.println("Unexpected Exception: " + ex);
			throw new SMTLIBException(ex);
		} finally {
			mLexer = last;
		}
	}
	
	public void include(String filename) throws SMTLIBException {
		final ExitHook oldexit = mExitHook;
		mExitHook = new ExitHook() {
			@Override
			public void exitHook() {
				/* ignore exit */
			}
		};
		final File oldcwd = mCwd;
		parseScript(filename);
		mCwd = oldcwd;
		mExitHook = oldexit;
	}
	
	public void printSuccess() {
		if (mOptions.isPrintSuccess()) {
			final PrintWriter out = mOptions.getOutChannel();
			out.println("success");
			out.flush();
		}
	}
	
	public void printError(String message) {
		final PrintWriter out = mOptions.getOutChannel();
		out.print("(error \"");
		out.print(message);
		out.println("\")");
		out.flush();
		if (!mOptions.continueOnError()) {
			System.exit(1);
		}
	}
	
	public void printValues(Map<Term, Term> values) {
		final PrintTerm pt = new PrintTerm();
		final PrintWriter out = mOptions.getOutChannel();
		out.print('(');
		String sep = "";
		final String itemSep = Config.RESULTS_ONE_PER_LINE 
				? System.getProperty("line.separator") + " " : " "; 
		for (final Map.Entry<Term, Term> me : values.entrySet()) {
			out.print(sep);
			out.print('(');
			pt.append(out, me.getKey());
			out.print(' ');
			pt.append(out, me.getValue());
			out.print(')');
			sep = itemSep;
		}
		out.println(')');
		out.flush();
	}
	
	public void printResponse(Object response) {
		final PrintWriter out = mOptions.getOutChannel();
		if (!mOptions.isPrintTermsCSE()) {
			if (response instanceof Term) {
				new PrintTerm().append(out, (Term) response);
				out.println();
				out.flush();
				return;
			} else if (response instanceof Term[]) {
				printTermResponse((Term[])response);
				out.flush();
				return;
			}
		}
		if (response instanceof Object[]) {
			final StringBuilder sb = new StringBuilder();
			convertSexp(sb, response, 0);
			out.println(sb.toString());
		} else if (response instanceof Iterable) {
			final Iterable<?> it = (Iterable<?>) response;
			out.print("(");
			for (final Object o : it) {
				printResponse(o);
			}
			out.println(")");
		} else if (response instanceof QuotedObject) {
			out.println(((QuotedObject) response).toString(mVersion25));
		} else {
			out.println(response);
		}
		out.flush();
	}
	
	public void printInfoResponse(String info, Object response) {
		final PrintWriter out = mOptions.getOutChannel();
		final StringBuilder sb = new StringBuilder();
		sb.append('(').append(info).append(' ');
		convertSexp(sb, response, 0);
		out.println(sb.append(')').toString());
		out.flush();
	}
	
	/**
	 * Direct printing of a term array response.  This function is introduced to
	 * satisfy the requirement of the SMTLIB standard for the get-assertions
	 * command.  We have to print the terms "as they are asserted", i.e.,
	 * without introducing let terms via cse.
	 * @param response The response to print.
	 */
	public void printTermResponse(Term[] response) {
		final StringBuilder sb = new StringBuilder();
		final PrintTerm pt = new PrintTerm();
		sb.append('(');
		String sep = "";
		final String itemSep = Config.RESULTS_ONE_PER_LINE 
				? System.getProperty("line.separator") + " " : " ";
		for (final Term t : response) {
			sb.append(sep);
			pt.append(sb, t);
			sep = itemSep;
		}
		sb.append(')');
		mOptions.getOutChannel().println(sb.toString());
		mOptions.getOutChannel().flush();
	}

	public void exit() {
		if (mExitHook == null) {
			mScript.exit();
			Runtime.getRuntime().exit(0);
		} else {
			mExitHook.exitHook();
		}
	}
	
	public void setInfo(String info, Object value) {
		if (info.equals(":smt-lib-version")) {
			final String svalue = String.valueOf(value);
			if ("2.5".equals(svalue) || "2.6".equals(svalue)) {
				mVersion25 = true;
				mLexer.setVersion25(true);
			} else if ("2.0".equals(svalue)) {
				mVersion25 = false;
				mLexer.setVersion25(false);
			} else {
				printError("Unknown SMTLIB version");
			}
		} else if (info.equals(":error-behavior")) {
			if ("immediate-exit".equals(value)) {
				mScript.setOption(":continue-on-error", false);
			} else if ("continued-execution".equals(value)) {
				mScript.setOption(":continue-on-error", true);
			}
		}
		mScript.setInfo(info, value);
	}
	
	public void addGlobal(TermVariable tv, TermVariable primed) {
		final String name = tv.getName();
		mGlobals.put(name, tv);
		mPrimedGlobals.put(name, primed);
	}

	public void addLocal(TermVariable tv, TermVariable primed, TermVariable other, TermVariable otherPrimed) {
		final String name = tv.getName();
		mLocals.put(name, tv);
		mPrimedLocals.put(name, primed);
		mOtherLocals.put(name, other);
		mPrimedOtherLocals.put(name, otherPrimed);
	}

	public void createInvariantSymbol() {
		int components = (int) mCartAbsNumber.getValue();
		ArrayList<Sort> allVars = new ArrayList<>();
		for (TermVariable tv : mGlobals.values()) {
			allVars.add(tv.getSort());
		}
		for (int i = 0; i < components; i++) {
			for (TermVariable tv : mLocals.values()) {
				allVars.add(tv.getSort());
			}
		}
		mScript.declareFun("inv", allVars.toArray(new Sort[allVars.size()]), mScript.sort("Bool"));
		mInvariant = "inv";

		createSymmetryRules();
	}

	private void createSymmetryRule(ArrayList<TermVariable> allVars, ArrayList<TermVariable> reorderVars) {
		Term inv1 = mScript.term(mInvariant, allVars.toArray(new Term[allVars.size()]));
		Term inv2 = mScript.term(mInvariant, reorderVars.toArray(new Term[reorderVars.size()]));
		mScript.assertTerm(mScript.quantifier(Script.FORALL, allVars.toArray(new TermVariable[allVars.size()]),
				mScript.term("=>", inv1, inv2)));
	}

	private void createSymmetryRules() {
		int components = (int) mCartAbsNumber.getValue();
		ArrayList<TermVariable> allVars = new ArrayList<>();
		@SuppressWarnings("unchecked")
		ArrayList<TermVariable>[] localVars = new ArrayList[components];

		allVars.addAll(mGlobals.values());
		for (int i = 0; i < components; i++) {
			localVars[i] = new ArrayList<>();
			for (TermVariable tv : mLocals.values()) {
				localVars[i].add(mScript.variable(tv.getName() + i, tv.getSort()));
			}
			allVars.addAll(localVars[i]);
		}
		ArrayList<TermVariable> reorderVars = new ArrayList<>();
		reorderVars.addAll(mGlobals.values());
		for (int i = 0; i < components; i++) {
			reorderVars.addAll(localVars[i < 2 ? 1 - i : i]);
		}
		createSymmetryRule(allVars, reorderVars);
		if (components > 2) {
			reorderVars.clear();
			reorderVars.addAll(mGlobals.values());
			for (int i = 0; i < components; i++) {
				reorderVars.addAll(localVars[i == components - 1 ? 0 : i + 1]);
			}
			createSymmetryRule(allVars, reorderVars);
		}
	}

	public void ruleInit(Term init) {
		if (mInvariant == null) {
			createInvariantSymbol();
		}
		int components = (int) mCartAbsNumber.getValue();
		ArrayList<TermVariable> allVars = new ArrayList<>();
		allVars.addAll(mGlobals.values());
		Term[] inits = new Term[components];
		for (int i = 0; i < components; i++) {
			ArrayList<TermVariable> letVars = new ArrayList<>();
			for (String lcl: mLocals.keySet()) {
				TermVariable tv = mScript.variable(lcl + i, mLocals.get(lcl).getSort());
				allVars.add(tv);
				letVars.add(tv);
			}
			inits[i] = mScript.let(mLocals.values().toArray(new TermVariable[mLocals.size()]),
					letVars.toArray(new Term[letVars.size()]), init);
		}
		init = mScript.term("and", inits);
		init = mScript.term("=>", init, mScript.term(mInvariant, allVars.toArray(new Term[allVars.size()])));
		init = mScript.quantifier(Script.FORALL, allVars.toArray(new TermVariable[allVars.size()]), init);
		System.err.println("init:" + init);
		mScript.assertTerm(init);
	}

	public void ruleError(String name, Term error) {
		if (mInvariant == null) {
			createInvariantSymbol();
		}
		int components = (int) mCartAbsNumber.getValue();

		ArrayList<TermVariable> allVars = new ArrayList<>();
		@SuppressWarnings("unchecked")
		ArrayList<TermVariable>[] localVars = new ArrayList[components];

		allVars.addAll(mGlobals.values());
		for (int i = 0; i < components; i++) {
			localVars[i] = new ArrayList<>();
			for (TermVariable tv : mLocals.values()) {
				localVars[i].add(mScript.variable(tv.getName() + i, tv.getSort()));
			}
			allVars.addAll(localVars[i]);
		}

		Term error1 = mScript.let(mLocals.values().toArray(new TermVariable[mLocals.size()]),
				localVars[0].toArray(new Term[localVars[0].size()]),
				mScript.let(mOtherLocals.values().toArray(new TermVariable[mLocals.size()]),
						localVars[1].toArray(new Term[localVars[1].size()]), error));
		Term error0 = mScript.let(mLocals.values().toArray(new TermVariable[mLocals.size()]),
				localVars[0].toArray(new Term[localVars[0].size()]),
				mScript.let(mOtherLocals.values().toArray(new TermVariable[mLocals.size()]),
						localVars[0].toArray(new Term[localVars[1].size()]), error));
		if (error0 != error1) {
			mScript.assertTerm(mScript.quantifier(Script.FORALL, allVars.toArray(new TermVariable[allVars.size()]),
					mScript.term("not", mScript.term("and", error0,
							mScript.term(mInvariant, allVars.toArray(new Term[allVars.size()]))))));
		}
		mScript.assertTerm(mScript.quantifier(Script.FORALL, allVars.toArray(new TermVariable[allVars.size()]),
				mScript.term("not", mScript.term("and", error1,
						mScript.term(mInvariant, allVars.toArray(new Term[allVars.size()]))))));
	}

	public Term buildLet(List<TermVariable> vars, List<Term> values, Term body) {
		return mScript.let(vars.toArray(new TermVariable[vars.size()]), values.toArray(new Term[values.size()]), body);
	}

	@SuppressWarnings("unchecked")
	public void ruleStatement(String ruleName, Term stmt) {
		if (mInvariant == null) {
			createInvariantSymbol();
		}
		int components = (int) mCartAbsNumber.getValue();

		TermVariable[] freeVars = stmt.getFreeVars();
		HashSet<TermVariable> freeVarSet = new HashSet<>();
		int flags = 0;
		final int GLOBAL       = 1;
		final int GLOBALPRIMED = 2;
		final int LOCAL        = 4;
		final int LOCALPRIMED  = 8;
		final int OTHER        = 16;
		final int OTHERPRIMED  = 32;
				
		for (TermVariable tv: freeVars) {
			freeVarSet.add(tv);
			if (tv.getName().endsWith("1'")) {
				flags |= OTHERPRIMED;
			} else if (tv.getName().endsWith("1")) {
				flags |= OTHER;
			} else if (tv.getName().endsWith("'")) {
				if (mGlobals.containsKey(tv.getName().substring(0, tv.getName().length() - 1))) {
					flags |= GLOBALPRIMED;
				} else {
					flags |= LOCALPRIMED;
				}
			} else {
				if (mGlobals.containsKey(tv.getName())) {
					flags |= GLOBAL;
				} else {
					flags |= LOCAL;
				}
			}
		}
		
		/* local == other */
		ArrayList<TermVariable> globalPrimed = new ArrayList<>();
		ArrayList<TermVariable> localPrimed = new ArrayList<>();
		ArrayList<TermVariable> otherPrimed = new ArrayList<>();
		ArrayList<TermVariable> commonPrimed = new ArrayList<>();
		ArrayList<String> duplicatedPrimed = new ArrayList<>();
		
		for (String varName : mGlobals.keySet()) {
			if (freeVarSet.contains(mPrimedGlobals.get(varName))) {
				globalPrimed.add(mPrimedGlobals.get(varName));
			} else {
				globalPrimed.add(mGlobals.get(varName));
			}
		}
		ArrayList<TermVariable>[] localVars = new ArrayList[components];
		for (int i = 0; i < components; i++) {
			localVars[i] = new ArrayList<>();
			for (TermVariable tv : mLocals.values()) {
				localVars[i].add(mScript.variable(tv.getName() + "_" + i, tv.getSort()));
			}
		}

		int idx = 0;
		for (String varName : mLocals.keySet()) {
			if (freeVarSet.contains(mPrimedLocals.get(varName))) {
				localPrimed.add(mPrimedLocals.get(varName));
			} else {
				localPrimed.add(localVars[0].get(idx));
			}
			if (freeVarSet.contains(mPrimedOtherLocals.get(varName))) {
				otherPrimed.add(mPrimedOtherLocals.get(varName));
				commonPrimed.add(mPrimedLocals.get(varName));
			} else {
				otherPrimed.add(localVars[1].get(idx));
				if (freeVarSet.contains(mPrimedLocals.get(varName))) {
					commonPrimed.add(mPrimedLocals.get(varName));
				} else {
					commonPrimed.add(localVars[0].get(idx));
				}
			}
			idx++;
		}
		ArrayList<TermVariable> allVars = new ArrayList<>();
		ArrayList<TermVariable> primedVarsNoLocal = new ArrayList<>();
		ArrayList<TermVariable> primedVarsCommon = new ArrayList<>();
		ArrayList<TermVariable> primedVarsLocal = new ArrayList<>();
		ArrayList<TermVariable> primedVarsOther = new ArrayList<>();
		ArrayList<TermVariable> primedVarsLocalOther = new ArrayList<>();
		allVars.addAll(mGlobals.values());
		primedVarsNoLocal.addAll(globalPrimed);
		primedVarsCommon.addAll(globalPrimed);
		primedVarsLocal.addAll(globalPrimed);
		primedVarsOther.addAll(globalPrimed);
		primedVarsLocalOther.addAll(globalPrimed);
		for (int i = 0; i < components; i++) {
			allVars.addAll(localVars[i]);
			primedVarsNoLocal.addAll(localVars[i]);
			primedVarsCommon.addAll(i == 0 ? commonPrimed : localVars[i]);
			primedVarsLocal.addAll(i == 0 ? localPrimed : localVars[i]);
			if (i == 0) {
				for (int j = 0; j < otherPrimed.size(); j++) {
					if (otherPrimed.get(j).getName().endsWith("'")) {
						primedVarsOther.add(otherPrimed.get(j));
					} else {
						primedVarsOther.add(localVars[0].get(j));
					}
				}
			} else {
				primedVarsOther.addAll(localVars[i]);
			}
			primedVarsLocalOther.addAll(i == 0 ? localPrimed : i == 1 ? otherPrimed : localVars[i]);
		}
		
		// g,g',l=o,l'=o'
		buildStatementRule(localVars[0], commonPrimed, localVars[0], commonPrimed, stmt, primedVarsCommon, localVars);
		// g,g' (l=o) if GLOBALPRIMED
		if ((flags & GLOBALPRIMED) != 0) {
			buildStatementRule(mLocals.values(), commonPrimed, mLocals.values(), commonPrimed, stmt, primedVarsNoLocal,
					localVars, mLocals.values());
		}
		if ((flags & (OTHER | OTHERPRIMED)) != 0) {
			// g,g',l,l',o,o'
			buildStatementRule(localVars[0], localPrimed, localVars[1], otherPrimed, stmt, primedVarsLocalOther,
					localVars);
			// g,g',l,l' if LOCALPRIMED | GLOBALPRIMED
			if ((flags & (LOCALPRIMED | GLOBALPRIMED)) != 0) {
				buildStatementRule(localVars[0], localPrimed, mOtherLocals.values(), otherPrimed, stmt, primedVarsLocal,
						localVars, mOtherLocals.values());
			}
			// g,g',o,o' if OTHERPRIMED | GLOBALPRIMED
			if ((flags & (OTHERPRIMED | GLOBALPRIMED)) != 0) {
				buildStatementRule(mLocals.values(), localPrimed, localVars[0], otherPrimed, stmt, primedVarsOther,
						localVars, mLocals.values());
			}
			// g,g' if GLOBALPRIMED
			if ((flags & GLOBALPRIMED) != 0) {
				buildStatementRule(mLocals.values(), localPrimed, mOtherLocals.values(), otherPrimed, stmt,
						primedVarsNoLocal,
						localVars,
						mLocals.values(), mOtherLocals.values());
			}
		}
	}

	private Term buildInvariant(Collection<TermVariable>[] localVars) {
		ArrayList<TermVariable> vars = new ArrayList<>();
		vars.addAll(mGlobals.values());
		for (Collection<TermVariable> locals : localVars) {
			vars.addAll(locals);
		}
		return mScript.term(mInvariant, vars.toArray(new Term[vars.size()]));
	}

	private void buildStatementRule(Collection<TermVariable> local, Collection<TermVariable> localPrimed,
			Collection<TermVariable> other, Collection<TermVariable> otherPrimed,
			Term letBody,
			Collection<TermVariable> goalVars, Collection<TermVariable>[] localVars,
			@SuppressWarnings("unchecked") Collection<TermVariable>... mixins) {
		ArrayList<TermVariable> letVars = new ArrayList<>();
		ArrayList<TermVariable> letValues = new ArrayList<>();
		letVars.addAll(mLocals.values());
		letValues.addAll(local);
		letVars.addAll(mPrimedLocals.values());
		letValues.addAll(localPrimed);
		letVars.addAll(mOtherLocals.values());
		letValues.addAll(other);
		letVars.addAll(mPrimedOtherLocals.values());
		letValues.addAll(otherPrimed);
		Term letTerm = mScript.let(letVars.toArray(new TermVariable[letVars.size()]),
				letValues.toArray(new Term[letValues.size()]), letBody);
		Term goalTerm = mScript.term(mInvariant, goalVars.toArray(new Term[goalVars.size()]));
		ArrayList<Term> lhs = new ArrayList<>();
		if (mixins.length == 0) {
			lhs.add(buildInvariant(localVars));
		} else if (mixins.length == 1) {
			@SuppressWarnings("unchecked")
			Collection<TermVariable>[] dest = new Collection[localVars.length];
			for (int i = -1; i < localVars.length; i++) {
				System.arraycopy(localVars, 0, dest, 0, localVars.length);
				if (i != -1) {
					dest[i] = mixins[0];
				}
				lhs.add(buildInvariant(dest));
			}
		} else if (mixins.length == 1) {
			@SuppressWarnings("unchecked")
			Collection<TermVariable>[] dest = new Collection[localVars.length];
			for (int i = -1; i < localVars.length; i++) {
				for (int j = -1; j < localVars.length; j++) {
					if (j <= i && j != -1) {
						continue;
					}
					System.arraycopy(localVars, 0, dest, 0, localVars.length);
					if (i != -1) {
						dest[i] = mixins[0];
					}
					if (j != -1) {
						dest[j] = mixins[1];
					}
					lhs.add(buildInvariant(dest));
				}
			}
		}
		lhs.add(letTerm);
		Term quantBody = mScript.term("=>", mScript.term("and", lhs.toArray(new Term[lhs.size()])), goalTerm);
		mScript.assertTerm(mScript.quantifier(Script.FORALL, quantBody.getFreeVars(), quantBody));
	}

	public Object getInfo(String info) {
		if (info.equals(":error-behavior")) {
			return mOptions.continueOnError() ? "continued-execution" : "immediate-exit";
		}
		return mScript.getInfo(info);
	}

	public void startTiming() {
		if (mTiming == null) {
			mTiming = new ArrayDeque<Long>();
		}
		mOptions.getOutChannel().print('(');
		mTiming.push(System.nanoTime());
	}
	
	public void endTiming() {
		final long old = mTiming.pop();
		final long duration = System.nanoTime() - old;
		final double secs = duration / 1000000000.0; // NOCHECKSTYLE
		mOptions.getOutChannel().printf((Locale) null, " :time %.3f)", secs);
		mOptions.getOutChannel().println();
		mOptions.getOutChannel().flush();
	}
	
	public boolean isContinueOnError() {
		return mOptions.continueOnError();
	}
}
