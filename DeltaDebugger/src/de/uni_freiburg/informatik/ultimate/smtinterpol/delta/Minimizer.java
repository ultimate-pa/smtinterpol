/*
 * Copyright (C) 2012-2013 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.smtinterpol.delta;

import java.io.File;
import java.io.FileNotFoundException;
import java.io.IOException;
import java.io.InputStream;
import java.io.PrintWriter;
import java.nio.file.Files;
import java.nio.file.StandardCopyOption;
import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.logic.AnnotatedTerm;
import de.uni_freiburg.informatik.ultimate.logic.Annotation;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermTransformer;
import de.uni_freiburg.informatik.ultimate.smtinterpol.DefaultLogger;
import de.uni_freiburg.informatik.ultimate.smtinterpol.delta.TermSimplifier.Mode;
import de.uni_freiburg.informatik.ultimate.smtinterpol.option.OptionMap;
import de.uni_freiburg.informatik.ultimate.smtinterpol.smtlib2.ParseEnvironment;
import de.uni_freiburg.informatik.ultimate.util.datastructures.ScopedHashMap;

public class Minimizer {

	private static class OutputReaper extends Thread implements Runnable {

		private final static int CHUNK_SIZE = 1024;

		private InputStream mToReap;

		public OutputReaper() {
			setDaemon(true);
		}

		@Override
		public void run() {
			final byte[] chunk = new byte[CHUNK_SIZE];
			while (true) {
				try {
					synchronized(this) {
						wait();
					}
				} catch (final InterruptedException eie) {
					// Interrupted while waiting for something to do => terminate
					return;
				}
				if (mToReap == null) {
					// woken up without anything to do => terminate thread
					return;
				}
				try {
					while (mToReap.read(chunk) != -1) {
						;
					}
				} catch (final IOException ignored) {
					// Ignore exception and wait since process died...
				}
				mToReap = null;
			}
		}

		public synchronized void setToReap(final InputStream toReap) {
			mToReap = toReap;
			notifyAll();
		}
	}

	private class DeactivateCmds implements BinSearch.Driver<Cmd> {

		@Override
		public Boolean prepare(final List<Cmd> sublist) {
			if (mVerbosity > 1) {
				System.err.println("Trying " + sublist);
			}
			for (final Cmd cmd : sublist) {
				cmd.deactivate();
			}
			return null;
		}

		@Override
		public void failure(final List<Cmd> sublist) {
			for (final Cmd cmd : sublist) {
				cmd.activate();
			}
		}

		@Override
		public void success(final List<Cmd> sublist) {
			// Commands remain deactivated.  shrinkCmdList will do the cleanup.
		}

	}

	private class SimplifyTerms implements BinSearch.Driver<Substitution> {

		private final AbstractOneTermCmd mCmd;
		private final SubstitutionManager mMgr;
		private final List<Substitution> mSubsts;
		private final HashMap<Term, Boolean> mSeen;
		private List<Cmd> mPres;

		public SimplifyTerms(final AbstractOneTermCmd cmd, final SubstitutionManager mgr,
				final List<Substitution> substs, final HashMap<Term, Boolean> cache) {
			mCmd = cmd;
			mMgr = mgr;
			mSubsts = substs;
			mSeen = cache;
		}

		@Override
		public Boolean prepare(final List<Substitution> sublist) {
			final SubstitutionApplier applier = new SubstitutionApplier();
			for (final Substitution subst : sublist) {
				subst.activate();
			}
			if (mVerbosity > 1) {
				System.err.println("Active substs: " + sublist);
			}
			applier.init(mMgr.getDepth(), mSubsts);
			final Term simp = applier.apply(mCmd.getTerm(mUnletRelet));
			if (mVerbosity > 1) {
				System.err.println("simp = " + simp);
			}
			final Boolean res = mSeen.get(simp);
			if (res != null && !res.booleanValue()) {
				for (final Substitution s : sublist) {
					s.deactivate();
				}
				return res;
			}
			mCmd.setTerm(simp, mUnletRelet);
			mPres = applier.getAdds();
			mCmd.appendPreCmds(mPres);
			if (res != null && res.booleanValue()) {
				success(sublist);
			}
			return res;
		}

		@Override
		public void failure(final List<Substitution> sublist) {
			mSeen.put(mCmd.getTerm(mUnletRelet), Boolean.FALSE);
			mCmd.removePreCmds(mPres);
			mCmd.failure();
			for (final Substitution subst : sublist) {
				subst.deactivate();
			}
			mPres = null;
		}

		@Override
		public void success(final List<Substitution> sublist) {
			mSeen.put(mCmd.getTerm(mUnletRelet), Boolean.TRUE);
			for (final Substitution s : sublist) {
				s.success();
			}
			mCmd.success();
			mPres = null;
		}

	}

	private static class RemoveScopes implements BinSearch.Driver<Scope> {

		private final List<Cmd> mCmds;

		public RemoveScopes(final List<Cmd> cmds) {
			mCmds = cmds;
		}

		@Override
		public Boolean prepare(final List<Scope> sublist) {
			for (final Scope s : sublist) {
				for (int i = s.mFirst; i < s.mLast; ++i) {
					mCmds.get(i).deactivate();
				}
				final ScopeCmd sc = (ScopeCmd) mCmds.get(s.mLast);
				final int remScopes = sc.getNumScopes() - s.mReduce;
				if (remScopes == 0) {
					sc.deactivate();
				} else {
					sc.tryNumScopes(remScopes);
				}
			}
			return null;
		}

		@Override
		public void failure(final List<Scope> sublist) {
			for (final Scope s : sublist) {
				for (int i = s.mFirst; i < s.mLast; ++i) {
					mCmds.get(i).activate();
				}
				final ScopeCmd sc = (ScopeCmd) mCmds.get(s.mLast);
				if (sc.isActive()) {
					sc.reset();
				} else {
					sc.activate();
				}
			}
		}

		@Override
		public void success(final List<Scope> sublist) {
			for (final Scope s : sublist) {
				s.mDeactivated = true;
			}
		}

	}

	private final class RemoveNeutrals implements BinSearch.Driver<Neutral> {

		private final AbstractOneTermCmd mCmd;

		public RemoveNeutrals(final AbstractOneTermCmd cmd) {
			mCmd = cmd;
		}

		@Override
		public Boolean prepare(final List<Neutral> sublist) {
			if (mVerbosity > 1) {
				System.err.println("Trying " + sublist);
			}
			final Term rem = new NeutralRemover(sublist).removeNeutrals(mCmd.getTerm(mUnletRelet));
			if (mVerbosity > 1) {
				System.err.println("Result: " + rem);
			}
			mCmd.setTerm(rem, mUnletRelet);
			return null;
		}

		@Override
		public void failure(final List<Neutral> sublist) {
			mCmd.failure();
		}

		@Override
		public void success(final List<Neutral> sublist) {
			mCmd.success();
		}

	}

	private List<Cmd> mCmds;
	private final int mGoldenExit;
	private final File mTmpFile, mResultFile;
	private final String mSolver;

	private int mTestCtr = 0, mSuccTestCtr = 0;
	/**
	 * The verbosity level for the delta debugger.  Values are:
	 * <th><td>level</td><td>meaning</td></th>
	 * <tr><td>0</td><td>only final statistics</td></tr>
	 * <tr><td>1</td><td>print current and successful phases</td></tr>
	 * <tr><td>2</td><td>print also debugging information for phases</td></tr>
	 * <tr><td>&gt;2</td><td>print also debugging information about tests</td></tr>
	 */
	private final int mVerbosity;

	private final OutputReaper mOut, mErr;

	private final boolean mUnletRelet;

	public Minimizer(final List<Cmd> cmds, final int goldenExit,
			final File tmpFile, final File resultFile, final String solver, final int verbosity,
			final OutputReaper out, final OutputReaper err, final boolean unletRelet) {
		mCmds = cmds;
		mGoldenExit = goldenExit;
		mTmpFile = tmpFile;
		mResultFile = resultFile;
		mSolver = solver;
		mVerbosity = verbosity;
		mOut = out;
		mErr = err;
		mUnletRelet = unletRelet;
	}

	public boolean deltaDebug() throws IOException, InterruptedException {
		if (mVerbosity > 0) {
			System.err.println("# commands: " + mCmds.size());
		}
		int numRounds = 0;
		boolean cmds = false, terms = false, bindings = false, neutrals = false,
				lists = false, ips = false, decls = false;
		final boolean scopes = removeScopes();
		do {
			cmds = removeCmds();
			terms = simplifyTerms(true);
			decls = removeDecls();
			shrinkCmdList();
			terms = simplifyTerms(false);
			bindings = removeBindings();
			neutrals = removeNeutrals();
			lists = simplifyTermListCmds();
			ips = simplifyGetInterpolants();
			decls = removeDecls() || decls;
			// Not needed anymore since I don't do further tests...
	//		shrinkCmdList();
			++numRounds;
			if (mVerbosity > 0) {
				if (cmds) {
					System.err.println("Removed commands");
				}
				if (terms) {
					System.err.println("Simplified terms");
				}
				if (bindings) {
					System.err.println("Removed bindings");
				}
				if (neutrals) {
					System.err.println("Removed neutrals");
				}
				if (lists) {
					System.err.println("Simplifed term command lists");
				}
				if (ips) {
					System.err.println("Simplified get-interpolants");
				}
				if (decls) {
					System.err.println("Removed declarations");
				}
			}
		} while (
				cmds || terms || bindings || neutrals || lists || ips || decls);
		final boolean features = removeFeatures();
		System.err.println("# tests: " + mTestCtr);
		System.err.println("# successful tests: " + mSuccTestCtr);
		System.err.println("# rounds: " + numRounds);
		return scopes || numRounds > 1 || features;
	}

	private static class Scope {
		int mFirst;
		int mLast;
		int mReduce;
		List<Scope> mNested;
		boolean mDeactivated = false;
		public Scope(final int f) {
			mFirst = f;
		}
		public void nest(final Scope s) {
			if (mNested == null) {
				mNested = new ArrayList<>();
			}
			mNested.add(s);
		}
	}

	private List<Scope> detectScopes() {
		final ArrayDeque<Scope> ppStack = new ArrayDeque<>();
		// All toplevel scopes.
		final List<Scope> res = new ArrayList<>();
		for (int i = 0; i < mCmds.size(); ++i) {
			final Cmd cmd = mCmds.get(i);
			if (!cmd.isActive()) {
				continue;
			}
			if (cmd instanceof ScopeCmd) {
				final ScopeCmd sc = (ScopeCmd) cmd;
				if (sc.isScopeStart()) {
					if (mVerbosity > 1) {
						System.err.println("Found scope start at " + i);
					}
					final Scope s = new Scope(i);
					for (int n = 0; n < sc.getNumScopes(); ++n) {
						ppStack.push(s);
					}
				} else {
					if (mVerbosity > 1) {
						System.err.println("Found scope end at " + i);
					}
					for (int n = 0; n < sc.getNumScopes(); ++n) {
						final Scope last = ppStack.pop();
						final Scope next = ppStack.peek();
						// We have found a scope end...
						last.mLast = i;
						last.mReduce = n + 1;
						if (next == null) {
							// toplevel scope
							res.add(last);
						} else if (last != next) {
							next.nest(last);
						}
					}
				}
			}
		}
		return res;
	}

	private boolean removeScopes() throws IOException, InterruptedException {
		if (mVerbosity > 0) {
			System.err.println("Removing scopes...");
		}
		boolean res = false;
		final ArrayDeque<List<Scope>> todo = new ArrayDeque<>();
		todo.push(detectScopes());
		while (!todo.isEmpty()) {
			final List<Scope> scopes = todo.pop();
			final BinSearch<Scope> bs = new BinSearch<>(
					scopes, new RemoveScopes(mCmds));
			res |= bs.run(this);
			for (final Scope s : scopes) {
				if (!s.mDeactivated && s.mNested != null) {
					todo.push(s.mNested);
				}
			}
		}
		if (mVerbosity > 0) {
			System.err.println("...done");
		}
		return res;
	}

	private boolean removeCmds() throws IOException, InterruptedException {
		if (mVerbosity > 0) {
			System.err.println("Removing commands...");
		}
		final List<Cmd> cmds = new ArrayList<>();
		for (int i = 0; i < mCmds.size(); ++i) {
			final Cmd cmd = mCmds.get(i);
			if (!cmd.isActive()) {
				continue;
			}
			if (cmd.canBeRemoved() && !cmd.hasDefinitions()) {
				cmds.add(cmd);
			}
		}
		final boolean res = deactivateCmds(cmds);
		if (mVerbosity > 0) {
			System.err.println("...done");
		}
		return res;
	}

	private boolean deactivateCmds(final List<Cmd> toDeactivate)
		throws IOException, InterruptedException {
		final DeactivateCmds driver = new DeactivateCmds();
		final BinSearch<Cmd> bs = new BinSearch<>(toDeactivate, driver);
		return bs.run(this);
	}

	private boolean removeDecls() throws IOException, InterruptedException {
		if (mVerbosity > 0) {
			System.err.println("Removing unused declarations...");
		}
		// Collect used definitions
		ScopedHashMap<String, Cmd> definitions =
				new ScopedHashMap<>();
		final Set<Cmd> usedDefs = new HashSet<>();
		for (final Cmd cmd : mCmds) {
			if (!cmd.isActive()) {
				continue;
			}
			cmd.addUsedDefinitions(definitions, usedDefs);
			if (cmd.hasDefinitions()) {
				cmd.insertDefinitions(definitions);
			}
			if (cmd instanceof ScopeCmd) {
				final ScopeCmd scope = (ScopeCmd) cmd;
				if (scope.isScopeStart()) {
					for (int i = 0; i < scope.getNumScopes(); ++i) {
						definitions.beginScope();
					}
				} else {
					for (int i = 0; i < scope.getNumScopes(); ++i) {
						definitions.endScope();
					}
				}
			}
		}
		// Free some space...
		definitions = null;
		// Collect unused definitions
		final List<Cmd> unusedDefs = new ArrayList<>();
		for (final Cmd cmd : mCmds) {
			if (!cmd.isActive()) {
				continue;
			}
			if (cmd.hasDefinitions() && !usedDefs.contains(cmd)) {
				unusedDefs.add(cmd);
			}
			if (cmd instanceof AbstractOneTermCmd) {
				for (final Cmd pre : ((AbstractOneTermCmd) cmd).getPreCmds()) {
					if (pre.isActive() && pre.hasDefinitions()
							&& !usedDefs.contains(pre)) {
						unusedDefs.add(pre);
					}
				}
			}
		}
		boolean res = deactivateCmds(unusedDefs);
		// Now, we have deactivated all unused definitions that can be
		// removed completely from the input.  But unfortunately some of these
		// definitions might be :named annotations and we still need the term!
		// Try to only remove the annotation.
		for (final Iterator<Cmd> it = unusedDefs.iterator(); it.hasNext(); ) {
			final Cmd next = it.next();
			if (!next.isActive() || !isNamedAssert(next)) {
				it.remove();
			}
		}
		final BinSearch<Cmd> bs = new BinSearch<>(
				unusedDefs, new BinSearch.Driver<Cmd>() {

			@Override
			public Boolean prepare(final List<Cmd> sublist) {
				for (final Cmd cmd : sublist) {
					final OneTermCmd tcmd = (OneTermCmd) cmd;
					final Term stripped = new TermTransformer() {

						@Override
						public void postConvertAnnotation(final AnnotatedTerm old,
								final Annotation[] newAnnots, final Term newBody) {
							final ArrayList<Annotation> noNames =
									new ArrayList<>(newAnnots.length);
							for (final Annotation a : newAnnots) {
								if (!a.getKey().equals(":named")) {
									noNames.add(a);
								}
							}
							setResult(noNames.isEmpty() ? newBody
								: old.getTheory().annotatedTerm(noNames.toArray(
										new Annotation[noNames.size()]),
										newBody));
						}

					}.transform(tcmd.getTerm(mUnletRelet));// NOCHECKSTYLE
					tcmd.setTerm(stripped, mUnletRelet);
				}
				return null;
			}

			@Override
			public void failure(final List<Cmd> sublist) {
				for (final Cmd cmd : sublist) {
					((OneTermCmd) cmd).failure();
				}
			}

			@Override
			public void success(final List<Cmd> sublist) {
				for (final Cmd cmd : sublist) {
					((OneTermCmd) cmd).success();
				}
			}

		});// NOCHECKSTYLE
		res |= bs.run(this);
		if (mVerbosity > 0) {
			System.err.println("...done");
		}
		return res;
	}

	private boolean isUnnamedAssert(final AbstractOneTermCmd cmd) {
		return (cmd instanceof OneTermCmd)
				&& ((OneTermCmd) cmd).getCmd().equals("assert")
				&& !cmd.hasDefinitions();
	}

	private boolean isNamedAssert(final Cmd cmd) {
		if (cmd instanceof OneTermCmd) {
			final OneTermCmd tcmd = (OneTermCmd) cmd;
			if (tcmd.getCmd().equals("assert")
					&& tcmd.getTerm(false) instanceof AnnotatedTerm) {
				for (final Annotation a : ((AnnotatedTerm) tcmd.getTerm(false)).
						getAnnotations()) {
					if (a.getKey().equals(":named")) {
						return true;
					}
				}
			}
		}
		return false;
	}

	private boolean removeUnusedCore(final Mode mode)
		throws IOException, InterruptedException {
		boolean res = false;
		final TermSimplifier simp = new TermSimplifier(mode);
		for (final Cmd cmd : mCmds) {
			if (!cmd.isActive() || !(cmd instanceof AbstractOneTermCmd)) {
				continue;
			}
			final AbstractOneTermCmd tcmd = (AbstractOneTermCmd) cmd;
			final Term s = simp.transform(tcmd.getTerm(mUnletRelet));
			if (s != tcmd.getTerm(mUnletRelet)) {
				tcmd.setTerm(s, mUnletRelet);
				if (test()) {
					res = true;
					tcmd.success();
				} else {
					tcmd.failure();
				}
			}
		}
		return res;
	}

	private boolean removeBindings() throws IOException, InterruptedException {
		return removeUnusedCore(Mode.BINDINGS);
	}

	private boolean removeNeutrals() throws IOException, InterruptedException {
//		return removeUnusedCore(Mode.NEUTRALS);
		boolean result = false;
		for (final Cmd cmd : mCmds) {
			if (!cmd.isActive() || !(cmd instanceof AbstractOneTermCmd)) {
				continue;
			}
			final AbstractOneTermCmd tcmd = (AbstractOneTermCmd) cmd;
			final List<Neutral> neutrals = new NeutralDetector().detect(tcmd.getTerm(mUnletRelet));
			if (neutrals.isEmpty()) {
				continue;
			}
			final RemoveNeutrals driver = new RemoveNeutrals(tcmd);
			final BinSearch<Neutral> bs = new BinSearch<>(neutrals, driver);
			result |= bs.run(this);
		}
		return result;
	}

	private boolean simplifyTerms(final boolean simpAsserts) throws IOException, InterruptedException {
		if (mVerbosity > 0) {
			System.err.println("Simplifying terms...");
		}
		boolean res = false;
		for (final Cmd cmd : mCmds) {
			if (!cmd.isActive() || !(cmd instanceof AbstractOneTermCmd)
					|| (simpAsserts ^ (cmd instanceof OneTermCmd && ((OneTermCmd) cmd).getCmd().equals("assert")))) {
				continue;
			}
			boolean localres = false;
			final AbstractOneTermCmd tcmd = (AbstractOneTermCmd) cmd;
			final SubstitutionManager substmgr =
					new SubstitutionManager(tcmd, mUnletRelet);
			// Try to simplify this one command...
			if (isUnnamedAssert(tcmd)) {
				// We should not substitute the top level
				substmgr.deepen();
			}
			final HashMap<Term, Boolean> testCache = new HashMap<>();
			deepen: while (substmgr.deepen()) {// NOCHECKSTYLE
				List<Substitution> substs;
				do {
					substs = substmgr.getSubstitutions();
					if (substs.isEmpty()) {
						continue deepen;
					}
					if (mVerbosity > 1) {
						System.err.println("Term: " + tcmd.getTerm(false));
						System.err.println("Substs: " + substs);
					}
					final SimplifyTerms driver = new SimplifyTerms(
							tcmd, substmgr, substs, testCache);
					final BinSearch<Substitution> bs =
							new BinSearch<>(substs, driver);
					localres |= bs.run(this);
				} while (substmgr.failed());
			}
			res |= localres;
		} // Cmd-loop
		if (mVerbosity > 0) {
			System.err.println("...done");
		}
		return res;
	}

	private Term unfoldAnd(final Term p1, final Term p2) {
		final ArrayList<Term> conjuncts = new ArrayList<>();
		ApplicationTerm at = (ApplicationTerm) p1;
		if (at.getFunction() == at.getTheory().mAnd) {
			conjuncts.addAll(Arrays.asList(at.getParameters()));
		} else {
			conjuncts.add(p1);
		}
		at = (ApplicationTerm) p2;
		if (at.getFunction() == at.getTheory().mAnd) {
			conjuncts.addAll(Arrays.asList(at.getParameters()));
		} else {
			conjuncts.add(p2);
		}
		return p1.getTheory().term("and",
				conjuncts.toArray(new Term[conjuncts.size()]));
	}

	private int numChildren(final int[] sos, final int parent) {
		int numChildren = 0;
		int child = parent - 1;
		while (child >= sos[parent]) {
			++numChildren;
			child = sos[child] - 1;
		}
		return numChildren;
	}

	private void mergeWithChild(final GetInterpolants gi, final int parent, int child) {
		final int[] sos = gi.getStartOfSubtree();
		int childidx = parent - 1;
		for (/* Nothing */ ; child > 0; --child) {
			childidx = sos[childidx];
		}
		final Term[] partition = gi.getPartition();
		final Term[] newPartition = new Term[partition.length - 1];
		final int[] newSos = new int[sos.length - 1];
		int diff = 0;
		for (int i = 0; i < partition.length; ++i) {
			if (i == childidx) {
				diff = 1;
			} else if (i == parent) {
				newPartition[i - diff] =
						unfoldAnd(partition[childidx], partition[parent]);
				newSos[i - diff] = Math.max(sos[i] - 1, 0);
			} else {
				newPartition[i - diff] = partition[i];
				newSos[i - diff] = Math.max(sos[i] - 1, 0);
			}
		}
		gi.setNewPartition(newPartition);
		gi.setNewStartOfSubtree(newSos);
	}

	private boolean mergeTree(final GetInterpolants gi)
		throws IOException, InterruptedException {
		boolean res = false;
		int[] sos = gi.getStartOfSubtree();
		int n = sos.length;
		for (int i = 1; i < n; ++i) {
			//@ invariant n == gi.getPartition().length && 0<= i <= n
			// invariant n >= 2 is hidden in assumption about interpolation tree
			int children = numChildren(sos, i);
			for (int child = 0; child < children; /*Nothing*/) {
				//@ invariant 0 <= child <= children
				//@ invariant old(children) >= children
				//@ invariant n == gi.getPartition().length
				//@ invariant i <= n
				// invariant n >= 2 see above
				if (n == 2) {
					// No further merge possible!
					return res;
				}
				mergeWithChild(gi, i, child);
				if (test()) {
					res = true;
					gi.success();
					sos = gi.getStartOfSubtree();
					--i;
					--n;
					--children;
				} else {
					gi.failure();
					++child;
				}
			}
		}
		return res;
	}

	private boolean isAnd(final Term t) {
		return ((ApplicationTerm) t).getFunction() == t.getTheory().mAnd;
	}

	private boolean simplifyAndParition(final GetInterpolants gi, final int idx) throws IOException, InterruptedException {
		Term[] partition = gi.getPartition();
		Term[] conjs =
				((ApplicationTerm) partition[idx]).getParameters();
		int c = 0;
		boolean res = false;
		while (c < conjs.length) {
			final ArrayList<Term> newcs =
					new ArrayList<>(conjs.length - 1);
			for (int j = 0; j < conjs.length; ++j) {
				if (j != c) {
					newcs.add(conjs[j]);
				}
			}
			final Term[] newPartition = partition.clone();
			newPartition[idx] = buildAnd(newcs);
			gi.setNewPartition(newPartition);
			gi.setNewStartOfSubtree(gi.getStartOfSubtree());
			if (test()) {
				gi.success();
				conjs = ((ApplicationTerm) newPartition[idx]).
						getParameters();
				partition = newPartition;
				res = true;
				// Don't increment c since we shifted elements
			} else {
				gi.failure();
				++c;
			}
		}
		return res;
	}

	private boolean simplifyInterpolantPartitions(final GetInterpolants gi)
		throws IOException, InterruptedException {
		boolean res = false;
		Term[] partition = gi.getPartition();
		if (partition.length == 2) {
			if (isAnd(partition[0])) {
				res |= simplifyAndParition(gi, 0);
			}
			if (isAnd(partition[1])) {
				res |= simplifyAndParition(gi, 1);
			}
			return res;
		}
		int i = 0;
		while (i < partition.length) {
			// Try to remove partition i
			// 1. complete
			final int newlength = partition.length - 1;
			if (newlength < 2) {
				// We cannot remove anything anymore!!!
				return res;
			}
			final Term[] newPartition = new Term[newlength];
			final int[] newSos = new int[newlength];
			final int[] sos = gi.getStartOfSubtree();
			int diff = 0;
			for (int j = 0; j < partition.length; ++j) {
				if (j == i) {
					diff = 1;
				} else {
					newPartition[j - diff] = partition[j];
					newSos[j - diff] = Math.max(0, sos[j] - diff);
				}
			}
			gi.setNewPartition(newPartition);
			gi.setNewStartOfSubtree(newSos);
			if (test()) {
				gi.success();
				partition = newPartition;
				res = true;
				// Don't increment i since we shifted a new element here
			} else {
				gi.failure();
				// 2. If conjunctive partition, try to simplify conjunction
				if (isAnd(partition[i])) {
					res |= simplifyAndParition(gi, i);
				}
				++i;
			}
		}
		return res;
	}

	private static ApplicationTerm buildAnd(final List<Term> conjs) {
		if (conjs.isEmpty()) {
			return null;
		}
		if (conjs.size() == 1) {
			return (ApplicationTerm) conjs.get(0);
		}
		return (ApplicationTerm) conjs.get(0).getTheory().term(
				"and", conjs.toArray(new Term[conjs.size()]));
	}

	private boolean simplifyGetInterpolants()
		throws IOException, InterruptedException {
		if (mVerbosity > 0) {
			System.err.println("Simplifying get-interpolants...");
		}
		boolean res = false;
		final Map<Term, Term> actualNames = new HashMap<>();
		for (final Cmd cmd : mCmds) {
			if (!cmd.isActive()) {
				continue;
			}
			if (cmd instanceof GetInterpolants) {
				final GetInterpolants gi = (GetInterpolants) cmd;
				res |= simplifyInterpolantPartitions(gi);
				// This should be superseded by simplifyInterpolantPartitions
//				res |= removeTruePartitions(gi, actualNames);
				// This should be superseded by mergeTree
//				res |= mergeSequential(gi);
				res |= mergeTree(gi);
			} else if (isNamedAssert(cmd)) {
				final AbstractOneTermCmd tcmd = (AbstractOneTermCmd) cmd;
				final AnnotatedTerm t = (AnnotatedTerm) tcmd.getTerm(false);
				final Term v = t.getSubterm();
				for (final Annotation a : t.getAnnotations()) {
					if (a.getKey().equals(":named")) {
						actualNames.put(
								t.getTheory().term(a.getValue().toString()), v);
					}
				}
			}
		}
		if (mVerbosity > 0) {
			System.err.println("...done");
		}
		return res;
	}

	private boolean simplifyTermListCmds()
		throws IOException, InterruptedException {
		if (mVerbosity > 0) {
			System.err.println("Simplifying term list commands...");
		}
		final List<TermListCmd> cmds = new ArrayList<>();
		for (final Cmd cmd : mCmds) {
			if (!cmd.isActive()) {
				continue;
			}
			if (cmd instanceof TermListCmd) {
				final TermListCmd tcmd = (TermListCmd) cmd;
				if (tcmd.getTerms().length > 1) {
					cmds.add(tcmd);
				}
			}
		}
		if (cmds.isEmpty()) {
			if (mVerbosity > 0) {
				System.err.println("...done");
			}
			return false;
		}
		// Try to reduce number of terms in the list
		// First try to reduce all cmds to their lower half terms.
		boolean goon = true;
		boolean res = false;
		while (goon) {
			goon = false;
			for (final TermListCmd cmd : cmds) {
				final Term[] terms = cmd.getTerms();
				final Term[] newTerms = new Term[terms.length / 2];
				System.arraycopy(terms, 0, newTerms, 0, newTerms.length);
				cmd.setNewTerms(newTerms);
			}
			if (test()) {
				for (final TermListCmd cmd : cmds) {
					cmd.success();
				}
				res = true;
				goon = true;
			} else {
				// We had a failure => Try to reduce to the other half
				for (final TermListCmd cmd : cmds) {
					cmd.failure();
					final Term[] terms = cmd.getTerms();
					final int len = terms.length - terms.length / 2;
					final Term[] newTerms = new Term[len];
					System.arraycopy(terms, terms.length / 2, newTerms, 0,
							newTerms.length);
					cmd.setNewTerms(newTerms);
				}
				if (test()) {
					for (final TermListCmd cmd : cmds) {
						cmd.success();
					}
					res = true;
					goon = true;
				} else {
					for (final TermListCmd cmd : cmds) {
						cmd.failure();
					}
					// Both reductions failed => give up
					if (mVerbosity > 0) {
						System.err.println("...done");
					}
					return res;
				}
			}
		}
		// Actually dead code, but required by the java compiler
		return res;
	}

	private void shrinkCmdList() {
		if (mVerbosity > 0) {
			System.err.println("Shrinking command list...");
		}
		int newsize = 0;
		for (final Iterator<Cmd> it = mCmds.iterator(); it.hasNext(); ) {
			if (it.next().isActive()) {
				++newsize;
			}
		}
		if (mVerbosity > 1) {
			System.err.println(mCmds.size() + " -> " + newsize);
		}
		final List<Cmd> tmp = new ArrayList<>(newsize);
		for (final Iterator<Cmd> it = mCmds.iterator(); it.hasNext(); ) {
			final Cmd cmd = it.next();
			if (cmd.isActive()) {
				tmp.add(cmd);
			}
		}
		mCmds = tmp;
		if (mVerbosity > 0) {
			System.err.println("...done");
		}
	}

	private boolean removeFeatures() throws IOException, InterruptedException {
		final Map<String, Cmd> features = new HashMap<>();
		for (final Cmd cmd : mCmds) {
			if (cmd.isActive()) {
				final String feature = cmd.provideFeature();
				if (feature != null) {
					if (mVerbosity > 1) {
						System.err.println("Found feature " + feature);
					}
					features.put(feature, cmd);
				}
			}
		}
		for (final Cmd cmd : mCmds) {
			if (cmd.isActive()) {
				cmd.checkFeature(features);
			}
		}
		final List<Cmd> featureProvider = new ArrayList<>(features.values());
		if (mVerbosity > 1) {
			System.err.println("Trying to remove features " + featureProvider);
		}
		return deactivateCmds(featureProvider);
	}

	/**
	 * Test a modified input script for error reproduction.
	 * @return Did the error still occur?
	 * @throws IOException
	 * @throws InterruptedException
	 */
	boolean test() throws IOException, InterruptedException {
		++mTestCtr;
		if (mVerbosity > 2) {
			System.err.println("Dumping...");
		}
		dumpCmds();
		if (mVerbosity > 2) {
			System.err.println("Testing...");
		}
		final Process p = Runtime.getRuntime().exec(mSolver);
		mOut.setToReap(p.getInputStream());
		mErr.setToReap(p.getErrorStream());
		final int exitVal = p.waitFor();
		if (exitVal == mGoldenExit) {
			++mSuccTestCtr;
			if (mVerbosity > 2) {
				System.err.println("Success");
			}
			Files.copy(mTmpFile.toPath(), mResultFile.toPath(),
					StandardCopyOption.REPLACE_EXISTING);
			return true;
		}
		if (mVerbosity > 2) {
			System.err.println("Failure");
		}
		return false;
	}

	private void dumpCmds() throws FileNotFoundException {
		final PrintWriter out = new PrintWriter(mTmpFile);
		for (final Cmd cmd : mCmds) {
			if (cmd.isActive()) {
				cmd.dump(out);
			}
		}
		out.flush();
		out.close();
	}

	public static void usage() {
		System.err.println(
				"Usage: Minimizer <infile> <outfile> [-v] [-golden <num>] <command> <args>");
		System.err.println("where");
		System.err.println("  infile        is the original input file");
		System.err.println("  outfile       is the desired output file");
		System.err.println("  command       is the command to start the solver");
		System.err.println("  -golden <num> sets expected exit code to \"num\" and safes initial test");
		System.err.println("  -v            make output more verbose (can be repeated)");
		System.err.println("  -u            forces all terms to be unlet and (potentially) reletted");
		System.err.println("  args          are optional arguments to \"command\"");
		System.exit(0);
	}

	public static void main(final String[] args) {
		if (args.length < 3) {
			usage();
		}
		int goldenExit = 0;
		final String infile = args[0];
		final String outfile = args[1];
		int cmdstart = 2;
		int arg = 2;
		boolean foundArg = true;
		int verbosity = 0;
		boolean unletReletMode = false;
		while (foundArg && arg < args.length) {
			foundArg = false;
			if (args[arg].equals("-v")) {
				++verbosity;
				++arg;
				foundArg = true;
			} else if (args[arg].equals("-golden")) {
				if (++arg == args.length) {
					usage();
				}
				try {
					goldenExit = Integer.parseInt(args[arg]);
				} catch (final NumberFormatException eNAN) {
					usage();
				}
				foundArg = true;
				++arg;
			} else if (args[arg].equals("-u")) {
				unletReletMode = true;
				++arg;
				foundArg = true;
			}
		}
		cmdstart = arg;
		StringBuilder command = new StringBuilder();
		if (cmdstart >= args.length) {
			usage();
		}
		for (int i = cmdstart; i < args.length; ++i) {
			command.append(args[i]).append(' ');
		}
		final File resultFile = new File(outfile);
		try {
			final File tmpFile = File.createTempFile("minimize", ".smt2");
			tmpFile.deleteOnExit();
			final File input = new File(infile);
			command.append(tmpFile.getAbsolutePath());
			final String solver = command.toString();
			// Free space
			command = null;
			// Start the output reapers
			final OutputReaper out = new OutputReaper();
			final OutputReaper err = new OutputReaper();
			out.start();
			err.start();
			if (goldenExit == 0) {
				Files.copy(input.toPath(), tmpFile.toPath(),
						StandardCopyOption.REPLACE_EXISTING);
				if (verbosity > 2) {
					System.err.println("Starting " + solver);
				}
				Process p = Runtime.getRuntime().exec(solver);
				out.setToReap(p.getInputStream());
				err.setToReap(p.getErrorStream());
				goldenExit = p.waitFor();
				// Free space
				p = null;
			}
			if (verbosity > 0) {
				System.err.println("Got golden exit code: " + goldenExit);
			}
			ParseScript ps = new ParseScript();
			ParseEnvironment pe = new ParseEnvironment(ps, new OptionMap(new DefaultLogger(), true)) {
				@Override
				public void printResponse(final Object response) {
					// Disable output
				}
			};
			if (verbosity > 0) {
				System.err.println("Begin parsing");
			}
			pe.parseScript(infile);
			// Free space
			pe = null;
			if (verbosity > 0) {
				System.err.println("Parsing done");
			}
			final Minimizer mini = new Minimizer(
					ps.getCmds(), goldenExit, tmpFile, resultFile, solver,
					verbosity, out, err, unletReletMode);
			// Free space
			ps = null;
			if (!mini.deltaDebug()) {
				System.err.println("Failed to minimize");
			}
			// Gracefully terminate our threads.
			out.setToReap(null);
			err.setToReap(null);
			out.join();
			err.join();
		} catch (final IOException e) {
			e.printStackTrace();
		} catch (final InterruptedException e) {
			e.printStackTrace();
		}
	}

}
