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
import de.uni_freiburg.informatik.ultimate.smtinterpol.delta.TermSimplifier.Mode;
import de.uni_freiburg.informatik.ultimate.smtinterpol.smtlib2.ParseEnvironment;
import de.uni_freiburg.informatik.ultimate.util.ScopedHashMap;

public class Minimizer {
	
	private static class OutputReaper extends Thread implements Runnable {

		private final static int CHUNK_SIZE = 1024;
		
		private final InputStream mToReap;
		
		public OutputReaper(InputStream toReap) {
			mToReap = toReap;
			setDaemon(true);
		}
		
		@Override
		public void run() {
			byte[] chunk = new byte[CHUNK_SIZE];
			try {
				while (mToReap.read(chunk) != -1) ;
			} catch (IOException ignored) {
				// Ignore exception and terminate since process died...
			}
			System.err.println("OutputReaper terminating");
			
		}
		
	}
	
	private static class DeactivateCmds implements BinSearch.Driver<Cmd> {

		@Override
		public void prepare(List<Cmd> sublist) {
			System.err.println("Trying " + sublist);
			for (Cmd cmd : sublist)
				cmd.deactivate();
		}

		@Override
		public void failure(List<Cmd> sublist) {
			for (Cmd cmd : sublist)
				cmd.activate();
		}

		@Override
		public void success(List<Cmd> sublist) {
			// Commands remain deactivated.  shrinkCmdList will do the cleanup.
		}
		
	}
	
	private static class SimplifyTerms 
		implements BinSearch.Driver<Substitution> {

		private final AbstractOneTermCmd mCmd;
		private final SubstitutionManager mMgr;
		private final List<Substitution> mSubsts;
		private List<Cmd> mPres;
		
		public SimplifyTerms(AbstractOneTermCmd cmd, SubstitutionManager mgr,
				List<Substitution> substs) {
			mCmd = cmd;
			mMgr = mgr;
			mSubsts = substs;
		}
		
		@Override
		public void prepare(List<Substitution> sublist) {
			SubstitutionApplier applier = new SubstitutionApplier();
			for (Substitution subst : sublist)
				subst.activate();
			System.err.println("Active substs: " + sublist); 	
			applier.init(mMgr.getDepth(), mSubsts);
			Term simp = applier.apply(mCmd.getTerm());
			System.err.println("simp = " + simp);
			mCmd.setTerm(simp);
			mPres = applier.getAdds();
			mCmd.appendPreCmds(mPres);
		}

		@Override
		public void failure(List<Substitution> sublist) {
			mCmd.removePreCmds(mPres);
			mCmd.failure();
			for (Substitution subst : sublist)
				subst.deactivate();
			mPres = null;
		}

		@Override
		public void success(List<Substitution> sublist) {
			for (Substitution s : sublist)
				s.success();
			mCmd.success();
			mPres = null;
		}
		
	}
	
	private static class RemoveScopes implements BinSearch.Driver<Scope> {
		
		private final List<Cmd> mCmds;
		
		public RemoveScopes(List<Cmd> cmds) {
			mCmds = cmds;
		}

		@Override
		public void prepare(List<Scope> sublist) {
			for (Scope s : sublist) {
				for (int i = s.mFirst; i < s.mLast; ++i)
					mCmds.get(i).deactivate();
				ScopeCmd sc = (ScopeCmd) mCmds.get(s.mLast);
				int remScopes = sc.getNumScopes() - s.mReduce;
				if (remScopes == 0)
					sc.deactivate();
				else
					sc.tryNumScopes(remScopes);
			}
		}

		@Override
		public void failure(List<Scope> sublist) {
			for (Scope s : sublist) {
				for (int i = s.mFirst; i < s.mLast; ++i)
					mCmds.get(i).activate();
				ScopeCmd sc = (ScopeCmd) mCmds.get(s.mLast);
				if (sc.isActive())
					sc.reset();
				else
					sc.activate();
			}
		}

		@Override
		public void success(List<Scope> sublist) {
			for (Scope s : sublist)
				s.mDeactivated = true;
		}
		
	}
	
	private final List<Cmd> mCmds;
	private final int mGoldenExit;
	private final File mTmpFile, mResultFile;
	private final String mSolver;
	
	private int mTestCtr = 0, mSuccTestCtr = 0;
	
	public Minimizer(List<Cmd> cmds, int goldenExit,
			File tmpFile, File resultFile, String solver) {
		mCmds = cmds;
		mGoldenExit = goldenExit;
		mTmpFile = tmpFile;
		mResultFile = resultFile;
		mSolver = solver;
	}
	
	public boolean deltaDebug() throws IOException, InterruptedException {
		System.err.println("# commands: " + mCmds.size());
		int numRounds = 0;
		boolean cmds, terms, bindings, neutrals, lists, ips, decls;
		boolean scopes = removeScopes();
		do {
			cmds = removeCmds();
			shrinkCmdList();
			terms = simplifyTerms();
			bindings = removeBindings();
			neutrals = removeNeutrals();
			lists = simplifyTermListCmds();
			ips = simplifyGetInterpolants();
			decls = removeDecls();
			// Not needed anymore since I don't do further tests...
	//		shrinkCmdList();
			++numRounds;
			if (cmds)
				System.err.println("Removed commands");
			if (terms)
				System.err.println("Simplified terms");
			if (bindings)
				System.err.println("Removed bindings");
			if (neutrals)
				System.err.println("Removed neutrals");
			if (lists)
				System.err.println("Simplifed term command lists");
			if (ips)
				System.err.println("Simplified get-interpolants");
			if (decls)
				System.err.println("Removed declarations");
//			System.in.read();
		} while (
				cmds || terms || bindings || neutrals || lists || ips || decls);
		boolean features = removeFeatures();
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
		public Scope(int f) {
			mFirst = f;
		}
		public void nest(Scope s) {
			if (mNested == null)
				mNested = new ArrayList<Scope>();
			mNested.add(s);
		}
	}
	
	private List<Scope> detectScopes() {
		ArrayDeque<Scope> ppStack = new ArrayDeque<Scope>();
		// All toplevel scopes.
		List<Scope> res = new ArrayList<Scope>();
		for (int i = 0; i < mCmds.size(); ++i) {
			Cmd cmd = mCmds.get(i);
			if (!cmd.isActive())
				continue;
			if (cmd instanceof ScopeCmd) {
				ScopeCmd sc = (ScopeCmd) cmd;
				if (sc.isScopeStart()) {
					System.err.println("Found scope start at " + i);
					Scope s = new Scope(i);
					for (int n = 0; n < sc.getNumScopes(); ++n)
						ppStack.push(s);
				} else {
					System.err.println("Found scope end at " + i);
					for (int n = 0; n < sc.getNumScopes(); ++n) {
						Scope last = ppStack.pop();
						Scope next = ppStack.peek();
						// We have found a scope end...
						last.mLast = i;
						last.mReduce = n + 1;
						if (next == null)
							// toplevel scope
							res.add(last);
						else if (last != next)
							next.nest(last);
					}
				}
			}
		}
		return res;
	}
	
	private boolean removeScopes() throws IOException, InterruptedException {
		System.err.println("Removing scopes...");
		boolean res = false;
		ArrayDeque<List<Scope>> todo = new ArrayDeque<List<Scope>>();
		todo.push(detectScopes());
		while (!todo.isEmpty()) {
			List<Scope> scopes = todo.pop();
			BinSearch<Scope> bs = new BinSearch<Scope>(
					scopes, new RemoveScopes(mCmds));
			res |= bs.run(this);
			for (Scope s : scopes)
				if (!s.mDeactivated && s.mNested != null)
					todo.push(s.mNested);
		}
		System.err.println("...done");
		return res;
	}
	
	private boolean removeCmds() throws IOException, InterruptedException {
		System.err.println("Removing commands...");
		List<Cmd> cmds = new ArrayList<Cmd>();
		for (int i = 0; i < mCmds.size(); ++i) {
			Cmd cmd = mCmds.get(i);
			if (!cmd.isActive())
				continue;
			if (cmd.canBeRemoved() && !cmd.hasDefinitions()) {
				cmds.add(cmd);
			}
		}
		boolean res = deactivateCmds(cmds);
		System.err.println("...done");
		return res;
	}
	
	private boolean deactivateCmds(List<Cmd> toDeactivate)
		throws IOException, InterruptedException {
		DeactivateCmds driver = new DeactivateCmds();
		BinSearch<Cmd> bs = new BinSearch<Cmd>(toDeactivate, driver);
		return bs.run(this);
	}
	
	private boolean removeDecls() throws IOException, InterruptedException {
		System.err.println("Removing unused declarations...");
		// Collect used definitions
		ScopedHashMap<String, Cmd> definitions =
				new ScopedHashMap<String, Cmd>();
		Set<Cmd> usedDefs = new HashSet<Cmd>();
		for (Cmd cmd : mCmds) {
			if (!cmd.isActive())
				continue;
			cmd.addUsedDefinitions(definitions, usedDefs);
			if (cmd.hasDefinitions())
				cmd.insertDefinitions(definitions);
			if (cmd instanceof ScopeCmd) {
				ScopeCmd scope = (ScopeCmd) cmd;
				if (scope.isScopeStart())
					for (int i = 0; i < scope.getNumScopes(); ++i)
						definitions.beginScope();
				else
					for (int i = 0; i < scope.getNumScopes(); ++i)
						definitions.endScope();
			}
		}
		// Free some space...
		definitions = null;
		// Collect unused definitions
		List<Cmd> unusedDefs = new ArrayList<Cmd>();
		for (Cmd cmd : mCmds) {
			if (!cmd.isActive())
				continue;
			if (cmd.hasDefinitions() && !usedDefs.contains(cmd))
				unusedDefs.add(cmd);
		}
		boolean res = deactivateCmds(unusedDefs);
		// Now, we have deactivated all unused definitions that can be
		// removed completely from the input.  But unfortunately some of these
		// definitions might be :named annotations and we still need the term!
		// Try to only remove the annotation.
		for (Iterator<Cmd> it = unusedDefs.iterator(); it.hasNext(); ) {
			Cmd next = it.next();
			if (!next.isActive() || !isNamedAssert(next))
				it.remove();
		}
		BinSearch<Cmd> bs = new BinSearch<Cmd>(
				unusedDefs, new BinSearch.Driver<Cmd>() {

			@Override
			public void prepare(List<Cmd> sublist) {
				for (Cmd cmd : sublist) {
					OneTermCmd tcmd = (OneTermCmd) cmd;
					Term stripped = new TermTransformer() {

						@Override
						public void postConvertAnnotation(AnnotatedTerm old,
								Annotation[] newAnnots, Term newBody) {
							ArrayList<Annotation> noNames =
									new ArrayList<Annotation>(newAnnots.length);
							for (Annotation a : newAnnots)
								if (!a.getKey().equals(":named"))
									noNames.add(a);
							setResult(noNames.isEmpty() ? newBody
								: old.getTheory().annotatedTerm(noNames.toArray(
										new Annotation[noNames.size()]),
										newBody));
						}
						
					}.transform(tcmd.getTerm());// NOCHECKSTYLE 
					tcmd.setTerm(stripped);
				}
			}

			@Override
			public void failure(List<Cmd> sublist) {
				for (Cmd cmd : sublist)
					((OneTermCmd) cmd).failure();
			}

			@Override
			public void success(List<Cmd> sublist) {
				for (Cmd cmd : sublist)
					((OneTermCmd) cmd).success();				
			}
			
		});// NOCHECKSTYLE
		res |= bs.run(this); 
		System.err.println("...done");
		return res;
	}
	
	private boolean isUnnamedAssert(AbstractOneTermCmd cmd) {
		return (cmd instanceof OneTermCmd) 
				&& ((OneTermCmd) cmd).getCmd().equals("assert")
				&& !cmd.hasDefinitions();
	}
	
	private boolean isNamedAssert(Cmd cmd) {
		if (cmd instanceof OneTermCmd) {
			OneTermCmd tcmd = (OneTermCmd) cmd;
			if (tcmd.getCmd().equals("assert")
					&& tcmd.getTerm() instanceof AnnotatedTerm)
				for (Annotation a : ((AnnotatedTerm) tcmd.getTerm()).
						getAnnotations())
					if (a.getKey().equals(":named"))
						return true;
		}
		return false;
	}
	
	private boolean removeUnusedCore(Mode mode)
		throws IOException, InterruptedException {
		boolean res = false;
		TermSimplifier simp = new TermSimplifier(mode);
		for (Cmd cmd : mCmds) {
			if (!cmd.isActive() || !(cmd instanceof AbstractOneTermCmd))
				continue;
			AbstractOneTermCmd tcmd = (AbstractOneTermCmd) cmd;
			Term s = simp.transform(tcmd.getTerm());
			if (s != tcmd.getTerm()) {
				tcmd.setTerm(s);
				if (test()) {
					res = true;
					tcmd.success();
				} else
					tcmd.failure();
			}
		}
		return res;
	}
	
	private boolean removeBindings() throws IOException, InterruptedException {
		return removeUnusedCore(Mode.BINDINGS);
	}
	
	private boolean removeNeutrals() throws IOException, InterruptedException {
		return removeUnusedCore(Mode.NEUTRALS);
	}
	
	private boolean simplifyTerms() throws IOException, InterruptedException {
		System.err.println("Simplifying terms...");
		boolean res = false;
		for (Cmd cmd : mCmds) {
			if (!cmd.isActive() || !(cmd instanceof AbstractOneTermCmd))
				continue;
			boolean localres = false;
			AbstractOneTermCmd tcmd = (AbstractOneTermCmd) cmd;
			SubstitutionManager substmgr =
					new SubstitutionManager(tcmd);
			// Try to simplify this one command...
			if (isUnnamedAssert(tcmd))
				// We should not substitute the top level
				substmgr.deepen();
			deepen: while (substmgr.deepen()) {// NOCHECKSTYLE
				List<Substitution> substs;
				do {
					substs = substmgr.getSubstitutions();
					if (substs.isEmpty())
						continue deepen;
					System.err.println("Term: " + tcmd.getTerm());
					System.err.println("Substs: " + substs);
					SimplifyTerms driver = new SimplifyTerms(
							tcmd, substmgr, substs);
					BinSearch<Substitution> bs =
							new BinSearch<Substitution>(substs, driver);
					localres |= bs.run(this);
				} while (substmgr.failed());
			}
			res |= localres;
		} // Cmd-loop
		System.err.println("...done");
		return res;
	}
	
	private Term unfoldAnd(Term p1, Term p2) {
		ArrayList<Term> conjuncts = new ArrayList<Term>();
		ApplicationTerm at = (ApplicationTerm) p1;
		if (at.getFunction() == at.getTheory().mAnd)
			conjuncts.addAll(Arrays.asList(at.getParameters()));
		else
			conjuncts.add(p1);
		at = (ApplicationTerm) p2;
		if (at.getFunction() == at.getTheory().mAnd)
			conjuncts.addAll(Arrays.asList(at.getParameters()));
		else
			conjuncts.add(p2);
		return p1.getTheory().term("and",
				conjuncts.toArray(new Term[conjuncts.size()]));
	}
	
	private int numChildren(int[] sos, int parent) {
		int numChildren = 0;
		int child = parent - 1;
		while (child >= sos[parent]) {
			++numChildren;
			child = sos[child] - 1;
		}
		return numChildren;
	}
	
	private void mergeWithChild(GetInterpolants gi, int parent, int child) {
		int[] sos = gi.getStartOfSubtree();
		int childidx = parent - 1;
		for (/* Nothing */ ; child > 0; --child)
			childidx = sos[childidx];
		Term[] partition = gi.getPartition();
		Term[] newPartition = new Term[partition.length - 1];
		int[] newSos = new int[sos.length - 1];
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
	}
	
	private boolean mergeTree(GetInterpolants gi)
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
				if (n == 2)
					// No further merge possible!
					return res;
				mergeWithChild(gi, i, child);
				if (test()) {
					res = true;
					gi.success();
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
	
	private boolean isAnd(Term t) {
		return ((ApplicationTerm) t).getFunction() == t.getTheory().mAnd;
	}
	
	private boolean simplifyInterpolantPartitions(GetInterpolants gi)
		throws IOException, InterruptedException {

		Term[] partition = gi.getPartition();
		if (partition.length == 2)
			return false;
		int i = 0;
		boolean res = false;
		while (i < partition.length) {
			// Try to remove partition i
			// 1. complete
			int newlength = partition.length - 1;
			if (newlength < 2)
				// We cannot remove anything anymore!!!
				return res;
			Term[] newPartition = new Term[newlength];
			int[] newSos = new int[newlength];
			int[] sos = gi.getStartOfSubtree();
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
					Term[] conjs =
							((ApplicationTerm) partition[i]).getParameters();
					ArrayList<Term> newcs =
							new ArrayList<Term>(conjs.length - 1);
					int c = 0;
					while (c < conjs.length) {
						for (int j = 0; j < conjs.length; ++j)
							if (j != c)
								newcs.add(conjs[j]);
						newPartition = partition.clone();
						newPartition[i] = buildAnd(newcs);
						gi.setNewPartition(newPartition);
						if (test()) {
							gi.success();
							conjs = ((ApplicationTerm) newPartition[i]).
									getParameters();
							partition = newPartition;
							res = true;
							// Don't increment c since we shifted elements
						} else {
							gi.failure();
							++c;
						}
					}
				}
				++i;
			}
		}
		return res;
	}
	
	private static ApplicationTerm buildAnd(List<Term> conjs) {
		if (conjs.isEmpty())
			return null;
		if (conjs.size() == 1)
			return (ApplicationTerm) conjs.get(0);
		return conjs.get(0).getTheory().term(
				"and", conjs.toArray(new Term[conjs.size()]));
	}
	
	private boolean simplifyGetInterpolants()
		throws IOException, InterruptedException {
		System.err.println("Simplifying get-interpolants...");
		boolean res = false;
		Map<Term, Term> actualNames = new HashMap<Term, Term>();
		for (Cmd cmd : mCmds) {
			if (!cmd.isActive())
				continue;
			if (cmd instanceof GetInterpolants) {
				GetInterpolants gi = (GetInterpolants) cmd;
				res |= simplifyInterpolantPartitions(gi);
				// This should be superseded by simplifyInterpolantPartitions
//				res |= removeTruePartitions(gi, actualNames);
				// This should be superseded by mergeTree
//				res |= mergeSequential(gi);
				res |= mergeTree(gi);
			} else if (isNamedAssert(cmd)) {
				AbstractOneTermCmd tcmd = (AbstractOneTermCmd) cmd;
				AnnotatedTerm t = (AnnotatedTerm) tcmd.getTerm();
				Term v = t.getSubterm();
				for (Annotation a : t.getAnnotations())
					if (a.getKey().equals(":named"))
						actualNames.put(
								t.getTheory().term(a.getValue().toString()), v);
			}
		}
		System.err.println("...done");
		return res;
	}
	
	private boolean simplifyTermListCmds()
		throws IOException, InterruptedException {
		System.err.println("Simplifying term list commands...");
		List<TermListCmd> cmds = new ArrayList<TermListCmd>();
		for (Cmd cmd : mCmds) {
			if (!cmd.isActive())
				continue;
			if (cmd instanceof TermListCmd) {
				TermListCmd tcmd = (TermListCmd) cmd;
				if (tcmd.getTerms().length > 1)
					cmds.add(tcmd);
			}
		}
		if (cmds.isEmpty()) {
			System.err.println("...done");
			return false;
		}
		// Try to reduce number of terms in the list
		// First try to reduce all cmds to their lower half terms.
		boolean goon = true;
		boolean res = false;
		while (goon) {
			goon = false;
			for (TermListCmd cmd : cmds) {
				Term[] terms = cmd.getTerms();
				Term[] newTerms = new Term[terms.length / 2];
				System.arraycopy(terms, 0, newTerms, 0, newTerms.length);
				cmd.setNewTerms(newTerms);
			}
			if (test()) {
				for (TermListCmd cmd : cmds)
					cmd.success();
				res = true;
				goon = true;
			} else {
				// We had a failure => Try to reduce to the other half
				for (TermListCmd cmd : cmds) {
					cmd.failure();
					Term[] terms = cmd.getTerms();
					int len = terms.length - terms.length / 2;
					Term[] newTerms = new Term[len];
					System.arraycopy(terms, terms.length / 2, newTerms, 0,
							newTerms.length);
					cmd.setNewTerms(newTerms);
				}
				if (test()) {
					for (TermListCmd cmd : cmds)
						cmd.failure();
					// Both reductions failed => give up
					System.err.println("...done");
					return res;
				} else {
					for (TermListCmd cmd : cmds)
						cmd.success();
					res = true;
					goon = true;
				}
			}
		}
		System.err.println("...done");
		return res;
	}
	
	private void shrinkCmdList() {
		System.err.println("Shrinking command list...");
		for (Iterator<Cmd> it = mCmds.iterator(); it.hasNext(); ) {
			if (!it.next().isActive())
				it.remove();
		}
		System.err.println("...done");
	}
	
	private boolean removeFeatures() throws IOException, InterruptedException {
		Map<String, Cmd> features = new HashMap<String, Cmd>();
		for (Cmd cmd : mCmds)
			if (cmd.isActive()) {
				String feature = cmd.provideFeature();
				if (feature != null) {
					System.err.println("Found feature " + feature);
					features.put(feature, cmd);
				}
			}
		for (Cmd cmd : mCmds)
			if (cmd.isActive())
				cmd.checkFeature(features);
		List<Cmd> featureProvider = new ArrayList<Cmd>(features.values());
		System.err.println("Trying to remove features " + featureProvider);
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
		System.err.println("Dumping...");
		dumpCmds();
		System.err.println("Testing...");
		Process p = Runtime.getRuntime().exec(mSolver);
		OutputReaper out = new OutputReaper(p.getInputStream());
		out.start();
		OutputReaper err = new OutputReaper(p.getErrorStream());
		err.start();
		int exitVal = p.waitFor();
		out.join();
		err.join();
		if (exitVal == mGoldenExit) {
			++mSuccTestCtr;
			System.err.println("Success");
			Files.copy(mTmpFile.toPath(), mResultFile.toPath(),
					StandardCopyOption.REPLACE_EXISTING);
			return true;
		}
		System.err.println("Failure");
		return false;
	}
	
	private void dumpCmds() throws FileNotFoundException {
		PrintWriter out = new PrintWriter(mTmpFile);
		for (Cmd cmd : mCmds) {
			if (cmd.isActive())
				cmd.dump(out);
		}
		out.flush();
		out.close();
	}
	
	public static void usage() {
		System.err.println(
				"Usage: Minimizer <infile> <outfile> <command> <args>");
		System.err.println("where");
		System.err.println("\tinfile\tis the original input file");
		System.err.println("\toutfile\tis the desired output file");
		System.err.println("\tcommand\tis the command to start the solver");
		System.err.println("\targs\tare optional arguments to \"command\"");
		System.exit(0);
	}
	
	public static void main(String[] args) {
		if (args.length < 3)// NOCHECKSTYLE
			usage();
		String infile = args[0];
		String outfile = args[1];
		StringBuilder command = new StringBuilder();
		for (int i = 2; i < args.length; ++i)
			command.append(args[i]).append(' ');
		File resultFile = new File(outfile);
		try {
			File tmpFile = File.createTempFile("minimize", ".smt2");
			tmpFile.deleteOnExit();
			File input = new File(infile);
			Files.copy(input.toPath(), resultFile.toPath());
			Files.copy(input.toPath(), tmpFile.toPath(),
					StandardCopyOption.REPLACE_EXISTING);
			command.append(tmpFile.getAbsolutePath());
			String solver = command.toString();
			// Free space
			command = null;
			System.err.println("Starting " + solver);
			Process p = Runtime.getRuntime().exec(solver);
			OutputReaper out = new OutputReaper(p.getInputStream());
			out.start();
			OutputReaper err = new OutputReaper(p.getErrorStream());
			err.start();
			int goldenExit = p.waitFor();
			out.join();
			err.join();
			// Free space
			p = null;
			System.err.println("Got golden exit code: " + goldenExit);
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
			System.err.println("Begin parsing");
			pe.parseScript(infile);
			// Free space
			pe = null;
			System.err.println("Parsing done");
			Minimizer mini = new Minimizer(
					ps.getCmds(), goldenExit, tmpFile, resultFile, solver);
			// Free space
			ps = null;
			if (!mini.deltaDebug())
				System.err.println("Failed to minimize");
		} catch (IOException e) {
			e.printStackTrace();
		} catch (InterruptedException e) {
			e.printStackTrace();
		}
	}
	
}
