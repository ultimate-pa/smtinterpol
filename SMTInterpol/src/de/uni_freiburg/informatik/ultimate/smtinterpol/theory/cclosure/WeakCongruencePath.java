/*
 * Copyright (C) 2014 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.smtinterpol.theory.cclosure;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Deque;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.smtinterpol.convert.EqualityProxy;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.Clause;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.Literal;
import de.uni_freiburg.informatik.ultimate.smtinterpol.proof.LeafNode;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.cclosure.ArrayAnnotation.RuleKind;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.cclosure.CCTermPairHash.Info;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.cclosure.WeakEQEntry.EntryPair;
import de.uni_freiburg.informatik.ultimate.smtinterpol.util.SymmetricPair;

public class WeakCongruencePath extends CongruencePath {
	
	private static class WeakSubPath {
		
		private final CCTerm mIdx;
		
		private final ArrayList<Object> mPath = new ArrayList<Object>();
		
		private final boolean mProduceProofs;
		
		public WeakSubPath(CCTerm idx, boolean produceProofs) {
			mIdx = idx;
			mProduceProofs = produceProofs;
		}
		
		public void storeInto(CCTerm[] weakIndices, CCTerm[][] weakpaths, int i) {
			assert mProduceProofs;
			ArrayList<CCTerm> path = new ArrayList<CCTerm>();
			CCTerm last = null;
			for (Object o : mPath) {
				if (o instanceof SubPath) {
					SubPath sub = (SubPath) o;
					if (last == sub.mTermsOnPath.get(0)) {
						for (int j = 1; j < sub.mTermsOnPath.size(); ++j)
							path.add(sub.mTermsOnPath.get(j));
					} else
						path.addAll(sub.mTermsOnPath);
					last = sub.mTermsOnPath.get(sub.mTermsOnPath.size() - 1);
				} else if (o instanceof CCTerm) {
					CCTerm co = (CCTerm) o;
					if (co != last) {
						path.add(co);
						last = co;
					}
				} else {
					throw new InternalError(
							"Encountered unexpected element on weak path");
				}
			}
			// allocate memory
			weakIndices[i] = mIdx;
			weakpaths[i] = path.toArray(new CCTerm[path.size()]);
		}
		
		void addSubPath(SubPath p) {
			if (mProduceProofs)
				mPath.add(p);
		}
		
		void addEmptySubPath(CCTerm l) {
			if (mProduceProofs)
				mPath.add(l);
		}
		
		void addModuloStep(WeakEQiEntry e, boolean inOrder) { // NOPMD
			if (mProduceProofs) {
				assert e.isModuloStep();
				if (inOrder) {
					mPath.add(e.getLeftSelect());
					mPath.add(e.getRightSelect());
				} else {
					mPath.add(e.getRightSelect());
					mPath.add(e.getLeftSelect());
				}
			}
		}
		
		public String toString() {
			return mPath.toString();
		}
	}

	final ArrayTheory mArrayTheory;
	
	final List<WeakSubPath> mWeakPaths;
	
	public WeakCongruencePath(ArrayTheory arrayTheory) {
		super(arrayTheory.getCClosure());
		mArrayTheory = arrayTheory;
		mWeakPaths = new ArrayList<WeakSubPath>();
	}

	private CCEquality createEquality(CCTerm t1, CCTerm t2) {
		EqualityProxy ep = t1.getFlatTerm().createEquality(t2.getFlatTerm());
		if (ep == EqualityProxy.getFalseProxy())
				return null;
		Literal res = ep.getLiteral();
		if (res instanceof CCEquality)
			return (CCEquality) res;
		return ep.createCCEquality(t1.getFlatTerm(), t2.getFlatTerm());
	}
	
	public Clause computeSelectOverWeakEQ(CCAppTerm select1, CCAppTerm select2,
			Map<SymmetricPair<CCTerm>, WeakEQEntry> weakeq,
			boolean produceProofs, Deque<Literal> suggestions) {
		CCEquality eq = createEquality(select1, select2);
		CCTerm i1 = select1.getArg();
		CCTerm i2 = select2.getArg();
		CCTerm a = ((CCAppTerm) select1.getFunc()).getArg();
		CCTerm b = ((CCAppTerm) select2.getFunc()).getArg();
		mMainPath = computePath(i1, i2);
		WeakSubPath weakpath =
				computeWeakPath(a, b, i1, weakeq, false, produceProofs);
		mWeakPaths.add(weakpath);
		return generateClause(eq, produceProofs, suggestions,
				RuleKind.READ_OVER_WEAKEQ);
	}
	
	public Clause computeWeakeqExt(CCTerm a, CCTerm b,
			WeakEQEntry weakpaths,
			HashMap<SymmetricPair<CCTerm>, WeakEQEntry> weakeq,
			boolean produceProofs, ArrayDeque<Literal> suggestions) {
		CCEquality eq = createEquality(a, b);
		for (CCTerm storeidx : weakpaths.getEntries().keySet()) {
			WeakSubPath weakpath =
					computeWeakPath(a, b, storeidx, weakeq, true, produceProofs);
			mWeakPaths.add(weakpath);
		}
		return generateClause(eq, produceProofs, suggestions,
				RuleKind.WEAKEQ_EXT);
	}

	/**
	 * Compute a weak path and the corresponding weak path condition.  The path
	 * condition is added to the set of literals constituting the conflict.
	 * @param a              Start of the path.
	 * @param b              End of the path.
	 * @param idx            Index for this path.
	 * @param weakeq         Weak equivalence relation.
	 * @param useModuloEdges Use edges induced by equalities on values stored at
	 *                       <code>idx</code>.
	 * @param produceProofs  Proof production enabled?
	 * @return Path information for this weak path.
	 */
	private WeakSubPath computeWeakPath(CCTerm a, CCTerm b, CCTerm idx,
			Map<SymmetricPair<CCTerm>, WeakEQEntry> weakeq,
			boolean useModuloEdges, boolean produceProofs) {
		assert a.getRepresentative() != b.getRepresentative()
				: "Compute a strong path not a weak path!";
		CCTerm left = a.getRepresentative();
		CCTerm right = b.getRepresentative();
		WeakSubPath sub = new WeakSubPath(idx, produceProofs);
		// first compute paths to their representatives
		if (a == left)
			sub.addEmptySubPath(a);
		else
			sub.addSubPath(computePath(a, left));
		WeakEQEntry step = weakeq.get(new SymmetricPair<CCTerm>(left, right));
		// TODO For now, I just prefer modulo edges.  We should revise this.
		boolean done = false;
		if (useModuloEdges) {
			WeakEQiEntry modEdge = step.getModuloPath(idx);
			if (modEdge != null) {
				if (modEdge.isModuloStep()) {
					addModuloStep(sub, left, right, idx, modEdge, weakeq);
					done = true;
				} else {
					CCTerm leftarr, rightarr;
					if (left.mArrayNum < right.mArrayNum) {
						leftarr = modEdge.getLeftModuloArray();
						rightarr = modEdge.getRightModuloArray();
					} else {
						leftarr = modEdge.getRightModuloArray();
						rightarr = modEdge.getLeftModuloArray();
					}
					addPath(sub, left, leftarr, idx, weakeq, null);
					WeakEQEntry weakstep = weakeq.get(
							new SymmetricPair<CCTerm>(leftarr, rightarr));
					WeakEQiEntry weakistep = weakstep.getModuloPath(idx);
					addModuloStep(sub, leftarr, rightarr, idx, weakistep, weakeq);
					addPath(sub, rightarr, right, idx, weakeq, null);
					done = true;
				}
			}
		}
		if (!done)
			// We either don't use or don't have mod edges here
			addPath(sub, left, right, idx, weakeq, step);
		if (b == right)
			sub.addEmptySubPath(b);
		else
			sub.addSubPath(computePath(b, right));
		return sub;
	}
	
	private void addModuloStep(WeakSubPath sub, CCTerm left, CCTerm right,
			CCTerm idx, WeakEQiEntry modEdge,
			Map<SymmetricPair<CCTerm>, WeakEQEntry> weakeq) {
		CCTerm leftarr, rightarr, leftsel, rightsel,
		startidx, endidx;
		boolean inOrder = left.mArrayNum < right.mArrayNum;
		if (inOrder) {
			leftarr = modEdge.getLeftArray();
			rightarr = modEdge.getRightArray();
			leftsel = modEdge.getLeftSelect();
			rightsel = modEdge.getRightSelect();
			startidx = modEdge.getLeftIndex();
			endidx = modEdge.getRightIndex();
		} else {
			leftarr = modEdge.getRightArray();
			rightarr = modEdge.getLeftArray();
			leftsel = modEdge.getRightSelect();
			rightsel = modEdge.getLeftSelect();
			startidx = modEdge.getLeftIndex();
			endidx = modEdge.getRightIndex();
		}
		assert left.getRepresentative() == leftarr.getRepresentative();
		assert right.getRepresentative() == rightarr.getRepresentative();
		if (left != leftarr)
			sub.addSubPath(computePath(left, leftarr));
		sub.addModuloStep(modEdge, inOrder);
		// Compute judgement for modEdge
		computePath(leftsel, rightsel);
		// Compute judgement for "idx equals select indices"
		computePath(idx, startidx);
		computePath(idx, endidx);
		if (right != rightarr)
			sub.addSubPath(computePath(rightarr, right));
	}
	
	/**
	 * Add a path entry.  This path entry might either be a weak equivalence
	 * path or a strong equivalence path, but not a modulo step.
	 * @param path   The path to extend.
	 * @param left   The start of the new path.
	 * @param right  The end of the new path.
	 * @param idx    The index for this weak path.
	 * @param weakeq The weak equivalence relation.
	 * @param first  First step of a weakeq path if available.  Might be
	 *               <code>null</code> in which case the method searches for the
	 *               first step.
	 */
	private void addPath(WeakSubPath path, CCTerm left, CCTerm right,
			CCTerm idx, Map<SymmetricPair<CCTerm>, WeakEQEntry> weakeq,
			WeakEQEntry first) {
		if (left.getRepresentative() == right.getRepresentative())
			return;
		WeakEQEntry step = first == null
				? weakeq.get(new SymmetricPair<CCTerm>(left, right)) : first;
		while (left != right) {
			EntryPair nextPair = step.getConnection(idx);
			boolean inOrder = left.mArrayNum < right.mArrayNum;
			CCTerm next = nextPair.getEntry(inOrder);
			assert mArrayTheory.isStore(next);
			CCTerm edgeleft, edgeright;
			if (left.getRepresentative() == next.getRepresentative()) {
				edgeleft = next;
				edgeright = ArrayTheory.getArrayFromStore(next);
			} else {
				edgeleft = ArrayTheory.getArrayFromStore(next);
				assert left.getRepresentative() == edgeleft.getRepresentative();
				edgeright = next;
			}
			/* Now, we have a path of the form
			 * left -- edgeleft -j- edgeright
			 * and should continue work at edgeright.getRepresentative()
			 * Not that reverse specifies whether we are moving towards
			 * right (if reverse if false) or left (if reverse is true).
			 */
			// left -- edgeleft
			if (left != edgeleft)
				path.addSubPath(computePath(left, edgeleft));
			// -j-
			computeIndexDiseq(idx, ArrayTheory.getIndexFromStore(next));
			// Check for final step
			CCTerm targetrep = right.getRepresentative();
			if (edgeright.getRepresentative() == targetrep) {
				// finish the path
				if (edgeright != right)
					path.addSubPath(computePath(edgeright, right));
				break;
			} else {
				// Continue at edgeright.getRepresentative();
				if (edgeright == edgeright.getRepresentative())
					path.addEmptySubPath(edgeright);
				else
					path.addSubPath(computePath(
							edgeright, edgeright.getRepresentative()));
				left = edgeright.getRepresentative();
			}
			step = weakeq.get(new SymmetricPair<CCTerm>(left, right));
		} // end while
	}

	/**
	 * Compute a justification for the disequality of two indices.
	 * @param idx          The index for a weak equality path.
	 * @param idxFromStore The index of an edge in the weakeq graph.
	 */
	private void computeIndexDiseq(CCTerm idx, CCTerm idxFromStore) {
		if (idx.getSharedTerm() != null && idxFromStore != null) {
			// check for shared term diseqality
			EqualityProxy ep = mArrayTheory.getClausifier().createEqualityProxy(
					idx.getSharedTerm(), idxFromStore.getSharedTerm());
			if (ep == EqualityProxy.getFalseProxy())
				// Always different
				return;
		}
		CCTerm idxrep = idx.getRepresentative();
		CCTerm idxStorerep = idxFromStore.getRepresentative();
		assert idxrep != idxStorerep;
		Info info = mClosure.mPairHash.getInfo(idxrep, idxStorerep);
		CCEquality diseq = null;
		boolean idxIsLhs = true;
		if (info != null) {
			CCEquality first = null;
			for (CCEquality.Entry entry : info.mEqlits) {
				CCEquality cur = entry.getCCEquality();
				// Pick first diseq
				if (first == null)
					first = cur;
				// Check for perfect matches
				if (cur.getLhs() == idx && cur.getRhs() == idxFromStore) {
					diseq = cur;
				} else if (cur.getLhs() == idxFromStore && cur.getRhs() == idx) {
					diseq = cur;
					idxIsLhs = false;
				}
			}
			if (diseq == null) {
				diseq = first;
				idxIsLhs = diseq.getLhs().getRepresentative() == idxrep;
			}
		}
		if (diseq == null) {
			// We don't have an equality literal for these equivalence classes
			// Create one
			CCEquality eqlit = createEquality(idx, idxFromStore);
			if (eqlit != null) {
				// mAllLiterals is conflict
				mAllLiterals.add(eqlit.negate());
			}
		} else {
			// compute paths to the literal
			computePath(idx, idxIsLhs ? diseq.getLhs() : diseq.getRhs());
			computePath(idxIsLhs ? diseq.getRhs() : diseq.getLhs(), idxFromStore);
			// mAllLiterals is conflict
			mAllLiterals.add(diseq.negate());
		}
	}

	private Clause generateClause(CCEquality diseq, boolean produceProofs,
			Deque<Literal> suggestions, RuleKind rule) {
		Literal[] lemma = new Literal[mAllLiterals.size() + 1];
		int i = 0;
		lemma[i++] = diseq;
		for (Literal l: mAllLiterals) {
			lemma[i++] = l.negate();
			// I want to suggest all paths.  Thus I put all l in suggestions.
//			suggestions.offer(l);
		}
		Clause c = new Clause(lemma);
		if (produceProofs)
			c.setProof(new LeafNode(
					LeafNode.THEORY_ARRAY, createAnnotation(diseq, rule)));
		return c;
	}
	
	private ArrayAnnotation createAnnotation(CCEquality diseq, RuleKind rule) {
		CCTerm[][] paths = new CCTerm[mVisited.size()][];
		CCEquality[][] lits  = new CCEquality[mVisited.size()][];
		int i = 0;
		if (mMainPath != null)
			mMainPath.storeInto(paths, lits, i++);
		for (SubPath subPath : mVisited.values()) {
			if (subPath != mMainPath)
				subPath.storeInto(paths, lits, i++);
		}
		CCTerm[] weakIndices = new CCTerm[mWeakPaths.size()];
		CCTerm[][] weakPaths = new CCTerm[mWeakPaths.size()][];
		int j = 0;
		for (WeakSubPath weakpath : mWeakPaths)
			weakpath.storeInto(weakIndices, weakPaths, j++);
		return new ArrayAnnotation(diseq, paths, lits, weakIndices, weakPaths, rule);
	}

}
