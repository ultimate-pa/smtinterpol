/*
 * Copyright (C) 2020-2021 Max Barth (Max.Barth95@gmx.de)
 * Copyright (C) 2020-2021 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.smtinterpol.theory.bitvector;

import java.util.ArrayDeque;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedHashSet;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.ConstantTerm;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.logic.Theory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.Config;
import de.uni_freiburg.informatik.ultimate.smtinterpol.LogProxy;
import de.uni_freiburg.informatik.ultimate.smtinterpol.convert.Clausifier;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.Clause;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.DPLLAtom;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.DPLLEngine;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.ITheory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.Literal;
import de.uni_freiburg.informatik.ultimate.smtinterpol.proof.LeafNode;
import de.uni_freiburg.informatik.ultimate.smtinterpol.proof.ResolutionNode;
import de.uni_freiburg.informatik.ultimate.smtinterpol.proof.ResolutionNode.Antecedent;
import de.uni_freiburg.informatik.ultimate.smtinterpol.proof.SourceAnnotation;
import de.uni_freiburg.informatik.ultimate.smtinterpol.util.IdentityHashSet;
import de.uni_freiburg.informatik.ultimate.util.datastructures.ScopedArrayList;


public class BitVectorTheory implements ITheory {
	private final Clausifier mClausifier;
	private final ScopedArrayList<Literal> mBVLiterals;
	private final LinkedHashSet<Term> mAllTerms; // Set to ensure no Term is Bitblasted twice
	final BitBlaster mBitblaster;
	final BvultGraph mBvultGraph;
	DPLLEngine mEngine; // Dpll engine for bitblasting
	private long mBitBlastingTime, mAddDPLLBitBlastTime, mBvultGraphTime;
	private int mClauseCount, mCircleCount, mTrivialConflicts;
	private boolean mBitBlast = true; // ensures Bitblasting happens only once, not compatible with incremental Tracks
	private final boolean mEnableBvultGraph = false;

	public BitVectorTheory(final Clausifier clausifier) {
		mClausifier = clausifier;
		mBVLiterals = new ScopedArrayList<>();
		mAllTerms = new LinkedHashSet<>();
		mBitblaster = new BitBlaster(mClausifier, getTheory());
		mBvultGraph = new BvultGraph();
		mEngine = new DPLLEngine(mClausifier.getLogger(), () -> false);
		mEngine.setProofGeneration(true);
	}

	@Override
	public Clause startCheck() {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public void endCheck() {
		// TODO Auto-generated method stub

	}

	/*
	 * non recursiv
	 */
	private final ArrayDeque<Term> mCollected = new ArrayDeque<>();
	private void collectAllTerms(Term term) {
		if (mAllTerms.contains(term)) {
			return;
		}
		mCollected.push(term);
		while (!mCollected.isEmpty()) {
			term = mCollected.pop();
			if (mAllTerms.contains(term)) {
				continue;
			}
			if (term instanceof TermVariable) {
				mAllTerms.add(term);
			} else if (term instanceof ApplicationTerm) {
				final ApplicationTerm appterm = (ApplicationTerm) term;
				if ((!appterm.getFunction().getName().equals("="))
						&& (!appterm.getFunction().getName().equals("bvult"))) {
					mAllTerms.add(term);
				}
				for (final Term subterm : appterm.getParameters()) {
					mCollected.push(subterm);
				}
			} else if (term instanceof ConstantTerm) {
				mAllTerms.add(term);

			}

		}
	}

	@Override
	public Clause setLiteral(final Literal literal) {
		final DPLLAtom atom = literal.getAtom();
		if (atom.getSMTFormula(getTheory()) instanceof ApplicationTerm) {
			final ApplicationTerm apAtom = (ApplicationTerm) atom.getSMTFormula(getTheory());

			if (apAtom.getFunction().getName().equals("=")) {
				if (apAtom.getParameters().length == 0) {
					// literal is boolean predicat
					return null;
				}
				// Set BV Literals
				final Term bvEqLHS = apAtom.getParameters()[0];
				final Term bvEqRHS = apAtom.getParameters()[1];
				boolean bvLit = true;
				if (bvEqLHS.getSort().isBitVecSort()) {
					bvLit = true;
					assert bvEqRHS.getSort().isBitVecSort();
					mClausifier.getLogger().debug("Set BitVec Literal: " + literal.getSMTFormula(getTheory()));
					mBVLiterals.add(literal);
				}
				boolean bvultLit = false;
				final Term bvultTerm = getBvult(literal);
				if (bvultTerm != null && !bvultTerm.equals(getTheory().mFalse)) {
					bvultLit = true;
					bvLit = true;
				}
				if(bvultLit) {
					if (mEnableBvultGraph) {
						final Term from = ((ApplicationTerm) bvultTerm).getParameters()[0];
						final Term to = ((ApplicationTerm) bvultTerm).getParameters()[1];
						mBvultGraph.addVertex(from);
						mBvultGraph.addVertex(to);
						if (literal.getSign() == 1) {
							mBvultGraph.addEdge(mBvultGraph.getVertex(from), literal, mBvultGraph.getVertex(to));
						}
					}
					mClausifier.getLogger().debug("Set BitVec Literal: " + literal.getSMTFormula(getTheory()));
					mBVLiterals.add(literal);
				}

				// Look for trivial Conflicts:
				if (bvEqLHS.equals(bvEqRHS)) {
					if (((ApplicationTerm) literal.getSMTFormula(getTheory())).getFunction().getName()
							.equals("not")) {
						final Literal[] conflictSet = new Literal[1];
						conflictSet[0] = literal.negate();
						final Clause conflict = new Clause(conflictSet);
						mTrivialConflicts += 1;
						return conflict;
					}
					return null;
				}
				if (bvLit) {
					final Clause trivialConflict = checkTrivialConflict(literal, bvultLit, bvultTerm);
					if (trivialConflict != null) {
						mTrivialConflicts += 1;
						return trivialConflict;
					}
				}
			}
		}
		return null;
	}

	/*
	 * looks for trivial conflicts of form (a = b and a < b or b < a )
	 * and (a < b and b < a).
	 */
	private Clause checkTrivialConflict(final Literal literal, final boolean bvultLit, final Term bvultTerm) {
		ApplicationTerm newLit;
		if (bvultLit) {
			newLit = (ApplicationTerm) bvultTerm;
		} else { // = Literal
			newLit = (ApplicationTerm) literal.getSMTFormula(getTheory());
		}
		if (newLit.getFunction().getName().equals("not")) {
			return null;
		}
		for (final Literal lit : mBVLiterals) {
			if ((lit.getSign() == 1) && (literal.getSign() == 1)) {
				ApplicationTerm oldLit = (ApplicationTerm) lit.getSMTFormula(getTheory());
				boolean oldLitBvult = false;
				final ApplicationTerm bvultOld = (ApplicationTerm) getBvult(lit);
				if (!oldLit.getFunction().getName().equals("not")) {
					if (bvultOld == null) {
						oldLitBvult = false;
					} else if (!bvultOld.equals(getTheory().mFalse)) {
						oldLitBvult = true;
						oldLit = bvultOld;
					}
					if ((newLit.getParameters()[0].equals(oldLit.getParameters()[0])) &&
							(newLit.getParameters()[1].equals(oldLit.getParameters()[1]))) {
						if ((!bvultLit && oldLitBvult) || (bvultLit && !oldLitBvult)) {
							// Conflict
							final Literal[] conflictSet = new Literal[2];
							conflictSet[0] = literal.negate();
							conflictSet[1] = lit.negate();
							final Clause conflict = new Clause(conflictSet);
							return conflict;
						}
					} else if ((newLit.getParameters()[0].equals(oldLit.getParameters()[1])) &&
							(newLit.getParameters()[1].equals(oldLit.getParameters()[0]))) {
						if (bvultLit || oldLitBvult) {
							// Conflict
							final Literal[] conflictSet = new Literal[2];
							conflictSet[0] = literal.negate();
							conflictSet[1] = lit.negate();
							final Clause conflict = new Clause(conflictSet);
							return conflict;
						}
					}
				}
			}
		}
		return null;
	}

	@Override
	public void backtrackLiteral(final Literal literal) {
		final Term bvult = getBvult(literal);
		if (bvult != null && literal.getSign() == 1 && !bvult.equals(getTheory().mFalse) && mEnableBvultGraph) {
			final Vertex from = mBvultGraph.getVertex(((ApplicationTerm) bvult).getParameters()[0]);
			final Vertex to = mBvultGraph.getVertex(((ApplicationTerm) bvult).getParameters()[1]);
			from.removeNeighbor(to, literal);
		}

		mBVLiterals.remove(literal);
	}

	@Override
	public Clause checkpoint() {
		long time;
		if (Config.PROFILE_TIME) {
			time = System.nanoTime();
		}
		if (mEnableBvultGraph) {
			for (final Literal lit : mBVLiterals) {
				// check only the newly set literals for circles
				if (lit.getAtom().getDecideLevel() == mClausifier.getEngine().getDecideLevel()) {
					if (mClausifier.getEngine().isTerminationRequested()) {
						return null;
					}
					final Term bvult = getBvult(lit);
					if (bvult != null && lit.getSign() == 1 && !bvult.equals(getTheory().mFalse)) {
						final Vertex ver = mBvultGraph.getVertex(((ApplicationTerm) bvult).getParameters()[0]);
						if (!ver.isVisited()) {
							final HashSet<Literal> conflict = mBvultGraph.getCycle(ver);
							if (conflict.size() >= 2) {
								final Literal[] cores = new Literal[conflict.size()];
								int i = 0;
								for (final Literal c : conflict) {
									cores[i] = c.negate();
									mClausifier.getLogger().debug("Bvult Circle: " + c.getSMTFormula(getTheory()));
									i++;
								}
								mBvultGraph.resetCycleVisited();
								if (Config.PROFILE_TIME) {
									addBvultGraphTime(System.nanoTime() - time);
								}
								mCircleCount += 1;
								return new Clause(cores, mClausifier.getStackLevel());
							}

						}

					}

				}
			}
			mBvultGraph.resetCycleVisited();
		}
		if (Config.PROFILE_TIME) {
			addBvultGraphTime(System.nanoTime() - time);
		}
		return null;

	}

	/*
	 * Bvult Literals are CCEqualities of the form (bvult == true).
	 * CClosure creates additional CCequalities for each such bvult term of form !(bvult == false)
	 * We will return false then.
	 */
	private Term getBvult(final Literal lit) {
		final DPLLAtom atom = lit.getAtom();
		if (atom.getSMTFormula(getTheory()) instanceof ApplicationTerm) {
			final ApplicationTerm apAtom = (ApplicationTerm) atom.getSMTFormula(getTheory());
			if (apAtom.getFunction().getName().equals("=")) {
				if(apAtom.getParameters()[0] instanceof ApplicationTerm) {
					if (((ApplicationTerm) apAtom.getParameters()[0]).getFunction().getName().equals("bvult")) {
						if (apAtom.getParameters()[1].equals(getTheory().mFalse)) {
							return getTheory().mFalse;
						}
						return  apAtom.getParameters()[0];
					}
				} else if (apAtom.getParameters()[1] instanceof ApplicationTerm) {
					if (((ApplicationTerm) apAtom.getParameters()[1]).getFunction().getName().equals("bvult")) {
						if (apAtom.getParameters()[0].equals(getTheory().mFalse)) {
							return getTheory().mFalse;
						}
						return apAtom.getParameters()[1];
					}
				}
			}
		}
		return null;
	}



	@Override
	public Clause computeConflictClause() {
		if (mBVLiterals.isEmpty()) {
			// problem was solved by constant simplifications or similiar
			return null;
		}

		long time;

		// bitblasting
		if (mBitBlast) {
			mBitBlast = false;
			// collect all terms from all set literals
			for (final Literal lit : mBVLiterals) {
				final Term atom = lit.getAtom().getSMTFormula(getTheory());
				final Term bvult = getBvult(lit);
				if (bvult != null) {
					if (!bvult.equals(getTheory().mFalse)) {
						collectAllTerms(bvult);
					}
					// else, lit can be ignored if form is (bvult == false)
				} else {
					collectAllTerms(atom);
				}
			}
			mClausifier.getLogger().info("Starting Bitblasting");
			if (Config.PROFILE_TIME) {
				time = System.nanoTime();
			}
			mBitblaster.bitBlasting(mBVLiterals, mAllTerms, mEngine.getAssertionStackLevel());
			if (Config.PROFILE_TIME) {
				addBitBlastingTime(System.nanoTime() - time);
			}
			mClausifier.getLogger().info("Finished Bitblasting in: " + (System.nanoTime() - time));
			for (final DPLLAtom atom : mBitblaster.getBoolAtoms()) {
				mEngine.addAtom(atom);
			}
			mClauseCount += mBitblaster.getClauses().size();
			for (final Clause cl : mBitblaster.getClauses()) {
				mEngine.addClause(cl);
			}
		}
		// mAllTerms = new LinkedHashSet<>(); //reset allTerms?


		if (mClausifier.getEngine().isTerminationRequested()) {
			return null;
		}

		// Propositional Skeleton for BitBlasting:
		mEngine.push();
		for (int i = 0; i < mBVLiterals.size(); i++) {
			final Literal[] propSkel = new Literal[1];
			final Literal bitblastingAtom = mBitblaster.mInputAtomMap.get(mBVLiterals.get(i).getAtom());
			if (mBVLiterals.get(i).getSign() == 1) {
				propSkel[0] = bitblastingAtom;
			} else {
				propSkel[0] = bitblastingAtom.negate();
			}
			mClauseCount += 1;
			final Clause cl = new Clause(propSkel, mEngine.getAssertionStackLevel());
			cl.setProof(new LeafNode(-1, SourceAnnotation.EMPTY_SOURCE_ANNOT));
			mEngine.learnClause(cl); // learn instead of add, we want to pop() the propSkeleton after solving
		}

		// DPLL for BitBlasting
		mClausifier.getLogger().info("Bitblasting DPLL:");
		if (Config.PROFILE_TIME) {
			time = System.nanoTime();
		}
		final boolean sat = mEngine.solve();
		if (Config.PROFILE_TIME) {
			addDPLLBitBlastTime(System.nanoTime() - time);
		}
		mClausifier.getLogger().info("Bitblasting DPLL finished");

		// DPLL result
		if (sat) {
			// TODO Model generation
			final Term[] model = mEngine.getSatisfiedLiterals(getTheory());
			for (final Term t : model) {
				if (t instanceof ApplicationTerm) {
					if (((ApplicationTerm) t).getFunction().getName().equals("not")) {
						final Term atom = ((ApplicationTerm) t).getParameters()[0];
						if (mBitblaster.getLiteralMap().containsKey(atom)) {
							mClausifier.getLogger()
							.debug("Model InputLiteral: "
									+ mBitblaster.getLiteralMap().get(atom).getSMTFormula(getTheory()));
						}
					}
					break;
				}
				if (mBitblaster.getLiteralMap().containsKey(t)) {
					mClausifier.getLogger()
					.debug("Model InputLiteral: "
							+ mBitblaster.getLiteralMap().get(t).getSMTFormula(getTheory()));
				}
			}
		} else {
			final Clause unsat = mEngine.getProof();
			final LinkedHashSet<Literal> unsatcore = getUnsatCore(unsat, mBitblaster.getLiteralMap());
			final Literal[] cores = new Literal[unsatcore.size()];
			int i = 0;
			for (final Literal c : unsatcore) {
				cores[i] = c;
				mClausifier.getLogger().debug("Unsat Core: " + c.getSMTFormula(getTheory()));
				i ++;
			}
			mEngine.pop(1); // remove prop skeleton from dppl engine
			return new Clause(cores, mClausifier.getStackLevel());
		}
		mEngine.pop(1); // remove prop skeleton from dppl engine
		return null;

	}

	/*
	 * Searches some sort of Unsat Core in the Bitblasting result.
	 * Returns the Conflict Clause, containing this core.
	 */
	private LinkedHashSet<Literal> getUnsatCore(final Clause unsat, final HashMap<Term, Literal> literals) {
		final LinkedHashSet<Literal> res = new LinkedHashSet<>();
		final ArrayDeque<Clause> todo = new ArrayDeque<>();
		todo.push(unsat);
		final IdentityHashSet<Clause> visited = new IdentityHashSet<>();
		while (!todo.isEmpty()) {
			final Clause c = todo.pop();
			if (visited.add(c)) {
				if (c.getProof().isLeaf()) {
					final Term lit = c.getLiteral(0).getAtom().getSMTFormula(getTheory());
					if (literals.containsKey(lit)) {
						final int idx = mBVLiterals.indexOf(literals.get(lit));
						if (idx != -1) {
							res.add(mBVLiterals.get(idx).negate());
						} else {
							res.add(mBVLiterals.get(mBVLiterals.indexOf(literals.get(lit).negate())).negate());
						}
					}

				} else {
					final ResolutionNode n = (ResolutionNode) c.getProof();
					todo.push(n.getPrimary());
					final Antecedent[] ants = n.getAntecedents();
					for (final Antecedent a : ants) {
						todo.push(a.mAntecedent);
					}
				}
			}
		}
		return res;
	}

	@Override
	public Literal getPropagatedLiteral() {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Clause getUnitClause(final Literal literal) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Literal getSuggestion() {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public int checkCompleteness() {
		// TODO Auto-generated method stub
		return 0;
	}

	@Override
	public void printStatistics(final LogProxy logger) {
		logger.info(
				"BVTimes: BB " + mBitBlastingTime + " BB_DPLL " + mAddDPLLBitBlastTime + " Graph " + mBvultGraphTime);
		logger.info("BitBlastingClauses: " + mClauseCount + " BvultGraphCircles: " + mCircleCount
				+ " TrivialConflicts: " + mTrivialConflicts);
	}

	@Override
	public void dumpModel(final LogProxy logger) {
		// TODO Auto-generated method stub

	}

	@Override
	public void increasedDecideLevel(final int currentDecideLevel) {
		// TODO Auto-generated method stub

	}

	@Override
	public void decreasedDecideLevel(final int currentDecideLevel) {
		// TODO Auto-generated method stub

	}

	@Override
	public Clause backtrackComplete() {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public void backtrackAll() {
		// TODO Auto-generated method stub
	}

	@Override
	public void restart(final int iteration) {
		// TODO Auto-generated method stub

	}

	@Override
	public void removeAtom(final DPLLAtom atom) {
		// TODO Auto-generated method stub

	}

	@Override
	public void push() {
		// TODO Auto-generated method stub

	}

	@Override
	public void pop() {
		// TODO Auto-generated method stub

	}

	void addDPLLBitBlastTime(final long time) {
		mAddDPLLBitBlastTime += time;
	}
	void addBitBlastingTime(final long time) {
		mBitBlastingTime += time;
	}

	void addBvultGraphTime(final long time) {
		mBvultGraphTime += time;
	}
	@Override
	public Object[] getStatistics() {
		return new Object[] { ":BV",
				new Object[][] {
			{ "Times", new Object[][] { { "BitBlasting", mBitBlastingTime },
				{ "Dpll BitBlasting", mAddDPLLBitBlastTime },
				{ "Bvult Graph", mBvultGraphTime } } },

			{ "Count", new Object[][] { { "BBClauses", mClauseCount },
				{ "GraphCircles", mCircleCount },
				{ "TrivialConflicts", mTrivialConflicts }

			} } } };
	}


	public DPLLEngine getEngine() {
		return mClausifier.getEngine();
	}

	public Theory getTheory() {
		return mClausifier.getTheory();
	}
}