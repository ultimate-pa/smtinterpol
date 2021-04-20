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
import de.uni_freiburg.informatik.ultimate.smtinterpol.proof.ResolutionNode;
import de.uni_freiburg.informatik.ultimate.smtinterpol.proof.ResolutionNode.Antecedent;
import de.uni_freiburg.informatik.ultimate.smtinterpol.util.IdentityHashSet;
import de.uni_freiburg.informatik.ultimate.util.datastructures.ScopedArrayList;

/**
 *
 * @author Max Barth (max.barth95@gmx.de)
 *
 */
public class BitVectorTheory implements ITheory {
	private final Clausifier mClausifier;
	private final ScopedArrayList<Literal> mBVLiterals;
	private final LinkedHashSet<Term> mAllTerms; // Set to ensure no Term is Bitblasted twice
	final BitBlaster mBitblaster;
	final BvultGraph mBvultGraph;
	private long mBitBlastingTime, mAddDPLLBitBlastTime, mBvultGraphTime;
	private int mClauseCount;

	public BitVectorTheory(final Clausifier clausifier) {
		mClausifier = clausifier;
		mBVLiterals = new ScopedArrayList<>();
		mAllTerms = new LinkedHashSet<>();
		mBitblaster = new BitBlaster(getTheory());
		mBvultGraph = new BvultGraph();

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
	 * recursiv
	 */
	private void getAllTerms(final Term term) {
		if (term instanceof TermVariable) {
			mAllTerms.add(term);
		} else if (term instanceof ApplicationTerm) {
			final ApplicationTerm appterm = (ApplicationTerm) term;
			if ((!appterm.getFunction().getName().equals("=")) && (!appterm.getFunction().getName().equals("bvult"))) {
				mAllTerms.add(term);
			}
			for (final Term subterm : appterm.getParameters()) {
				getAllTerms(subterm);
			}
		} else if (term instanceof ConstantTerm) {
			mAllTerms.add(term);

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
				final Term bvEqLHS = apAtom.getParameters()[0];
				final Term bvEqRHS = apAtom.getParameters()[1];
				if (bvEqLHS.getSort().isBitVecSort()) {
					assert bvEqRHS.getSort().isBitVecSort();
					mClausifier.getLogger().debug("Set BitVec Literal: " + literal.getSMTFormula(getTheory()));
					mBVLiterals.add(literal);
				}

				final Term bvultTerm = getBvult(literal);
				if (bvultTerm != null) {
					final Term from = ((ApplicationTerm) bvultTerm).getParameters()[0];
					final Term to = ((ApplicationTerm) bvultTerm).getParameters()[1];
					mBvultGraph.addVertex(from);
					mBvultGraph.addVertex(to);
					if (literal.getSign() == 1) {
						mBvultGraph.addEdge(mBvultGraph.getVertex(from), literal, mBvultGraph.getVertex(to));
					}

					mClausifier.getLogger().debug("Set BitVec Literal: " + literal.getSMTFormula(getTheory()));
					mBVLiterals.add(literal);
				}

				// Trivial Literal:
				if (bvEqLHS.toString().equals(bvEqRHS.toString())) {
					if (((ApplicationTerm) literal.getSMTFormula(getTheory())).getFunction().getName()
							.equals("not")) {
						final Literal[] conflictSet = new Literal[1];
						conflictSet[0] = literal.negate();
						final Clause conflict = new Clause(conflictSet);
						return conflict;
					}
					return null;
				}
				if ((bvEqLHS instanceof ConstantTerm) && (bvEqRHS instanceof ConstantTerm)) {
					if (!BVUtils.getConstAsString((ConstantTerm) bvEqLHS)
							.equals(BVUtils.getConstAsString((ConstantTerm) bvEqRHS))) {
						if (((ApplicationTerm) literal.getSMTFormula(getTheory())).getFunction().getName()
								.equals("not")) {
							return null;
						}
						final Literal[] conflictSet = new Literal[1];
						conflictSet[0] = literal.negate();
						final Clause conflict = new Clause(conflictSet);
						return conflict;
					}
				}
			}

		}


		return null;
	}

	@Override
	public void backtrackLiteral(final Literal literal) {
		mBVLiterals.remove(literal);
	}

	@Override
	public Clause checkpoint() {
		// wenn alle kenne nach unitclausel schaun
		long time;
		if (Config.PROFILE_TIME) {
			time = System.nanoTime();
		}
		for (final Literal lit : mBVLiterals) {
			final Term bvult = getBvult(lit);
			if (bvult != null && lit.getSign() == 1) {
				final Vertex ver = mBvultGraph.getVertex(((ApplicationTerm) bvult).getParameters()[0]);
				if (!ver.isVisited()) {
					System.out.println("Check kreis for " + ver.getTerm() + " lit: " + lit);
					final HashSet<Literal> circle = new HashSet<>();
					final HashSet<Literal> conflict = mBvultGraph.getCycle(ver);
					// TODO negate lit for conflict
					System.out.println(conflict);
				}


			}

		}
		mBvultGraph.resetCycleVisited();
		if (Config.PROFILE_TIME) {
			addBvultGraphTime(System.nanoTime() - time);
		}
		return null;
	}

	/*
	 * Bvult Literals are CCEqualities of the form (bvult == true).
	 * CClosure creates additional CCequalities for each such bvult term of form !(bvult == false)
	 * We will ignore them.
	 */
	private Term getBvult(final Literal lit) {
		final DPLLAtom atom = lit.getAtom();

		if (atom.getSMTFormula(getTheory()) instanceof ApplicationTerm) {
			final ApplicationTerm apAtom = (ApplicationTerm) atom.getSMTFormula(getTheory());

			assert apAtom.getFunction().getName().equals("=");

			if(apAtom.getParameters()[0] instanceof ApplicationTerm) {
				if (((ApplicationTerm) apAtom.getParameters()[0]).getFunction().getName().equals("bvult")) {
					if (apAtom.getParameters()[1].equals(getTheory().mFalse)) {
						return null;
					}
					return  apAtom.getParameters()[0];
				}
			} else if (apAtom.getParameters()[1] instanceof ApplicationTerm) {
				if (((ApplicationTerm) apAtom.getParameters()[1]).getFunction().getName().equals("bvult")) {
					if (apAtom.getParameters()[0].equals(getTheory().mFalse)) {
						return null;
					}
					return apAtom.getParameters()[1];
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
		// bitblasting
		final DPLLEngine engine = new DPLLEngine(mClausifier.getLogger(), () -> false); // TODO TimeHandler
		engine.setProofGeneration(true);

		long time;
		if (Config.PROFILE_TIME) {
			time = System.nanoTime();
		}
		mClausifier.getLogger().debug("Starting Bitblasting");

		// collect all terms from all set literals
		for (final Literal lit : mBVLiterals) {
			final Term atom = lit.getAtom().getSMTFormula(getTheory());
			final Term bvult = getBvult(lit);
			if (bvult != null) {
				getAllTerms(bvult);
			} else { // bvult null if (bvult == false) TODO
				getAllTerms(atom);
			}
		}
		mBitblaster.bitBlasting(mBVLiterals, mAllTerms, engine.getAssertionStackLevel());
		// mAllTerms = new LinkedHashSet<>(); //reset allTerms?
		mClausifier.getLogger().debug("Finished Bitblasting");
		if (Config.PROFILE_TIME) {
			addBitBlastingTime(System.nanoTime() - time);
		}
		if (Config.PROFILE_TIME) {
			time = System.nanoTime();
		}
		for (final DPLLAtom atom : mBitblaster.getBoolAtoms()) {
			engine.addAtom(atom);
		}
		mClauseCount += mBitblaster.getClauses().size();
		for (final Clause cl : mBitblaster.getClauses()) {
			engine.addClause(cl);
		}
		mClausifier.getLogger().info("Bitblasting DPLL:");
		final boolean sat = engine.solve();
		if (Config.PROFILE_TIME) {
			addDPLLBitBlastTime(System.nanoTime() - time);
		}
		mClausifier.getLogger().debug("Bitblasting DPLL solved");

		if (sat) {
			// TODO Model generation
			final Term[] model = engine.getSatisfiedLiterals(getTheory());
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
			final Clause unsat = engine.getProof();
			final HashSet<Literal> unsatcore = getUnsatCore(unsat, mBitblaster.getLiteralMap());
			final Literal[] cores = new Literal[unsatcore.size()];
			int i = 0;
			for (final Literal c : unsatcore) {
				cores[i] = c;
				mClausifier.getLogger().debug("Unsat Core: " + c.getSMTFormula(getTheory()));
				i ++;
			}
			return new Clause(cores, mClausifier.getStackLevel());
		}
		return null;
	}

	/*
	 * Searches some sort of Unsat Core in the Bitblasting result.
	 * Returns the Conflict Clause, containing this core.
	 */
	private HashSet<Literal> getUnsatCore(final Clause unsat, final HashMap<Term, Literal> literals) {
		final HashSet<Literal> res = new HashSet<>();
		final ArrayDeque<Clause> todo = new ArrayDeque<>();
		todo.push(unsat);
		final IdentityHashSet<Clause> visited = new IdentityHashSet<>();
		while (!todo.isEmpty()) {
			final Clause c = todo.pop();
			if (visited.add(c)) {
				if (c.getProof().isLeaf()) {
					final Term lit = c.getLiteral(0).getAtom().getSMTFormula(getTheory());
					if (literals.containsKey(lit)) {
						res.add(literals.get(lit).negate());
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
		// zurück geben, welches literal nicht gelten darf weil sonst transitivity
		// literal.getAtom().mExplanation und erklärung in (das was conflict wäre wenns gilt)
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
		logger.info("BVTimes: BB " + mBitBlastingTime + " DPLL " + mAddDPLLBitBlastTime + " Graph " + mBvultGraphTime);
		logger.info("BitBlastingClauses: " + mClauseCount);
	}

	@Override
	public void dumpModel(final LogProxy logger) {
		// TODO Auto-generated method stub

	}

	@Override
	public void increasedDecideLevel(final int currentDecideLevel) {
		// neuer scope
		// TODO Auto-generated method stub

	}

	@Override
	public void decreasedDecideLevel(final int currentDecideLevel) {
		// TODO Auto-generated method stub

	}

	@Override
	public Clause backtrackComplete() {
		//
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public void backtrackAll() {
		// TODO Auto-generated method stub
		// mBVLiterals
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
		// TODO
		// bb atome, unit clause,
		// Zeit für checkconflict und für ste lit, knoten im graphen zeit den cyclus zu finden
		return new Object[] { ":BV",
				new Object[][] {
			{ "Times", new Object[][] { { "BitBlasting", mBitBlastingTime },
				{ "Dpll BitBlasting", mAddDPLLBitBlastTime },
				{ "Bvult Graph", mBvultGraphTime }

			} } } };
	}


	public DPLLEngine getEngine() {
		return mClausifier.getEngine();
	}

	public Theory getTheory() {
		return mClausifier.getTheory();
	}
}