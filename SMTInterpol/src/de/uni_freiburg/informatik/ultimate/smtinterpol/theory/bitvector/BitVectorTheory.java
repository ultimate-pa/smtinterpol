package de.uni_freiburg.informatik.ultimate.smtinterpol.theory.bitvector;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedHashSet;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.ConstantTerm;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.logic.Theory;
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
	private final ScopedArrayList<Literal> mBVLiterals; // Linked Hash Set
	private final LinkedHashSet<Term> mAllTerms;
	private ScopedArrayList<String> mAllNewVarNames;
	private ScopedArrayList<Term> mAllNewVars;
	final BitBlaster mBitblaster;

	public BitVectorTheory(final Clausifier clausifier) {

		mClausifier = clausifier;
		mBVLiterals = new ScopedArrayList<>();
		mAllTerms = new LinkedHashSet<>();
		mBitblaster = new BitBlaster(getTheory());
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
	 * TODO NONRECURSIV?
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
		boolean bitVecLiteral = false;

		final DPLLAtom atom = literal.getAtom();

		if (atom.getSMTFormula(getTheory()) instanceof ApplicationTerm) {
			final ApplicationTerm apAtom = (ApplicationTerm) atom.getSMTFormula(getTheory());

			if (apAtom.getFunction().getName().equals("=")) {
				final Term bvEqLHS = apAtom.getParameters()[0];
				final Term bvEqRHS = apAtom.getParameters()[1];
				if (bvEqLHS.getSort().isBitVecSort()) { // TODO
					bitVecLiteral = true;
					assert bvEqRHS.getSort().isBitVecSort();
				}

				if (apAtom.getParameters().length == 0) {
					// literal is boolean predicat
					return null;
				}

				final Term bvultTerm = getBvult(literal);
				if (bvultTerm != null) {
					bitVecLiteral = true;
				}

				// Trivial Literal:
				if (bvEqLHS.toString().equals(bvEqRHS.toString())) {
					System.out.println("Trivial BVEquality: " + literal.getSMTFormula(getTheory()));
					// getEngine(). //tell dpll
					// .setPreferredStatus(status)
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
						System.out.println("Constant BVEquality: " + literal.getSMTFormula(getTheory()));
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


				if(bitVecLiteral) {
					if (bvultTerm != null) {
						// bvultTerm;
						getAllTerms(bvultTerm);
					} else {
						getAllTerms(apAtom); // For Bitblasting erst machen
					}
					mClausifier.getLogger().debug("Set BitVec Literal: " + literal.getSMTFormula(getTheory()));
					mBVLiterals.add(literal);

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
		final Clause bvultTrans = checkBvultTransitivity();
		return bvultTrans;
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

	private Clause checkBvultTransitivity() {
		for (final Literal lit : mBVLiterals) {
			final Term bvult = getBvult(lit);
			if (bvult != null && (lit.getSign() == 1)) {
				final HashSet<Literal> conflict = new HashSet<>();
				conflict.add(lit.negate());

				final ApplicationTerm apBvult = (ApplicationTerm) bvult;
				final Term lowerBound = apBvult.getParameters()[0];
				final List<Term> upperBounds = new ArrayList<>();
				upperBounds.add(apBvult.getParameters()[1]);

				boolean terminate = false;
				while (!terminate) {
					terminate = true;
					for (final Literal next : mBVLiterals) {
						final Term nextBvult = getBvult(next);
						if (nextBvult != null && (next.getSign() == 1)) {
							final ApplicationTerm apNxtBvult = (ApplicationTerm) nextBvult;
							final Term lhs = apNxtBvult.getParameters()[0];
							final Term rhs = apNxtBvult.getParameters()[1];

							if (upperBounds.contains(lhs) && !upperBounds.contains(rhs)) {
								// conflict.add(next.negate());
								upperBounds.add(rhs);
								terminate = false;
								break;
							} else if (rhs.equals(lowerBound) && upperBounds.contains(lhs)) {
								conflict.add(next.negate());
								final Literal[] bvultChain = new Literal[conflict.size()];
								int i = 0;
								for (final Literal c : conflict) {
									bvultChain[i] = c;
									i++;
								}
								mClausifier.getLogger().debug("Bvult transitivity conflict");
								return new Clause(bvultChain, mClausifier.getStackLevel());
							}
						}
					}

				}
			}
		}

		return null;
	}

	@Override
	public Clause computeConflictClause() {

		// TODO choose variable assignment nad try to show Sat using the const optimizations, prevents us from using
		// private final TermCompiler mCompiler = new TermCompiler();

		// bitblasting
		final DPLLEngine engine = new DPLLEngine(mClausifier.getLogger(), () -> false); // TODO TimeHandler
		// TODO fill mAllTerms
		engine.setProofGeneration(true);
		final ScopedArrayList<Literal> allLiterals = mBVLiterals;
		final int engineStackLevel = engine.getAssertionStackLevel();
		// TODO
		mClausifier.getLogger().debug("Starting Bitblasting");
		mBitblaster.bitBlasting(mBVLiterals, mAllTerms, engine.getAssertionStackLevel());
		mClausifier.getLogger().debug("Finished Bitblasting");

		for (final DPLLAtom atom : mBitblaster.getBoolAtoms()) {
			engine.addAtom(atom);
		}
		for (final Clause cl : mBitblaster.getClauses()) {
			engine.addClause(cl);
		}
		final boolean sat = engine.solve();
		mClausifier.getLogger().debug("Bitblasting DPLL solved");
		if (sat) {
			final Term[] model = engine.getSatisfiedLiterals(getTheory());
			for (final Term t : model) {
				if (t instanceof ApplicationTerm) {
					if (((ApplicationTerm) t).getFunction().getName().equals("not")) {
						final Term atom = ((ApplicationTerm) t).getParameters()[0];
						if (mBitblaster.getLiteralMap().containsKey(atom)) {
							mClausifier.getLogger()
							.info("Model InputLiteral: "
									+ mBitblaster.getLiteralMap().get(atom).getSMTFormula(getTheory()));
						} else {
							// System.out.println("Model: " + t);

						}
					} else {
						if (mBitblaster.getLiteralMap().containsKey(t)) {
							mClausifier.getLogger()
							.info("Model InputLiteral: "
									+ mBitblaster.getLiteralMap().get(t).getSMTFormula(getTheory()));
						} else {
							// System.out.println("Model: " + t);
						}
					}
				} else {
					if (mBitblaster.getLiteralMap().containsKey(t)) {
						mClausifier.getLogger()
						.info("Model InputLiteral: "
								+ mBitblaster.getLiteralMap().get(t).getSMTFormula(getTheory()));
					} else {
						// System.out.println("Model: " + t);
					}
				}

			}
		} else {
			final Clause unsat = engine.getProof();
			// for (final Term lit : engine.getSatisfiedLiterals(getTheory())) {
			// System.out.println("Unsat: " + lit);
			// }
			final HashSet<Literal> unsatcore = getUnsatCore(unsat, mBitblaster.getLiteralMap());
			final Literal[] cores = new Literal[unsatcore.size()];
			int i = 0;
			for (final Literal c : unsatcore) {
				cores[i] = c;
				System.out.println("Core: " + c.getSMTFormula(getTheory()));
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
		// TODO Auto-generated method stub

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

	@Override
	public Object[] getStatistics() {
		// TODO Auto-generated method stub
		return null;
	}



	public DPLLEngine getEngine() {
		return mClausifier.getEngine();
	}

	public Theory getTheory() {
		return mClausifier.getTheory();
	}
}
