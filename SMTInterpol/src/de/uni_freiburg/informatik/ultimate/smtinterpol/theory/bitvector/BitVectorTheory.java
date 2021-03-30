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
	private final ScopedArrayList<BvLiteral> mBVLiterals; // Linked Hash Set
	private final LinkedHashSet<Term> mAllTerms;
	private ScopedArrayList<String> mAllNewVarNames;
	private ScopedArrayList<Term> mAllNewVars;
	private final HashMap<Literal, BvLiteral> mLiteralMap; // All Bool Atoms, aux varaibles too
	final BitBlaster mBitblaster;

	public BitVectorTheory(final Clausifier clausifier) {

		mClausifier = clausifier;
		mBVLiterals = new ScopedArrayList<>();
		mAllTerms = new LinkedHashSet<>();
		mLiteralMap = new HashMap<>();
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
		boolean inequality = false;
		final DPLLAtom atom = literal.getAtom();

		if (atom.getSMTFormula(getTheory()) instanceof ApplicationTerm) {
			final ApplicationTerm apAtom = (ApplicationTerm) atom.getSMTFormula(getTheory());

			if (apAtom.getFunction().getName().equals("=")) {
				final Term bvEqLHS = apAtom.getParameters()[0];
				final Term bvEqRHS = apAtom.getParameters()[1];
				if(bvEqLHS.getSort().isBitVecSort()) {
					bitVecLiteral = true;
					assert bvEqRHS.getSort().isBitVecSort();
				}

				if (apAtom.getParameters().length == 0) {
					// literal is boolean predicat
					return null;
				}

				Term bvultTerm = null;
				Term bvultSign = null;
				if(apAtom.getParameters()[0] instanceof ApplicationTerm) {
					if (((ApplicationTerm) apAtom.getParameters()[0]).getFunction().getName().equals("bvult")) {
						bitVecLiteral = true;
						inequality = true;
						bvultTerm = apAtom.getParameters()[0];
						bvultSign = apAtom.getParameters()[1];
					}

				} else if (apAtom.getParameters()[1] instanceof ApplicationTerm) {
					if (((ApplicationTerm) apAtom.getParameters()[1]).getFunction().getName().equals("bvult")) {
						bitVecLiteral = true;
						inequality = true;
						bvultTerm = apAtom.getParameters()[1];
						bvultSign = apAtom.getParameters()[0];

					}
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

				// if (mLiteralMap.containsKey(literal.getAtom())) {
				// final BvLiteral bvLit = mLiteralMap.get(literal.getAtom());
				//
				// if (inequality) {
				// // bvultTerm;
				// if (bvultSign.equals(getTheory().mTrue) && (literal.getSign() == 1)) {
				// bvLit.setSign(true);
				// } else if (bvultSign.equals(getTheory().mTrue) && (literal.getSign() == -1)) {
				// bvLit.setSign(false);
				// } else if (bvultSign.equals(getTheory().mFalse) && (literal.getSign() == 1)) {
				// bvLit.setSign(false);
				// } else if (bvultSign.equals(getTheory().mFalse) && (literal.getSign() == -1)) {
				// bvLit.setSign(true);
				// } else {
				// throw new UnsupportedOperationException("Unknown Atom");
				// }
				//
				// } else {
				// if (literal.getSign() == 1) {
				// bvLit.setSign(true);
				// } else {
				// bvLit.setSign(false);
				// }
				// }
				// mBVLiterals.add(bvLit);
				// } else
				if(bitVecLiteral) {
					BvLiteral bvLit;
					if (inequality) {
						// bvultTerm;
						if (bvultSign.equals(getTheory().mTrue) && (literal.getSign() == 1)) {
							bvLit = new BvLiteral(literal, bvultTerm, true);
						} else if (bvultSign.equals(getTheory().mTrue) && (literal.getSign() == -1)) {
							bvLit = new BvLiteral(literal, bvultTerm, false);
						} else if (bvultSign.equals(getTheory().mFalse) && (literal.getSign() == 1)) {
							bvLit = new BvLiteral(literal, bvultTerm, false);
						} else if (bvultSign.equals(getTheory().mFalse) && (literal.getSign() == -1)) {
							bvLit = new BvLiteral(literal, bvultTerm, true);
						} else {
							throw new UnsupportedOperationException("Unknown Atom");
						}
						getAllTerms(bvultTerm);
					} else {
						bvLit = new BvLiteral(literal, apAtom, (literal.getSign() == 1));
						getAllTerms(apAtom); // For Bitblasting erst machen
					}
					mClausifier.getLogger().debug("Set BitVec Literal: " + literal.getSMTFormula(getTheory()));
					mBVLiterals.add(bvLit);
					mLiteralMap.put(literal, bvLit);
				}
			}

		}


		return null;
	}

	@Override
	public void backtrackLiteral(final Literal literal) {
		// TODO Auto-generated method stub
		mBVLiterals.remove(mLiteralMap.get(literal));
	}

	@Override
	public Clause checkpoint() {
		// TODO Auto-generated method stub
		// bvult transititititity
		// wenn alle kenne nach unitclausel schaun
		return null;
	}

	@Override
	public Clause computeConflictClause() {
		mClausifier.getLogger().debug("Checking for bvult transitivities");
		for (final BvLiteral lit : mBVLiterals) {
			if (lit.isBvult()) {
				final Term lowerBound = lit.getLhs();
				Term lowestBound = lit.getLhs(); // TODO
				final List<Term> upperBounds = new ArrayList<>();
				upperBounds.add(lit.getRhs());
				boolean terminate = false;
				while (!terminate) {
					terminate = true;
					for (final BvLiteral lit1 : mBVLiterals) {
						if (lit.isBvult() && upperBounds.contains(lit1.getLhs())
								&& !upperBounds.contains(lit1.getRhs())) {
							upperBounds.add(lit1.getRhs());
							terminate = false;
							break;
						} else if (lit.isBvult() && lit1.getRhs().equals(lowerBound)
								&& upperBounds.contains(lit1.getLhs()) && lit.getSign()) {
							final Literal[] conflict = new Literal[mBVLiterals.size()];
							int i = 0;
							for (final BvLiteral c : mBVLiterals) {
								// TODO alle literale in der transitivität
								conflict[i] = c.getLiteral().negate();
								i++;
							}
							System.out.println("Tranisitivität Conflict");
							return new Clause(conflict, mClausifier.getStackLevel());
						} else if (lit.isBvult() && lit1.getRhs().equals(lowerBound)
								&& !upperBounds.contains(lit1.getLhs())) {
							lowestBound = lit1.getLhs();
						}

					}


				}
				System.out.println(
						"transitivity: " + lowestBound + " bvult " + upperBounds.get(upperBounds.size() - 1));
			}
		}
		mClausifier.getLogger().debug("Finished bvult transitivity check");

		// TODO choose variable assignment nad try to show Sat using the const optimizations, prevents us from using
		// private final TermCompiler mCompiler = new TermCompiler();

		// bitblasting
		final DPLLEngine engine = new DPLLEngine(mClausifier.getLogger(), () -> false); // TODO TimeHandler
		// TODO fill mAllTerms
		engine.setProofGeneration(true);
		final ScopedArrayList<BvLiteral> allLiterals = mBVLiterals;
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
							.info("Model InputLiteral: " + mBitblaster.getLiteralMap().get(atom).getTerm());
						} else {
							// System.out.println("Model: " + t);

						}
					} else {
						if (mBitblaster.getLiteralMap().containsKey(t)) {
							mClausifier.getLogger()
							.info("Model InputLiteral: " + mBitblaster.getLiteralMap().get(t).getTerm());
						} else {
							// System.out.println("Model: " + t);
						}
					}
				} else {
					if (mBitblaster.getLiteralMap().containsKey(t)) {
						mClausifier.getLogger()
						.info("Model InputLiteral: " + mBitblaster.getLiteralMap().get(t).getTerm());
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
	private HashSet<Literal> getUnsatCore(final Clause unsat, final HashMap<Term, BvLiteral> literals) {
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
						res.add(literals.get(lit).getLiteral().negate());
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
