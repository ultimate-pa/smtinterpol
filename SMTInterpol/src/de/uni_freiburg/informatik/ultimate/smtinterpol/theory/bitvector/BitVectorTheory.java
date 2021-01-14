package de.uni_freiburg.informatik.ultimate.smtinterpol.theory.bitvector;

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
import de.uni_freiburg.informatik.ultimate.util.datastructures.ScopedArrayList;

/**
 *
 * @author Max Barth (max.barth95@gmx.de)
 *
 */
public class BitVectorTheory implements ITheory {
	private final Clausifier mClausifier;
	private final ScopedArrayList<Literal> mBVLiterals;
	private final ScopedArrayList<Term> mAllTerms;
	private ScopedArrayList<String> mAllNewVarNames;
	private ScopedArrayList<Term> mAllNewVars;

	public BitVectorTheory(final Clausifier clausifier) {

		mClausifier = clausifier;
		mBVLiterals = new ScopedArrayList<>();
		mAllTerms = new ScopedArrayList<>();

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
		// merke getsetze literale in scoped
		System.out.println("SetBvli");
		// mSolver.getTheory().getFunctionWithResult("(_ bv 4 4)");

		final DPLLAtom atom = literal.getAtom();

		if ((atom instanceof BVEquality) || (atom instanceof BVInEquality)) {
			mBVLiterals.add(literal);

			if (literal.getAtom().getSMTFormula(getTheory()) instanceof ApplicationTerm) {
				final ApplicationTerm appterm = (ApplicationTerm) literal.getAtom().getSMTFormula(getTheory());
				if (appterm.getFunction().getName().equals("=")) {
					final Term bvEqLHS = appterm.getParameters()[0];
					final Term bvEqRHS = appterm.getParameters()[1];
					getAllTerms(appterm); // For Bitblasting erst machen
					System.out.println("SetBVEquality: (= " + bvEqLHS + " " + bvEqRHS + ")");
					if ((bvEqLHS instanceof ConstantTerm) && (bvEqRHS instanceof ConstantTerm)) {
						if (!BVUtils.getConstAsString((ConstantTerm) bvEqLHS)
								.equals(BVUtils.getConstAsString((ConstantTerm) bvEqRHS))) {
							// if (!(bvEqLHS == bvEqRHS)) { //TODO BUGFIX sollte auf term nicht auf string ebene gehen
							final Literal[] conflictSet = new Literal[1];
							conflictSet[0] = literal.negate();
							final Clause conflict = new Clause(conflictSet);
							return conflict;
						}
					}

					if (bvEqLHS.toString().equals(bvEqRHS.toString())) {
						// getEngine(). //tell dpll
						// .setPreferredStatus(status)
						return null;
					}
				} else if (appterm.getFunction().getName().equals("bvult")) {
					final Term bvInEqLHS = appterm.getParameters()[0];
					final Term bvInEqRHS = appterm.getParameters()[1];
					getAllTerms(appterm);
					// TODO
				} else {
					// TODO Trivial Atom
				}
			}

		}
		return null;
	}

	@Override
	public void backtrackLiteral(final Literal literal) {
		// TODO Auto-generated method stub

	}

	@Override
	public Clause checkpoint() {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Clause computeConflictClause() {

		final DPLLEngine engine = new DPLLEngine(mClausifier.getLogger(), () -> false); // TODO terminationrequest
		// TODO fill mAllTerms

		final ScopedArrayList<Literal> allLiterals = mBVLiterals;
		final int engineStackLevel = engine.getAssertionStackLevel();
		final BitBlaster bitblaster = new BitBlaster(getTheory(), engineStackLevel, allLiterals, mAllTerms);
		final Term propEquiSat = bitblaster.bitBlasting();

		System.out.println("Bitblasting Result: " + propEquiSat.toStringDirect());


		for (final DPLLAtom atom : bitblaster.getBoolAtoms()) {
			engine.addAtom(atom);
		}
		for (final Clause cl : bitblaster.getClauses()) {
			engine.addClause(cl);
		}

		final boolean sat = engine.solve();
		System.out.println("DPLL: " + sat);
		if (sat) {
			final Term[] model = engine.getSatisfiedLiterals(getTheory());
			for (final Term t : model) {
				System.out.println("Model: " + t);
			}
		} else {
			final Literal[] unsat = engine.getUnsatAssumptions();
			System.out.println("DPLL: " + unsat.length);
			for (final Term lit : engine.getSatisfiedLiterals(getTheory())) {
				System.out.println("Unsat: " + lit);
			}
			return new Clause(unsat, mClausifier.getStackLevel());
		}
		return null;
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

	public DPLLAtom createEquality(final Term lhs, final Term rhs) {
		System.out.println("createBV_EQ_LIT");
		final BVEquality bveqlit = new BVEquality(lhs, rhs, mClausifier.getStackLevel());
		getEngine().addAtom(bveqlit);
		return bveqlit;

	}

	public DPLLEngine getEngine() {
		return mClausifier.getEngine();
	}

	public Theory getTheory() {
		return mClausifier.getTheory();
	}

	public DPLLAtom createInEquality(final Term lhs, final Term rhs) {
		System.out.println("createBV_BVULT_LIT");
		final BVInEquality bvInEqlit = new BVInEquality(lhs, rhs, mClausifier.getStackLevel());
		getEngine().addAtom(bvInEqlit);
		return bvInEqlit;

	}
}
