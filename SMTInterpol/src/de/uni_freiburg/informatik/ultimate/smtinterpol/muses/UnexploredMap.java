package de.uni_freiburg.informatik.ultimate.smtinterpol.muses;

import java.util.ArrayList;
import java.util.BitSet;

import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.Clause;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.DPLLEngine;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.Literal;

/**
 * A class that represents the map of unexplored subsets in the MUS enumeration.
 *
 * @author LeonardFichtner
 *
 */
public class UnexploredMap {

	DPLLEngine mEngine;
	Translator mTranslator;

	public UnexploredMap(final DPLLEngine engine, final Translator translator) {
		mEngine = engine;
		mTranslator = translator;
	}

	/**
	 * Blocks all supersets of the given unsatisfiable set (since they are also unsatisfiable).
	 */
	public void BlockUp(final BitSet unsatSet) {
		final ArrayList<Literal> clause = new ArrayList<>();
		for (int i = unsatSet.nextSetBit(0); i >= 0; i = unsatSet.nextSetBit(i + 1)) {
			clause.add(mTranslator.translate2Atom(i).negate());
		}
		mEngine.addClause(new Clause(clause.toArray(new Literal[clause.size()]), mEngine.getAssertionStackLevel()));
	}

	/**
	 * Blocks all subsets of the given satisfiable set (since they are also satisfiable).
	 */
	public void BlockDown(final BitSet satSet) {
		final ArrayList<Literal> clause = new ArrayList<>();
		final BitSet notInSatSet = (BitSet) satSet.clone();
		notInSatSet.flip(0, mTranslator.getNumberOfConstraints());
		for (int i = notInSatSet.nextSetBit(0); i >= 0; i = notInSatSet.nextSetBit(i + 1)) {
			clause.add(mTranslator.translate2Atom(i));
		}
		mEngine.addClause(new Clause(clause.toArray(new Literal[clause.size()]), mEngine.getAssertionStackLevel()));
	}

	/**
	 * Gets a maximal unexplored subset (maximal in the sense that every superset of this set is explored) of the given
	 * working set. Returns a BitSet with all bits set to false, if there is no maximal unexplored subset.
	 */
	public BitSet getMaximalUnexploredSubsetOf(final BitSet workingSet) {
		final BitSet notInWorkingSet = (BitSet) workingSet.clone();
		notInWorkingSet.flip(0, mTranslator.getNumberOfConstraints());
		mEngine.push();
		for (int i = notInWorkingSet.nextSetBit(0); i >= 0; i = notInWorkingSet.nextSetBit(i + 1)) {
			final Literal[] unitClause = new Literal[1];
			unitClause[0] = mTranslator.translate2Atom(i).negate();
			mEngine.addClause(new Clause(unitClause, mEngine.getAssertionStackLevel()));
		}
		if (mEngine.solve()) {
			final BitSet maximalUnexplored = collectTrueAtomsOf(workingSet);
			mEngine.pop(1);
			return maximalUnexplored;
		}else {
			mEngine.pop(1);
			return new BitSet();
		}
	}

	/**
	 * Collects all Atoms that are contained in workingSet and are set to True. Assumes, that all
	 * Atoms have been decided (else NullPointerExceptions may occur).
	 */
	private BitSet collectTrueAtomsOf(final BitSet workingSet) {
		final BitSet model = new BitSet(mTranslator.getNumberOfConstraints());
		for (int i = workingSet.nextSetBit(0); i >= 0; i = workingSet.nextSetBit(i + 1)) {
			if (mTranslator.translate2Atom(i).getDecideStatus().getSign() == 1) {
				model.set(i);
			}
		}
		return model;
	}
}
