package de.uni_freiburg.informatik.ultimate.smtinterpol.muses;

import java.util.ArrayList;
import java.util.BitSet;
import java.util.function.Function;

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
	boolean mMapModifiedSinceLastSolve;
	BitSet mImpliedCrits;
	BitSet mMaximalUnexploredSubset;
	BitSet mLastWorkingSet;

	public UnexploredMap(final DPLLEngine engine, final Translator translator) {
		mEngine = engine;
		mTranslator = translator;
		mMapModifiedSinceLastSolve = true;
	}

	/**
	 * Blocks all supersets of the given unsatisfiable set (since they are also unsatisfiable).
	 */
	public void BlockUp(final BitSet unsatSet) {
		mMapModifiedSinceLastSolve = true;
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
		mMapModifiedSinceLastSolve = true;
		final ArrayList<Literal> clause = new ArrayList<>();
		final BitSet notInSatSet = (BitSet) satSet.clone();
		notInSatSet.flip(0, mTranslator.getNumberOfConstraints());
		for (int i = notInSatSet.nextSetBit(0); i >= 0; i = notInSatSet.nextSetBit(i + 1)) {
			clause.add(mTranslator.translate2Atom(i));
		}
		mEngine.addClause(new Clause(clause.toArray(new Literal[clause.size()]), mEngine.getAssertionStackLevel()));
	}

	/**
	 * Finds a maximal unexplored subset and the implied crits for the given working set. They can then be accessed by
	 * {@link getMaximalUnexploredSubset()} and {@link getImpliedCrits}.
	 */
	private boolean findMaximalUnexploredSubsetAndImpliedCrits(final BitSet workingSet) {
		mMapModifiedSinceLastSolve = false;
		mLastWorkingSet = (BitSet) workingSet.clone();
		final BitSet notInWorkingSet = (BitSet) workingSet.clone();
		notInWorkingSet.flip(0, mTranslator.getNumberOfConstraints());
		mEngine.push();
		for (int i = notInWorkingSet.nextSetBit(0); i >= 0; i = notInWorkingSet.nextSetBit(i + 1)) {
			final Literal[] unitClause = new Literal[1];
			unitClause[0] = mTranslator.translate2Atom(i).negate();
			mEngine.addClause(new Clause(unitClause, mEngine.getAssertionStackLevel()));
		}
		if (mEngine.solve()) {
			mMaximalUnexploredSubset = collectAtomsWithCriteria(workingSet, this::isSetToTrue);
			mImpliedCrits = collectAtomsWithCriteria(workingSet, this::isImpliedToTrue);
			mEngine.pop(1);
			return true;
		} else {
			mMaximalUnexploredSubset = new BitSet();
			mImpliedCrits = new BitSet();
			mEngine.pop(1);
			return false;
		}
	}

	/**
	 * If it has not already been found, this method finds a maximal unexplored subset of the given workingSet.
	 * If no maximal unexplored subset has been found, it returns a BitSet with all values set to false.
	 */
	public BitSet getMaximalUnexploredSubsetOf(final BitSet workingSet) {
		if (mMapModifiedSinceLastSolve || workingSet.equals(mLastWorkingSet)) {
			findMaximalUnexploredSubsetAndImpliedCrits(workingSet);
		}
		return mMaximalUnexploredSubset;
	}

	/**
	 * If this no ImpliedCrits have been found, it returns a BitSet with all values set to false.
	 */
	public BitSet getImpliedCritsOf(final BitSet workingSet) {
		if (mMapModifiedSinceLastSolve || workingSet.equals(mLastWorkingSet)) {
			findMaximalUnexploredSubsetAndImpliedCrits(workingSet);
		}
		return mImpliedCrits;
	}

	/**
	 * Collects all Atoms that are contained in workingSet and fulfill the given criteria. The criteria Function takes
	 * the Number of the atom and returns True if it fulfills certain criteria, false otherwise. Assumes, that all Atoms
	 * have been decided (else NullPointerExceptions may occur).
	 */
	private BitSet collectAtomsWithCriteria(final BitSet workingSet, final Function<Integer, Boolean> criteria) {
		final BitSet model = new BitSet(mTranslator.getNumberOfConstraints());
		for (int i = workingSet.nextSetBit(0); i >= 0; i = workingSet.nextSetBit(i + 1)) {
			if (criteria.apply(i)) {
				model.set(i);
			}
		}
		return model;
	}

	private Boolean isSetToTrue(final int atomNumber) {
		return mTranslator.translate2Atom(atomNumber).getDecideStatus().getSign() == 1;
	}

	private Boolean isImpliedToTrue(final int atomNumber) {
		return isSetToTrue(atomNumber) && mTranslator.translate2Atom(atomNumber).getDecideLevel() == 0;
	}
}
