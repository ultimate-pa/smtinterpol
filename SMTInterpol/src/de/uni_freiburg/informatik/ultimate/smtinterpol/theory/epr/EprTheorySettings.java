package de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr;

public class EprTheorySettings {

	/**
	 * If this is set to true, EprTheory just computes all groundings for a given quantified clause
	 * and returns them to the DPLLEngine.
	 */
	public static final boolean FullInstatiationMode = false;

	/**
	 * If this is true, we use all constants declared before the first assert as
	 * the AllConstants set. We assume that no further constants are added
	 * later. If this is false, we dynamically update the AllConstants set by
	 * scanning all the clauses we encounter for constants.
	 */
	public static final boolean UseAndFreezeDeclaredConstants = true;

}
