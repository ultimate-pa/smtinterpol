/*
 * Copyright (C) 2018 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.smtinterpol.theory.quant;

import java.util.BitSet;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.logic.FunctionSymbol;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.Literal;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.cclosure.CCTerm;
import de.uni_freiburg.informatik.ultimate.util.datastructures.ScopedHashMap;

/**
 * Represents a clause in the QuantifierTheory. This means, it contains at least one literal with an (implicitly)
 * universally quantified variable.
 *
 * @author Tanja Schindler
 */
public class QuantClause {

	private final QuantifierTheory mQuantTheory;
	/**
	 * The ground literals in this clause.
	 */
	private final Literal[] mGroundLits;
	/**
	 * The quantified literals in this clause.
	 */
	private final QuantLiteral[] mQuantLits;
	/**
	 * The variables occurring in this clause and the information needed for instantiation.
	 */
	private final Map<TermVariable, VarInfo> mVarInfos;
	/**
	 * For each variable, the set of potentially interesting instantiations.
	 */
	private ScopedHashMap<TermVariable, Set<Term>> mInstantiationTerms; // TODO Should we use SharedTerm?

	/**
	 * Build a new QuantClause. At least one literal must not be ground. This should only be called after performing
	 * DER.
	 * 
	 * @param groundLits
	 *            the ground literals in this clause.
	 * @param quantLits
	 *            the quantified literals in this clause. This must not be empty.
	 * @param quantTheory
	 *            the QuantifierTheory.
	 */
	QuantClause(final Literal[] groundLits, final QuantLiteral[] quantLits, final QuantifierTheory quantTheory) {
		assert quantLits.length != 0;
		mQuantTheory = quantTheory;
		mGroundLits = groundLits;
		mQuantLits = quantLits;
		mVarInfos = new HashMap<TermVariable, VarInfo>();

		mInstantiationTerms = new ScopedHashMap<TermVariable, Set<Term>>();
	}

	public QuantifierTheory getTheory() {
		return mQuantTheory;
	}

	public Literal[] getGroundLits() {
		return mGroundLits;
	}

	public QuantLiteral[] getQuantLits() {
		return mQuantLits;
	}

	public Set<TermVariable> getVars() {
		return mVarInfos.keySet();
	}

	public void push() {
		mInstantiationTerms.beginScope();
	}

	public void pop() {
		mInstantiationTerms.endScope();
	}

	/**
	 * Go through the quantified literals in this clause to collect information the appearing variables. In particular,
	 * for each variable we collect the lower and upper ground bounds, and the functions and positions where the
	 * variable appears as arguments.
	 */
	public void collectVarInfo() {
		for (final QuantLiteral lit : mQuantLits) {
			final QuantLiteral atom = lit.getAtom();
			if (atom instanceof QuantVarConstraint) {
				// Here, we need to add lower and/or upper bounds.
				final QuantVarConstraint constraint = (QuantVarConstraint) atom;
				final TermVariable lowerVar = constraint.getLowerVar();
				final TermVariable upperVar = constraint.getUpperVar();
				// Note that the constraint can be both a lower and upper bound - if it consists of two variables.
				if (lowerVar != null) {
					final Term upperBound;
					if (!mVarInfos.containsKey(lowerVar)) {
						mVarInfos.put(lowerVar, new VarInfo());
					}
					VarInfo varInfo = mVarInfos.get(lowerVar);
					if (upperVar != null) {
						upperBound = upperVar;
					} else {
						upperBound = constraint.getGroundBound().getTerm();
					}
					varInfo.addUpperBound(upperBound);
				}
				if (upperVar != null) {
					final Term lowerBound;
					if (!mVarInfos.containsKey(upperVar)) {
						mVarInfos.put(upperVar, new VarInfo());
					}
					VarInfo varInfo = mVarInfos.get(upperVar);
					if (lowerVar != null) {
						lowerBound = lowerVar;
					} else {
						lowerBound = constraint.getGroundBound().getTerm();
					}
					varInfo.addLowerBound(lowerBound);
				}
			} else if (atom instanceof QuantEUBoundConstraint || atom instanceof QuantEUEquality) {
				// Here, we need to add the positions where variables appear as arguments of functions.
				Set<EUTerm> subTerms;
				if (atom instanceof QuantEUBoundConstraint) {
					final QuantEUBoundConstraint euConstraint = (QuantEUBoundConstraint) atom;
					final EUTerm affineTerm = euConstraint.getAffineTerm();
					subTerms = mQuantTheory.getSubEUTerms(affineTerm);
				} else {
					final QuantEUEquality euEq = (QuantEUEquality) atom;
					final EUTerm lhs = euEq.getLhs();
					final EUTerm rhs = euEq.getRhs();
					subTerms = mQuantTheory.getSubEUTerms(lhs);
					subTerms.addAll(mQuantTheory.getSubEUTerms(rhs));
				}
				for (final EUTerm sub : subTerms) {
					if (sub instanceof QuantAppTerm) {
						QuantAppArg[] args = ((QuantAppTerm) sub).getArgs();
						FunctionSymbol func = ((QuantAppTerm) sub).getFunc();
						for (int i = 0; i < args.length; i++) {
							if (args[i].isVar()) {
								final TermVariable var = args[i].getVar();
								if (!mVarInfos.containsKey(var)) {
									mVarInfos.put(var, new VarInfo());
								}
								VarInfo varInfo = mVarInfos.get(var);
								varInfo.addPosition(func, i);
							}
						}
					}
				}
			}
		}
	}

	/**
	 * Compute the possible instantiation terms for each variable.
	 */
	public void computeInstantiationTerms() {
		for (final TermVariable var : mVarInfos.keySet()) {
			final Set<Term> instTerms = computeInstantiationTerms(var); // TODO Should we use shared terms?
			if (!mInstantiationTerms.containsKey(var)) {
				mInstantiationTerms.put(var, new HashSet<Term>());
			}
			mInstantiationTerms.get(var).addAll(instTerms);
		}
		// If two variables depend on each other, synchronize their instantiation sets.
		for (final TermVariable var : mInstantiationTerms.keySet()) {
			// TODO Both lower and upper?
			for (final Term term : mVarInfos.get(var).mLowerBoundTerms) {
				if (term instanceof TermVariable) {
					final TermVariable otherVar = (TermVariable) term;
					mInstantiationTerms.get(var).addAll(mInstantiationTerms.get(otherVar));
				}
			}
			for (final Term term : mVarInfos.get(var).mUpperBoundTerms) {
				if (term instanceof TermVariable) {
					final TermVariable otherVar = (TermVariable) term;
					mInstantiationTerms.get(var).addAll(mInstantiationTerms.get(otherVar));
				}
			}
		}
	}

	/**
	 * Compute the ground terms which a given variable should be instantiated with.
	 * <p>
	 * This method does not consider dependencies between variables. They must be taken care of after computing the sets
	 * for each single variable.
	 * 
	 * @param var
	 *            the TermVariable which we compute the instantiation terms for.
	 * @return a Set of SharedTerms.
	 */
	private Set<Term> computeInstantiationTerms(TermVariable var) { // TODO Should we use SharedTerm?
		final VarInfo info = mVarInfos.get(var);
		assert info != null;
		final HashSet<Term> instantiationTerms = new HashSet<Term>();

		// TODO: lower or upper bounds or both?
		for (final Term lower : info.mLowerBoundTerms) {
			if (!(lower instanceof TermVariable)) {
				instantiationTerms.add(lower);
			}
		}
		for (final Term upper : info.mUpperBoundTerms) {
			if (!(upper instanceof TermVariable)) {
				instantiationTerms.add(upper);
			}
		}

		// retrieve from CClosure all ground terms that appear under the same functions at the same positions as var
		final Set<CCTerm> ccTerms = new HashSet<CCTerm>();
		final Map<FunctionSymbol, BitSet> positions = info.mFuncArgPositions;
		for (final FunctionSymbol func : positions.keySet()) {
			final BitSet pos = positions.get(func);
			for (int i = pos.nextSetBit(0); i >= 0; i = pos.nextSetBit(i + 1)) {
				final Set<CCTerm> argTerms = mQuantTheory.mCClosure.getArgTermsForFunc(func, i);
				if (argTerms != null) {
					ccTerms.addAll(argTerms);
				}
			}
		}
		for (final CCTerm ccTerm : ccTerms) {
			instantiationTerms.add(ccTerm.getSharedTerm().getTerm());
		}
		return instantiationTerms;
	}

	/**
	 * Instantiate this clause with a given substitution.
	 *
	 * TODO Each type of QuantLiteral needs to have an instantiation method that should build the corresponding literal.
	 *
	 * @param substitution
	 *            pairs of TermVariables and ground Terms that are used to instantiate the corresponding TermVariable.
	 * @return the ground literals.
	 */
	public Literal[] instantiate(Map<TermVariable, Term> substitution) {
		int groundLength = mGroundLits.length;
		Literal[] instClause = new Literal[groundLength + mQuantLits.length];
		// Copy the ground literals
		System.arraycopy(mGroundLits, 0, instClause, 0, groundLength);
		// Instantiate QuantLiterals
		for (int i = 0; i < mQuantLits.length; i++) {
			instClause[groundLength + i] = mQuantLits[i].instantiate(substitution);
		}
		return instClause;
	}

	/**
	 * Contains information for variable instantiation, i.e. - the functions where the variable is an argument and this
	 * argument's position, and - the lower and upper bounds for the variable.
	 */
	private class VarInfo {
		private Map<FunctionSymbol, BitSet> mFuncArgPositions;
		// TODO Do we need both lower and upper bounds?
		private Set<Term> mLowerBoundTerms;
		private Set<Term> mUpperBoundTerms;

		/**
		 * Create a new VarInfo. This is used to store information for one variable: - lower and upper ground bounds and
		 * - functions and positions where the variable appears as argument.
		 */
		public VarInfo() {
			mFuncArgPositions = new HashMap<FunctionSymbol, BitSet>();
			mLowerBoundTerms = new HashSet<Term>();
			mUpperBoundTerms = new HashSet<Term>();
		}

		/**
		 * Add a position where the variable appears as function argument.
		 * 
		 * @param func
		 *            the function under which the variable appears as argument.
		 * @param pos
		 *            the position of this argument.
		 */
		public void addPosition(final FunctionSymbol func, final int pos) {
			if (mFuncArgPositions.containsKey(func)) {
				BitSet occs = mFuncArgPositions.get(func);
				occs.set(pos);
			} else {
				BitSet occs = new BitSet(func.getParameterSorts().length);
				occs.set(pos);
				mFuncArgPositions.put(func, occs);
			}
		}

		/**
		 * Add a lower bound for the variable.
		 * 
		 * @param lowerBound
		 *            the lower bound. This can also be another variable.
		 */
		public void addLowerBound(final Term lowerBound) {
			mLowerBoundTerms.add(lowerBound);
		}

		/**
		 * Add an upper bound for the variable.
		 * 
		 * @param upperBound
		 *            the upper bound. This can also be another variable.
		 */
		public void addUpperBound(final Term upperBound) {
			mUpperBoundTerms.add(upperBound);
		}
	}
}
