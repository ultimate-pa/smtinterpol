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

import java.util.Arrays;
import java.util.BitSet;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.logic.FunctionSymbol;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.smtinterpol.convert.SharedTerm;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.Literal;
import de.uni_freiburg.informatik.ultimate.smtinterpol.proof.SourceAnnotation;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.cclosure.CCTerm;
import de.uni_freiburg.informatik.ultimate.util.datastructures.ScopedHashSet;

/**
 * Represents a clause in the QuantifierTheory. This means, it contains at least one literal with an (implicitly)
 * universally quantified variable.
 *
 * @author Tanja Schindler
 */
public class QuantClause {

	private final QuantifierTheory mQuantTheory;
	private final Literal[] mGroundLits;
	private final QuantLiteral[] mQuantLits;

	private final SourceAnnotation mSource;

	/**
	 * The quantified variables in this clause. Defines an order on the variables.
	 */
	private final TermVariable[] mVars;
	/**
	 * For each variable, the information needed for instantiation.
	 */
	private final VarInfo[] mVarInfos;
	/**
	 * For each variable, the set of potentially interesting instantiations.
	 */
	private ScopedHashSet<SharedTerm>[] mPotentialInstantiations;
	
	/**
	 * The current instantiations of this clause.
	 */
	private ScopedHashSet<Term[]> mInstantiations;

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
	@SuppressWarnings("unchecked")
	QuantClause(final Literal[] groundLits, final QuantLiteral[] quantLits, final QuantifierTheory quantTheory,
			final SourceAnnotation source) {
		assert quantLits.length != 0;
		mQuantTheory = quantTheory;

		mGroundLits = groundLits;
		mQuantLits = quantLits;
		mSource = source;

		mVars = computeVars();
		mVarInfos = new VarInfo[mVars.length];
		collectVarInfos();

		mPotentialInstantiations = new ScopedHashSet[mVars.length];
		for (int i = 0; i < mVars.length; i++) {
			mPotentialInstantiations[i] = new ScopedHashSet<SharedTerm>();
		}
		mInstantiations = new ScopedHashSet<Term[]>();
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

	public SourceAnnotation getSource() {
		return mSource;
	}

	public TermVariable[] getVars() {
		return mVars;
	}

	void push() {
		for (int i = 0; i < mVars.length; i++) {
			mPotentialInstantiations[i].beginScope();
			mInstantiations.beginScope();
		}
	}

	void pop() {
		for (int i = 0; i < mVars.length; i++) {
			mPotentialInstantiations[i].endScope();
			mInstantiations.endScope();
		}
	}

	/**
	 * Compute the possible instantiation terms for each variable.
	 */
	void computePotentialInstantiations() {
		for (int i = 0; i < mVars.length; i++) {
			final TermVariable var = mVars[i];
			final Set<SharedTerm> instTerms = computePotentialInstantiations(var);
			mPotentialInstantiations[i].addAll(instTerms);
		}
		// If two variables depend on each other, synchronize their instantiation sets.
		for (int i = 0; i < mVars.length; i++) {
			for (final TermVariable otherVar : mVarInfos[i].mLowerVarBounds) {
				mPotentialInstantiations[i].addAll(mPotentialInstantiations[Arrays.asList(mVars).indexOf(otherVar)]);
			}
		}
		for (int i = 0; i < mVars.length; i++) {
			for (final TermVariable otherVar : mVarInfos[i].mUpperVarBounds) {
				mPotentialInstantiations[i].addAll(mPotentialInstantiations[Arrays.asList(mVars).indexOf(otherVar)]);
			}
		}
	}

	/**
	 * Compute all instances of this clause w.r.t. the sets of potential instantiation terms for each variable. Do not
	 * recompute existing instances.
	 */
	void instantiateAll() {
		// Compute all possible new instantiations
		Set<Term[]> allSubs = new HashSet<Term[]>();
		allSubs.add(new Term[mVars.length]);
		for (int i = 0; i < mVars.length; i++) {
			Set<Term[]> partialSubs = new HashSet<Term[]>();
			for (final Term[] oldSub : allSubs) {
				if (mPotentialInstantiations[i].isEmpty()) {
					// TODO Use lambda
				} else {
					for (final SharedTerm ground : mPotentialInstantiations[i]) {
						Term[] newSub = new Term[mVars.length];
						System.arraycopy(oldSub, 0, newSub, 0, mVars.length);
						newSub[i] = ground.getTerm();
						partialSubs.add(newSub);
					}
				}
			}
			allSubs.clear();
			allSubs.addAll(partialSubs);
		}
		allSubs.removeAll(mInstantiations);
		
		// Instantiate
		final Set<Literal[]> instances = new HashSet<Literal[]>();
		for (final Term[] subs : allSubs) {
			final Map<TermVariable, Term> subsMap = new HashMap<TermVariable, Term>();
			for (int i = 0; i < mVars.length; i++) {
				subsMap.put(mVars[i], subs[i]);
			}
			final Literal[] inst = mQuantTheory.getInstantiator().instantiateClause(this, subsMap);
			if (inst != null) {
				instances.add(inst);
			}
		}
		mInstantiations.addAll(allSubs);
		// TODO store and report conflicts
	}

	/**
	 * Compute the free variables in this clause.
	 * 
	 * @return an array containing the free variables in this clause.
	 */
	private TermVariable[] computeVars() {
		final Set<TermVariable> varSet = new HashSet<TermVariable>();
		for (final QuantLiteral lit : mQuantLits) {
			final TermVariable[] vars = lit.getTerm().getFreeVars();
			Collections.addAll(varSet, vars);
		}
		return varSet.toArray(new TermVariable[varSet.size()]);
	}

	/**
	 * Go through the quantified literals in this clause to collect information the appearing variables. In particular,
	 * for each variable we collect the lower and upper ground bounds, and the functions and positions where the
	 * variable appears as arguments.
	 */
	private void collectVarInfos() {
		for (final QuantLiteral lit : mQuantLits) {
			final QuantLiteral atom = lit.getAtom();
			if (atom instanceof QuantVarConstraint) {
				// Here, we need to add lower and/or upper bounds.
				final QuantVarConstraint constraint = (QuantVarConstraint) atom;
				final TermVariable lowerVar = constraint.getLowerVar();
				final TermVariable upperVar = constraint.getUpperVar();
				// Note that the constraint can be both a lower and upper bound - if it consists of two variables.
				if (lowerVar != null) {
					final int index = Arrays.asList(mVars).indexOf(lowerVar);
					if (mVarInfos[index] == null) {
						mVarInfos[index] = new VarInfo();
					}
					VarInfo varInfo = mVarInfos[index];
					if (upperVar != null) {
						varInfo.addUpperVarBound(upperVar);
					} else {
						varInfo.addUpperGroundBound(constraint.getGroundBound());
					}

				}
				if (upperVar != null) {
					final int index = Arrays.asList(mVars).indexOf(upperVar);
					if (mVarInfos[index] == null) {
						mVarInfos[index] = new VarInfo();
					}
					VarInfo varInfo = mVarInfos[index];
					if (lowerVar != null) {
						varInfo.addLowerVarBound(lowerVar);
					} else {
						varInfo.addLowerGroundBound(constraint.getGroundBound());
					}
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
								final int index = Arrays.asList(mVars).indexOf(var);
								if (mVarInfos[index] == null) {
									mVarInfos[index] = new VarInfo();
								}
								VarInfo varInfo = mVarInfos[index];
								varInfo.addPosition(func, i);
							}
						}
					}
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
	private Set<SharedTerm> computePotentialInstantiations(TermVariable var) {
		final VarInfo info = mVarInfos[Arrays.asList(mVars).indexOf(var)];
		assert info != null;
		final HashSet<SharedTerm> instantiationTerms = new HashSet<SharedTerm>();

		// TODO Maybe this part (adding bound terms) should already be done earlier...
		// TODO: lower or upper bounds or both?
		for (final GroundTerm lower : info.mLowerGroundBounds) {
			instantiationTerms.add(lower.getSharedTerm());
		}
		for (final GroundTerm upper : info.mUpperGroundBounds) {
			instantiationTerms.add(upper.getSharedTerm());
		}

		// Retrieve from CClosure all ground terms that appear under the same functions at the same positions as var
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
			instantiationTerms.add(ccTerm.getFlatTerm());
		}
		return instantiationTerms;
	}

	/**
	 * Contains information for variable instantiation, i.e. - the functions where the variable is an argument and this
	 * argument's position, and - the lower and upper bounds for the variable.
	 */
	private class VarInfo {
		private Map<FunctionSymbol, BitSet> mFuncArgPositions;
		// TODO Do we need both lower and upper bounds?
		private Set<GroundTerm> mLowerGroundBounds;
		private Set<GroundTerm> mUpperGroundBounds;
		private Set<TermVariable> mLowerVarBounds;
		private Set<TermVariable> mUpperVarBounds;

		/**
		 * Create a new VarInfo. This is used to store information for one variable: - lower and upper ground bounds and
		 * - functions and positions where the variable appears as argument.
		 */
		VarInfo() {
			mFuncArgPositions = new HashMap<FunctionSymbol, BitSet>();
			mLowerGroundBounds = new HashSet<GroundTerm>();
			mUpperGroundBounds = new HashSet<GroundTerm>();
			mLowerVarBounds = new HashSet<TermVariable>();
			mUpperVarBounds = new HashSet<TermVariable>();
		}

		/**
		 * Add a position where the variable appears as function argument.
		 * 
		 * @param func
		 *            the function under which the variable appears as argument.
		 * @param pos
		 *            the position of this argument.
		 */
		void addPosition(final FunctionSymbol func, final int pos) {
			if (mFuncArgPositions.containsKey(func)) {
				BitSet occs = mFuncArgPositions.get(func);
				occs.set(pos);
			} else {
				BitSet occs = new BitSet(func.getParameterSorts().length);
				occs.set(pos);
				mFuncArgPositions.put(func, occs);
			}
		}

		void addLowerGroundBound(final GroundTerm lowerBound) {
			mLowerGroundBounds.add(lowerBound);
		}

		void addUpperGroundBound(final GroundTerm upperBound) {
			mUpperGroundBounds.add(upperBound);
		}

		void addLowerVarBound(final TermVariable lower) {
			mLowerVarBounds.add(lower);
		}

		void addUpperVarBound(final TermVariable lower) {
			mUpperVarBounds.add(lower);
		}
	}
}
