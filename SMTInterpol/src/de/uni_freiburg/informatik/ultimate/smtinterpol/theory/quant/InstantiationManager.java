/*
 * Copyright (C) 2019 University of Freiburg
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

import java.util.ArrayList;
import java.util.HashMap;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.FormulaUnLet;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.smtinterpol.convert.Clausifier;
import de.uni_freiburg.informatik.ultimate.smtinterpol.convert.EqualityProxy;
import de.uni_freiburg.informatik.ultimate.smtinterpol.convert.SMTAffineTerm;
import de.uni_freiburg.informatik.ultimate.smtinterpol.convert.SharedTerm;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.Literal;
import de.uni_freiburg.informatik.ultimate.smtinterpol.proof.SourceAnnotation;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.linar.MutableAffinTerm;

/**
 * This class takes care of clause, literal and term instantiation.
 * 
 * Literals and clauses are only created if necessary, in particular, false literals as well as clauses that would
 * contain true literals are not created.
 * 
 * @author Tanja Schindler
 *
 */
public class InstantiationManager {

	private final Clausifier mClausifier;
	private final QuantifierTheory mQuantTheory;

	public InstantiationManager(Clausifier clausifier, QuantifierTheory quantTheory) {
		mClausifier = clausifier;
		mQuantTheory = quantTheory;
	}

	/**
	 * Instantiate a clause with a given substitution. Note that partial instantiation is not supported.
	 * 
	 * @param clause
	 *            a clause containing at least one quantified literal
	 * @param substitution
	 *            pairs of variable and ground term that is used to instantiate the corresponding variable.
	 * 
	 * @return the set of ground literals, or null if the clause would be true.
	 */
	public Literal[] instantiateClause(final QuantClause clause, final Map<TermVariable, Term> substitution) {
		// Compute proxies for literal instances
		final ArrayList<Term> litProxies = new ArrayList<Term>();
		for (int i = 0; i < clause.getQuantLits().length; i++) {
			final boolean isNeg = clause.getQuantLits()[i].isNegated();
			final QuantLiteral atom = clause.getQuantLits()[i].getAtom();
			Term prox = instantiateLitProxy(atom, substitution, clause.getSource());
			if (!isNeg && prox.equals(mClausifier.getTheory().mTrue)
					|| isNeg && prox.equals(mClausifier.getTheory().mFalse)) {
				return null; // Don't instantiate the clause if a literal would be true.
			} else if (!isNeg && prox.equals(mClausifier.getTheory().mFalse)
					|| isNeg && prox.equals(mClausifier.getTheory().mTrue)) {
				// Don't instantiate a literal that would be false.
			} else {
				if (isNeg) {
					prox = mClausifier.getTheory().not(prox);
				}
				litProxies.add(prox);
			}
		}
		// None of the literals is trivially true, so build the clause. TODO Evaluate proxies before creating literals.
		final int groundLength = clause.getGroundLits().length;
		final int instLength = litProxies.size();
		Literal[] instClause = new Literal[groundLength + instLength];
		System.arraycopy(clause.getGroundLits(), 0, instClause, 0, groundLength);
		for (int i = 0; i < instLength; i++) {
			final Term litProxy = litProxies.get(i);
			assert litProxy instanceof ApplicationTerm;
			ApplicationTerm atomProxy = (ApplicationTerm) litProxy;
			boolean isNeg = false;
			if (atomProxy.getFunction().getName().equals("not")) {
				assert atomProxy.getParameters()[0] instanceof ApplicationTerm;
				atomProxy = (ApplicationTerm) atomProxy.getParameters()[0];
				isNeg = true;
			}
			Literal inst;
			if (atomProxy.getFunction().getName().equals("=")) {
				final SharedTerm left = mClausifier.getSharedTerm(atomProxy.getParameters()[0], clause.getSource());
				final SharedTerm right = mClausifier.getSharedTerm(atomProxy.getParameters()[1], clause.getSource());
				final EqualityProxy eq = left.createEquality(right);
				inst = eq.getLiteral(clause.getSource());
			} else {
				assert atomProxy.getFunction().getName().equals("<=") || atomProxy.getFunction().getName().equals("<"); // TODO Only <=?
				boolean strict = false;
				if (atomProxy.getFunction().getName().equals("<")) {
					strict = true;
				}
				final SMTAffineTerm sum = new SMTAffineTerm(atomProxy.getParameters()[0]);
				final MutableAffinTerm at = mClausifier.createMutableAffinTerm(sum, clause.getSource());
				inst = mQuantTheory.mLinArSolve.generateConstraint(at, strict);
			}
			if (isNeg) {
				inst = inst.negate();
			}
			instClause[groundLength + i] = inst;
		}
		return instClause;
	}

	/**
	 * Build a proxy instance for a QuantLiteral and a given instantiation.
	 * 
	 * 
	 * @param atom
	 *            the underlying atom of a QuantLiteral
	 * @return a term as proxy for the literal instance
	 */
	private Term instantiateLitProxy(QuantLiteral atom, Map<TermVariable, Term> instantiation,
			SourceAnnotation source) {
		assert !atom.isNegated();
		final Term litProxy;
		if (atom instanceof QuantEUEquality) {
			final QuantEUEquality eUeq = (QuantEUEquality) atom;
			final Term left = instantiateEUTerm(eUeq.getLhs(), instantiation);
			final Term right = instantiateEUTerm(eUeq.getRhs(), instantiation);
			litProxy = instantiateEqualityProxy(left, right);
		} else if (atom instanceof QuantVarEquality) {
			final QuantVarEquality varEq = (QuantVarEquality) atom;
			final Term left = instantiation.get(varEq.getLeftVar());
			final Term right =
					varEq.isBothVar() ? instantiation.get(varEq.getRightVar()) : varEq.getGroundTerm().getTerm();
			litProxy = instantiateEqualityProxy(left, right);
		} else if (atom instanceof QuantEUBoundConstraint) {
			final QuantEUBoundConstraint qBoundConstr = (QuantEUBoundConstraint) atom;
			final SMTAffineTerm smtAff = instantiateEUTerm(qBoundConstr.getAffineTerm(), instantiation);
			final Sort sort = instantiation.values().iterator().next().getSort();
			litProxy = instantiateBoundConstraintProxy(smtAff, false, sort);
		} else if (atom instanceof QuantVarConstraint) {
			final QuantVarConstraint varCons = (QuantVarConstraint) atom;
			final Term lower =
					(varCons.isBothVar() || !varCons.isLowerBound()) ? instantiation.get(varCons.getLowerVar())
							: varCons.getGroundBound().getTerm();
			final Term upper =
					(varCons.isBothVar() || varCons.isLowerBound()) ? instantiation.get(varCons.getUpperVar())
							: varCons.getGroundBound().getTerm();
			final SMTAffineTerm smtAff = SMTAffineTerm.create(upper);
			smtAff.add(Rational.MONE, lower);
			final Sort sort = instantiation.values().iterator().next().getSort();
			litProxy = instantiateBoundConstraintProxy(smtAff, false, sort);
		} else {
			litProxy = null;
			assert false : "No support for instantiation of QuantNamedAtom so far";
		}
		assert litProxy != null;
		return litProxy;
	}

	/**
	 * Create a proxy instance for an equality literal.
	 * 
	 * This method simplifies trivially true or false instances.
	 * 
	 * @return an equality term.
	 */
	private Term instantiateEqualityProxy(final Term left, final Term right) {
		final SMTAffineTerm diff = new SMTAffineTerm(left);
		diff.negate();
		diff.add(new SMTAffineTerm(right));
		if (diff.isConstant()) {
			if (diff.getConstant().equals(Rational.ZERO)) {
				return mClausifier.getTheory().mTrue;
			} else {
				return mClausifier.getTheory().mFalse;
			}
		}
		diff.div(diff.getGcd());
		Sort sort = left.getSort();
		// Normalize equality to integer logic if all variables are integer.
		if (mClausifier.getTheory().getLogic().isIRA() && sort.getName().equals("Real") && diff.isAllIntSummands()) {
			sort = mClausifier.getTheory().getSort("Int");
		}
		// Check for unsatisfiable integer formula, e.g. 2x + 2y = 1.
		if (sort.getName().equals("Int") && !diff.getConstant().isIntegral()) {
			return mClausifier.getTheory().mFalse;
		}
		// TODO Do we need to normalize more? (see Clausifier.createEqualityProxy(...))
		return mClausifier.getTheory().term("=", left, right);
	}

	/**
	 * Create a proxy instance for an inequality literal.
	 * 
	 * This method simplifies trivially true or false instances.
	 * 
	 * @return an equality term.
	 */
	private Term instantiateBoundConstraintProxy(SMTAffineTerm smtAff, boolean isStrict, Sort sort) {
		if (smtAff.isConstant()) {
			if (isStrict && smtAff.getConstant().isNegative()
					|| !isStrict && !smtAff.getConstant().negate().isNegative()) {
				return mClausifier.getTheory().mTrue;
			} else {
				return mClausifier.getTheory().mFalse;
			}
		}
		if (isStrict) {
			return mClausifier.getTheory().term("<", smtAff.toTerm(mClausifier.getTermCompiler(), sort),
					Rational.ZERO.toTerm(sort));
		} else {
			return mClausifier.getTheory().term("<=", smtAff.toTerm(mClausifier.getTermCompiler(), sort),
					Rational.ZERO.toTerm(sort));
		}
	}

	private Term instantiateEUTerm(final EUTerm euTerm, final Map<TermVariable, Term> termSubst) {
		if (euTerm instanceof GroundTerm) {
			return ((GroundTerm) euTerm).getTerm();
		}
		final FormulaUnLet unletter = new FormulaUnLet();
		unletter.addSubstitutions(termSubst);
		final Term inst = unletter.unlet(euTerm.getTerm());
		assert inst.getFreeVars().length == 0;
		return inst;
	}

	private SMTAffineTerm instantiateEUTerm(final QuantAffineTerm euAffine, final Map<TermVariable, Term> termSubst) {
		final HashMap<Term, Rational> summands = new HashMap<Term, Rational>();
		for (final EUTerm euTerm : euAffine.getSummands().keySet()) {
			final Term inst = instantiateEUTerm(euTerm, termSubst);
			Rational factor = euAffine.getSummands().get(euTerm);
			if (summands.containsKey(inst)) {
				factor = factor.add(summands.get(inst));
				summands.remove(inst);
			}
			if (!factor.equals(Rational.ZERO)) {
				summands.put(inst, factor);
			}
		}
		final SMTAffineTerm instAff = new SMTAffineTerm(summands, euAffine.getConstant(), null);
		return instAff;
	}
}
