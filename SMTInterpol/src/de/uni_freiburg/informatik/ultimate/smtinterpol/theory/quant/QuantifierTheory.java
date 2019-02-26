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

import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.logic.Theory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.LogProxy;
import de.uni_freiburg.informatik.ultimate.smtinterpol.convert.Clausifier;
import de.uni_freiburg.informatik.ultimate.smtinterpol.convert.SMTAffineTerm;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.Clause;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.DPLLAtom;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.DPLLEngine;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.ITheory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.Literal;
import de.uni_freiburg.informatik.ultimate.smtinterpol.proof.SourceAnnotation;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.cclosure.CClosure;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.clauses.EprClauseState;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.linar.LinArSolve;
import de.uni_freiburg.informatik.ultimate.util.datastructures.ScopedHashSet;

/**
 * Solver for quantified formulas within the almost uninterpreted fragment (Restrictions on terms and literals are
 * explained in the corresponding classes. For reference, see Ge & de Moura, 2009).
 * 
 * This may be merged with the EPR solver implementation by Alexander Nutz in the future; for now, we keep it separate.
 *
 * @author Tanja Schindler
 */
public class QuantifierTheory implements ITheory {

	private final Clausifier mClausifier;
	private final LogProxy mLogger;
	private final Theory mTheory;
	private final DPLLEngine mEngine;

	final CClosure mCClosure;
	final LinArSolve mLinArSolve;

	private final EUTermManager mEUTermManager;
	private final InstantiationManager mInstantiationManager;

	/**
	 * The quantified literals built so far.
	 */
	private Map<Term, QuantLiteral> mQuantLits;

	/**
	 * Clauses that only the QuantifierTheory knows, i.e. that contain at least one literal with an (implicitly)
	 * universally quantified variable.
	 */
	private final ScopedHashSet<QuantClause> mQuantClauses;

	/**
	 * Clauses to propagate. At creation they would have been conflicts or unit clauses if the corresponding theories
	 * already knew the contained literals. They should be checked in setLiteral() and checkPoint() where they can be
	 * actual conflicts or unit clauses.
	 */
	private final List<List<Literal>> mPropClauses;

	public QuantifierTheory(final Theory th, final DPLLEngine engine, final Clausifier clausifier) {
		mClausifier = clausifier;
		mLogger = clausifier.getLogger();
		mTheory = th;
		mEngine = engine;

		mCClosure = clausifier.getCClosure();
		mLinArSolve = clausifier.getLASolver();

		mEUTermManager = new EUTermManager(this);
		mInstantiationManager = new InstantiationManager(mClausifier, this);

		mQuantLits = new HashMap<Term, QuantLiteral>();
		mQuantClauses = new ScopedHashSet<QuantClause>();
		
		mPropClauses = new ArrayList<List<Literal>>();
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

	@Override
	public Clause setLiteral(Literal literal) {
		// Mark clauses that are true due to this literal.
		for (final QuantClause quantClause : mQuantClauses) {
			if (Arrays.asList(quantClause.getGroundLits()).contains(literal)) {
				quantClause.setState(EprClauseState.Fulfilled);
			}
		}
		final Clause conflict = checkPropClausesForConflict();
		return conflict;
	}

	@Override
	public void backtrackLiteral(Literal literal) {
		// TODO Auto-generated method stub

	}

	@Override
	public Clause checkpoint() {
		for (final QuantClause clause : mQuantClauses) {
			clause.updateInterestingTermsAllVars();
		}
		mPropClauses.addAll(mInstantiationManager.findConflictAndUnitInstances());
		final Clause conflict = checkPropClausesForConflict();
		return conflict;
	}

	@Override
	public Clause computeConflictClause() {
		Clause conflict = checkpoint();
		if (conflict != null) {
			return conflict;
		}
		conflict = mInstantiationManager.instantiateAll();
		if (conflict != null) {
			return conflict;
		}
		// TODO
		// throw new UnsupportedOperationException("Support for quantifiers coming soon.");
		return null;
	}

	@Override
	public Literal getPropagatedLiteral() {
		// Nothing to do
		return null;
	}

	@Override
	public Clause getUnitClause(Literal literal) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Literal getSuggestion() {
		// TODO
		return null;
	}

	@Override
	public void printStatistics(LogProxy logger) {
		// TODO Auto-generated method stub

	}

	@Override
	public void dumpModel(LogProxy logger) {
		// TODO Auto-generated method stub

	}

	@Override
	public void increasedDecideLevel(int currentDecideLevel) {
		// TODO Auto-generated method stub

	}

	@Override
	public void decreasedDecideLevel(int currentDecideLevel) {
		// TODO Auto-generated method stub

	}

	@Override
	public Clause backtrackComplete() {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public void restart(int iteration) {
		// TODO Auto-generated method stub

	}

	@Override
	public void removeAtom(DPLLAtom atom) {
		// TODO Auto-generated method stub

	}

	@Override
	public Object push() {
		mQuantClauses.beginScope();
		for (final QuantClause qClause : mQuantClauses) {
			qClause.push();
		}
		return null;
	}

	@Override
	public void pop(Object object, int targetlevel) {
		mQuantClauses.endScope();
		for (final QuantClause qClause : mQuantClauses) {
			qClause.pop();
		}

	}

	@Override
	public Object[] getStatistics() {
		// TODO Auto-generated method stub
		return null;
	}

	/**
	 * Get a quantified equality atom for a term - in case the literal is supported.
	 * 
	 * We support the following (dis-)equality literals: (i) EUTerm = EUTerm (pos. and neg.), (ii) TermVariable =
	 * GroundTerm, (iii) TermVariable != GroundTerm, and (iv) TermVariable != TermVariable. Note that (iii) and (iv)
	 * require destructive equality reasoning.
	 * 
	 * @param term
	 *            the term for the underlying equality atom.
	 * @param positive
	 *            flag that indicates if the term appears positively or negated in the clause. This is required to
	 *            determine if the literal is supported.
	 * @param source
	 *            the source partition of the term.
	 * @param lhs
	 *            the term at the left hand side of the equality.
	 * @param rhs
	 *            the term at the right hand side of the equality.
	 * 
	 * @return the underlying equality atom as a QuantLiteral, if the literal is supported.
	 */
	public QuantLiteral getQuantEquality(Term term, boolean positive, SourceAnnotation source, Term lhs, Term rhs) {
		final QuantLiteral atom = mQuantLits.get(term);
		if (atom != null) {
			if (positive && atom.isSupported()) {
				return atom;
			} else if (!positive && atom.negate().isSupported()) {
				return atom;
			} else {
				throw new UnsupportedOperationException(
						(positive ? "Negated term " : "Term ") + term + " not in almost uninterpreted fragment!");
			}
		}

		SMTAffineTerm rightAff = SMTAffineTerm.create(rhs);
		rightAff.negate();
		SMTAffineTerm linAdded = SMTAffineTerm.create(lhs);
		linAdded.add(rightAff);
		Map<Term, Rational> summands = linAdded.getSummands();
		final Rational constant = linAdded.getConstant();

		TermVariable leftVar = null;
		TermVariable rightVar = null;
		final Iterator<Term> it = summands.keySet().iterator();
		while (it.hasNext()) {
			Term summand = it.next();
			if (summand instanceof TermVariable) {
				if (summands.get(summand).isNegative()) {
					if (rightVar != null) {
						throw new UnsupportedOperationException(
								"Term " + term + " not in almost uninterpreted fragment!");
					}
					rightVar = (TermVariable) summand;
					it.remove();
				} else {
					if (leftVar != null) {
						throw new UnsupportedOperationException(
								"Term " + term + " not in almost uninterpreted fragment!");
					}
					leftVar = (TermVariable) summand;
					it.remove();
				}
			}
		}

		if (leftVar != null && rightVar != null) {
			if (!positive && summands.isEmpty() && constant.equals(Rational.ZERO)) {
				QuantVarEquality varEq = new QuantVarEquality(term, leftVar, rightVar);
				mQuantLits.put(term, varEq);
				return varEq;
			}
		} else if (leftVar != null || rightVar != null) {
			if (positive && !term.getSort().getName().equals("Int")) { // We support var=ground only for integers.
				throw new UnsupportedOperationException("Term " + term + " not in almost uninterpreted fragment!");
			}
			// We can either do destructive equality reasoning later (if !positive), or build an aux axiom.
			SMTAffineTerm remainderAffine = new SMTAffineTerm(summands, constant);
			if (leftVar != null) {
				remainderAffine.negate();
			}
			Term remainder = remainderAffine.toTerm(mClausifier.getTermCompiler(), term.getSort());
			if (remainder.getFreeVars().length == 0) { // The variable can only be bound by ground terms.
				final EUTerm boundTerm = mEUTermManager.getEUTerm(remainder, source);
				assert boundTerm instanceof GroundTerm;
				final TermVariable var = leftVar != null ? leftVar : rightVar;
				QuantVarEquality varEq = new QuantVarEquality(term, var, (GroundTerm) boundTerm);
				mQuantLits.put(term, varEq);
				return varEq;
			}
		} else if (leftVar == null && rightVar == null) {
			final EUTerm lhsEU = mEUTermManager.getEUTerm(lhs, source);
			final EUTerm rhsEU = mEUTermManager.getEUTerm(rhs, source);
			QuantEUEquality euEq = new QuantEUEquality(term, lhsEU, rhsEU);
			mQuantLits.put(term, euEq);
			return euEq;
		}
		throw new UnsupportedOperationException(
				(positive ? "Term " : "Negated term ") + term + " not in almost uninterpreted fragment!");
	}

	/**
	 * Get a quantified inequality literal for a term - in case it is supported.
	 * 
	 * We support the following inequality literals: (i) (EUTerm <= 0) (and negated) (ii) ~(TermVariable <= GroundTerm)
	 * (iii) ~(GroundTerm <= TermVariable) (iv) ~(TermVariable <= TermVariable). Note that this will return a
	 * <em>negated</em> literal (not (x<=t)) in the latter three cases if positive==true!
	 * 
	 * @param term
	 *            the term for the underlying inequality <em>atom</em> "term <= 0".
	 * @param positive
	 *            flag that indicates if the term appears positively or negated in the clause. This is required to
	 *            determine if the literal is supported.
	 * @param source
	 *            the source partition of the term.
	 * @param lhs
	 *            the left hand side in "term <= 0"
	 * 
	 * @return a QuantLiteral if the literal is supported.
	 */
	public QuantLiteral getQuantInequality(Term term, boolean positive, SourceAnnotation source, Term lhs) {
		final QuantLiteral lit = mQuantLits.get(term);
		if (lit != null) {
			if (positive && lit.isSupported()) {
				return lit;
			} else if (!positive && lit.negate().isSupported()) {
				return lit;
			} else {
				throw new UnsupportedOperationException(
						(positive ? "Term " : "Negated term ") + term + " not in almost uninterpreted fragment!");
			}
		}

		final SMTAffineTerm linTerm = SMTAffineTerm.create(lhs);
		Map<Term, Rational> summands = linTerm.getSummands();
		final Rational constant = linTerm.getConstant();

		// Check for free variables that do not appear in EUTerms.
		TermVariable lower = null; // the lower variable in x<t
		TermVariable upper = null;
		final Iterator<Term> it = summands.keySet().iterator();
		while (it.hasNext()) {
			Term summand = it.next();
			if (summand instanceof TermVariable) {
				if (positive == summands.get(summand).isNegative()) {
					// the variable has a lower bound
					if (upper != null) {
						throw new UnsupportedOperationException(
								"Term " + term + " not in almost uninterpreted fragment!");
					}
					upper = (TermVariable) summand;
					it.remove();
				} else {
					// the variable has an upper bound
					if (lower != null) {
						throw new UnsupportedOperationException(
								"Term " + term + " not in almost uninterpreted fragment!");
					}
					lower = (TermVariable) summand;
					it.remove();
				}
			}
		}

		// If the literal is a QuantEUBoundConstraint, keep the given form.
		if (lower == null && upper == null) {
			final EUTerm euAffine = mEUTermManager.getEUTerm(lhs, source);
			QuantEUBoundConstraint euConstr = new QuantEUBoundConstraint(term, euAffine);
			mQuantLits.put(term, euConstr);
			return euConstr;
		}

		// Else, bring the literals into the form ~(x<=t), ~(t<=x), ~(x<=y)
		if (positive) {
			// First step of rewriting positive (x-t<=0) into ~(t+1<=x) for x integer
			if (term.getSort().getName().equals("Int")) {
				constant.add(Rational.MONE);
			} else {
				throw new UnsupportedOperationException("Term " + term + " not in almost uninterpreted fragment!");
			}
		}

		if (lower != null && upper != null) {
			// Two variables can only be compared with each other.
			if (!it.hasNext() && constant == Rational.ZERO) {
				QuantVarConstraint varConstr = new QuantVarConstraint(term, lower, upper);
				if (positive) {
					// Second step of converting positive literals into negated ones.
					// This can happen for positive (x+1<=y) (---> converted into ~(y<=x))
					varConstr.negate();
				}
				mQuantLits.put(term, varConstr);
				return varConstr;
			}
		} else {
			final boolean hasLowerBound = (upper != null);
			final TermVariable var = hasLowerBound ? upper : lower;
			SMTAffineTerm boundAffine = new SMTAffineTerm(summands, constant);
			// Isolate variable by bringing bound to the other side
			if (positive != hasLowerBound) { // for rewriting ~(x-t<=0) into ~(x<=t) and (x-t<=0) into ~(t+1<=x)
				boundAffine.negate();
			}
			Term bound = boundAffine.toTerm(mClausifier.getTermCompiler(), term.getSort());
			// The variable can only be bound by ground terms.
			if (bound.getFreeVars().length == 0) {
				final EUTerm boundTerm = mEUTermManager.getEUTerm(bound, source);
				QuantVarConstraint varConstr = new QuantVarConstraint(term, var, hasLowerBound, (GroundTerm) boundTerm);
				if (positive) {
					// Second step of converting positive literals into negated ones.
					// This can happen for positive (x+1<=y) (---> converted into ~(y<=x))
					varConstr.negate();
				}
				mQuantLits.put(term, varConstr);
				return varConstr;
			}
		}
		throw new UnsupportedOperationException(
				(positive ? "Term " : "Negated term ") + term + " not in almost uninterpreted fragment!");
	}

	public QuantLiteral getQuantNamedAtom(Term term) {
		return new QuantNamedAtom(term);
	}

	/**
	 * Add a QuantClause for a given set of literals and quantified literals.
	 *
	 * This should be called after applying DER.
	 *
	 * @param lits
	 *            ground literals in the new clause.
	 * @param quantLits
	 *            literals in the new clause containing at least one free variable.
	 * @param hook
	 * @param proof
	 */
	public void addQuantClause(final Literal[] lits, final QuantLiteral[] quantLits, SourceAnnotation source) {
		if (quantLits.length == 0) {
			throw new IllegalArgumentException("Cannot add clause to QuantifierTheory: No quantified literal!");
		}
		for (QuantLiteral lit : quantLits) {
			if (!lit.mIsSupported) {
				throw new IllegalArgumentException(
						"Cannot add clause to QuantifierTheory: Contains unsupported literals!");
			} else if (lit.isNegated() && lit.getAtom() instanceof QuantVarEquality) {
				throw new IllegalArgumentException(
						"Cannot add clause to QuantifierTheory: Disequalities on variables must be eliminated by DER before!");
			}
		}
		final QuantClause clause = new QuantClause(lits, quantLits, this, source);
		mQuantClauses.add(clause);
	}

	/**
	 * Get all EUTerms that are sub-terms of a given term.
	 * 
	 * @param euTerm
	 *            the EUTerm we want to get the subterms for.
	 * @return a set of EUTerms containing all sub-EUTerms of a term, including the term itself.
	 */
	public Set<EUTerm> getSubEUTerms(EUTerm euTerm) {
		return mEUTermManager.getSubEUTerms(euTerm);
	}

	public Clausifier getClausifier() {
		return mClausifier;
	}

	public CClosure getCClosure() {
		return mCClosure;
	}

	public LinArSolve getLinAr() {
		return mLinArSolve;
	}

	public EUTermManager getEUTermManager() {
		return mEUTermManager;
	}

	public InstantiationManager getInstantiator() {
		return mInstantiationManager;
	}
	
	public ScopedHashSet<QuantClause> getQuantClauses() {
		return mQuantClauses;
	}

	private Clause checkPropClausesForConflict() {
		final Iterator<List<Literal>> it = mPropClauses.iterator();
		while (it.hasNext()) {
			final List<Literal> clauseLits = it.next();
			boolean isConflict = true;
			for (final Literal lit : clauseLits) {
				if (lit.getAtom().getDecideStatus() != lit.negate()) {
					isConflict = false;
				}
			}
			if (isConflict) {
				it.remove();
				return new Clause(clauseLits.toArray(new Literal[clauseLits.size()]));
			}
		}
		return null;
	}
}
