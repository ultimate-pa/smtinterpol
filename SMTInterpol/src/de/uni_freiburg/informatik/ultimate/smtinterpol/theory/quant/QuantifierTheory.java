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
import java.util.Collection;
import java.util.HashMap;
import java.util.Iterator;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
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
import de.uni_freiburg.informatik.ultimate.util.datastructures.ScopedArrayList;

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
	private final ScopedArrayList<QuantClause> mQuantClauses;

	/**
	 * Literals (not atoms!) mapped to potential conflict and unit clauses that they are contained in. At creation, the
	 * clauses would have been conflicts or unit clauses if the corresponding theories had already known the contained
	 * literals. In the next checkpoint, false literals should have been propagated by the other theories, but we might
	 * still have one undefined literal (and is a unit clause). If not, it is a conflict then.
	 */
	private final Map<Literal, Set<InstClause>> mPotentialConflictAndUnitClauses;

	// Statistics
	private long mConflictCount, mPropCount, mFinalCount;

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
		mQuantClauses = new ScopedArrayList<QuantClause>();

		mPotentialConflictAndUnitClauses = new LinkedHashMap<>();

		mConflictCount = mPropCount = mFinalCount = 0;
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
		if (mPotentialConflictAndUnitClauses.containsKey(literal)) {
			mPotentialConflictAndUnitClauses.remove(literal);
		}
		final Iterator<Literal> litIt = mPotentialConflictAndUnitClauses.keySet().iterator();
		while (litIt.hasNext()) {
			final Literal keyLit = litIt.next();
			final Iterator<InstClause> clauseIt = mPotentialConflictAndUnitClauses.get(keyLit).iterator();
			while (clauseIt.hasNext()) {
				final InstClause clause = clauseIt.next();
				if (clause.mLits.contains(literal.negate())) {
					clauseIt.remove();
				}
			}
			if (mPotentialConflictAndUnitClauses.get(keyLit).isEmpty()) {
				litIt.remove();
			}
		}
		if (mPotentialConflictAndUnitClauses.containsKey(literal.negate())) {
			for (final InstClause instClause : mPotentialConflictAndUnitClauses.get(literal.negate())) {
				assert instClause.mNumUndefLits > 0;
				instClause.mNumUndefLits -= 1;
				if (instClause.isConflict()) {
					mConflictCount++;
					return new Clause(instClause.mLits.toArray(new Literal[instClause.mLits.size()]));
				}
			}
		}
		return null;
	}

	@Override
	public void backtrackLiteral(Literal literal) {
		for (final QuantClause clause : mQuantClauses) {
			if (Arrays.asList(clause.getGroundLits()).contains(literal)) {
				clause.setState(EprClauseState.Normal);
			}
		}
		for (final Literal lit : mPotentialConflictAndUnitClauses.keySet()) {
			for (final InstClause clause : mPotentialConflictAndUnitClauses.get(lit)) {
				if (clause.mLits.contains(literal.negate())) {
					clause.mNumUndefLits += 1;
				}
			}
		}
	}

	@Override
	public Clause checkpoint() {
		for (final QuantClause clause : mQuantClauses) {
			clause.updateInterestingTermsAllVars();
		}
		final Clause conflict =
				addPotentialConflictAndUnitClauses(mInstantiationManager.findConflictAndUnitInstances());
		if (conflict != null) {
			mConflictCount++;
		}
		return conflict;
	}

	@Override
	public Clause computeConflictClause() {
		mFinalCount++;
		Clause conflict = checkpoint();
		if (conflict != null) {
			return conflict;
		}
		assert mPotentialConflictAndUnitClauses.isEmpty();
		conflict = mInstantiationManager.instantiateAll();
		if (conflict != null) {
			mConflictCount++;
			return conflict;
		}
		return null;
	}

	@Override
	public Literal getPropagatedLiteral() {
		for (final Literal lit : mPotentialConflictAndUnitClauses.keySet()) {
			for (final InstClause clause : mPotentialConflictAndUnitClauses.get(lit)) {
				if (clause.isUnit()) {
					lit.getAtom().mExplanation = new Clause(clause.mLits.toArray(new Literal[clause.mLits.size()]));
					mPropCount++;
					if (mLogger.isDebugEnabled()) {
						mLogger.debug("Quant Prop: " + lit + " reason: " + lit.getAtom().mExplanation);
					}
					return lit;
				}
			}
		}
		return null;
	}

	@Override
	public Clause getUnitClause(Literal literal) {
		assert false : "Should never be called.";
		// assert mPotentialConflictAndUnitClauses.containsKey(literal);
//		Clause unitClause = null;
		// for (final InstClause clause : mPotentialConflictAndUnitClauses.get(literal)) {
//			if (clause.isUnit()) {
//				unitClause = new Clause(clause.mLits.toArray(new Literal[clause.mLits.size()]));
		// mPotentialConflictAndUnitClauses.get(literal).remove(clause);
		// if (mPotentialConflictAndUnitClauses.get(literal).isEmpty()) {
		// mPotentialConflictAndUnitClauses.remove(literal);
//				}
//				return unitClause;
//			}
//		}
		return null;
	}

	@Override
	public Literal getSuggestion() {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public void printStatistics(LogProxy logger) {
		logger.info("Quant: Conflicts: " + mConflictCount + " Props: " + mPropCount + " Final Checks: " + mFinalCount);

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
	public QuantLiteral getQuantEquality(final Term term, final boolean positive, final SourceAnnotation source,
			final Term lhs, final Term rhs) {
		final QuantLiteral atom = mQuantLits.get(term);
		if (atom != null) {
			if (positive && atom.isSupported()) {
				return atom;
			} else if (!positive && atom.negate().isSupported()) {
				return atom;
			} else {
				throw new UnsupportedOperationException(
						(positive ? term : "(not " + term + ")") + " not in almost uninterpreted fragment!");
			}
		}

		if (!lhs.getSort().isNumericSort()) {
			final TermVariable leftVar = lhs instanceof TermVariable ? (TermVariable) lhs : null;
			final TermVariable rightVar = rhs instanceof TermVariable ? (TermVariable) rhs : null;
			if (leftVar == null && rightVar == null) {
				final EUTerm lhsEU = mEUTermManager.getEUTerm(lhs, source);
				final EUTerm rhsEU = mEUTermManager.getEUTerm(rhs, source);
				QuantEUEquality euEq = new QuantEUEquality(term, lhsEU, rhsEU);
				mQuantLits.put(term, euEq);
				return euEq;
			}
			if (!positive) {
				if (leftVar != null && rightVar != null) {
					final QuantVarEquality varEq = new QuantVarEquality(term, leftVar, rightVar);
					mQuantLits.put(term, varEq);
					return varEq;
				} else {
					final TermVariable onlyVar = leftVar != null ? leftVar : rightVar;
					final EUTerm euTerm = leftVar != null ? mEUTermManager.getEUTerm(rhs, source)
							: mEUTermManager.getEUTerm(lhs, source);
					if (euTerm instanceof GroundTerm) {
						QuantVarEquality euEq = new QuantVarEquality(term, onlyVar, (GroundTerm) euTerm);
						mQuantLits.put(term, euEq);
						return euEq;
					}
				}
			}
			throw new UnsupportedOperationException(
					(positive ? term : "(not " + term + ")") + " not in almost uninterpreted fragment!");
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
						throw new UnsupportedOperationException(term + " not in almost uninterpreted fragment!");
					}
					rightVar = (TermVariable) summand;
					it.remove();
				} else {
					if (leftVar != null) {
						throw new UnsupportedOperationException(term + " not in almost uninterpreted fragment!");
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
			if (positive && !lhs.getSort().getName().equals("Int")) { // We support (var = ground) only for integers.
				throw new UnsupportedOperationException(term + " not in almost uninterpreted fragment!");
			}
			// We will do destructive equality reasoning later if !positive.
			SMTAffineTerm remainderAffine = new SMTAffineTerm(summands, constant);
			if (leftVar != null) {
				remainderAffine.negate();
			}
			Term remainder = remainderAffine.toTerm(mClausifier.getTermCompiler(), lhs.getSort());
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
				(positive ? term : "(not " + term + ")") + " not in almost uninterpreted fragment!");
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
						(positive ? term : "(not " + term + ")") + " not in almost uninterpreted fragment!");
			}
		}

		final SMTAffineTerm linTerm = SMTAffineTerm.create(lhs);
		Map<Term, Rational> allSummands = linTerm.getSummands();
		final Rational constant = linTerm.getConstant();

		// Check for free variables that do not appear in EUTerms.
		TermVariable lower = null; // the lower variable in x<=t
		TermVariable upper = null;
		final Map<Term, Rational> nonVarSummands = new LinkedHashMap<>();
		for (final Term summand : allSummands.keySet()) {
			if (summand instanceof TermVariable) {
				if (positive != allSummands.get(summand).isNegative()) {
					// the variable has a lower bound
					if (upper != null) {
						throw new UnsupportedOperationException(term + " not in almost uninterpreted fragment!");
					}
					upper = (TermVariable) summand;
				} else {
					// the variable has an upper bound
					if (lower != null) {
						throw new UnsupportedOperationException(term + " not in almost uninterpreted fragment!");
					}
					lower = (TermVariable) summand;
				}
			} else {
				nonVarSummands.put(summand, allSummands.get(summand));
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
			if (lhs.getSort().getName().equals("Int")) {
				constant.add(Rational.MONE);
			} else {
				throw new UnsupportedOperationException(term + " not in almost uninterpreted fragment!");
			}
		}

		if (lower != null && upper != null) {
			// Two variables can only be compared with each other.
			if (nonVarSummands.isEmpty() && constant == Rational.ZERO) {
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
			SMTAffineTerm boundAffine = new SMTAffineTerm(nonVarSummands, constant);
			// Isolate variable by bringing bound to the other side
			if (positive == hasLowerBound) { // for rewriting ~(x-t<=0) into ~(x<=t) and (x-t<=0) into ~(t+1<=x)
				boundAffine.negate();
			}
			Term bound = boundAffine.toTerm(mClausifier.getTermCompiler(), lhs.getSort());
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
				(positive ? term : "(not " + term + ")") + " not in almost uninterpreted fragment!");
	}

	/**
	 * Add a QuantClause for a given set of literals and quantified literals.
	 *
	 * This method performs Destructive Equality Reasoning, and if the clause becomes ground, it returns the literals
	 * instead of adding a new QuantClause (Idea from Alex' EPR implementation).
	 *
	 * @param groundLits
	 *            ground literals in the new clause.
	 * @param quantLits
	 *            literals in the new clause containing at least one free variable.
	 * @param source
	 *            the source of the clause
	 * @return the ground literals if the clause became ground after DER; null otherwise.
	 */
	public Literal[] addQuantClause(final Literal[] groundLits, final QuantLiteral[] quantLits,
			SourceAnnotation source) {
		if (quantLits.length == 0) {
			throw new IllegalArgumentException("Cannot add clause to QuantifierTheory: No quantified literal!");
		}

		final DestructiveEqualityReasoning der = new DestructiveEqualityReasoning(this, groundLits, quantLits, source);
		final Literal[] groundLitsAfterDER;
		final QuantLiteral[] quantLitsAfterDER;
		if (der.applyDestructiveEqualityReasoning()) { // DER changed something
			if (der.getState() == EprClauseState.Fulfilled) {
				return null; // Don't add trivially true clauses. // TODO: What about proof production?
			}
			groundLitsAfterDER = der.getGroundLitsAfterDER();
			quantLitsAfterDER = der.getQuantLitsAfterDER();
			if (quantLitsAfterDER.length == 0) {
				if (mLogger.isDebugEnabled()) {
					mLogger.debug("Quant: DER returned ground clause.");
				}
				if (groundLitsAfterDER.length == 0) {
					assert der.getState() == EprClauseState.Conflict;
				}
				return groundLitsAfterDER; // Can have length 0; corresponds to false clause.
			}
		} else {
			groundLitsAfterDER = groundLits;
			quantLitsAfterDER = quantLits;
		}

		for (QuantLiteral lit : quantLitsAfterDER) {
			if (!lit.mIsSupported) {
				throw new UnsupportedOperationException(
						"Cannot add clause to QuantifierTheory: Contains unsupported literal " + lit.toString());
			} else if (lit.isNegated() && lit.getAtom() instanceof QuantVarEquality) {
				throw new UnsupportedOperationException(
						"Cannot add clause to QuantifierTheory: Disequality on variables " + lit.toString()
								+ " must be eliminated by DER before!");
			}
		}
		final QuantClause clause = new QuantClause(groundLitsAfterDER, quantLitsAfterDER, this, source);
		mQuantClauses.add(clause);
		if (mLogger.isDebugEnabled()) {
			mLogger.debug("Quant: Added clause: " + clause);
		}
		return null;
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

	public Collection<QuantClause> getQuantClauses() {
		return mQuantClauses;
	}

	public Map<Term, QuantLiteral> getQuantLits() {
		return mQuantLits;
	}

	/**
	 * Add potential conflict and unit clauses to the map from undefined literals to clauses. We stop as soon as we find
	 * an actual conflict.
	 * 
	 * TODO How can we handle actual conflicts in a better way?
	 * 
	 * @param instances
	 *            a set of potential conflict and unit clauses
	 * @return a conflict
	 */
	private Clause addPotentialConflictAndUnitClauses(final Set<List<Literal>> instances) {
		if (instances == null) {
			return null;
		}
		boolean isConflict = true;
		for (List<Literal> clause : instances) {
			boolean isTrueInst = false;
			int numUndef = 0;
			// Count the number of undefined literals
			for (final Literal lit : clause) {
				if (lit.getAtom().getDecideStatus() == lit) {
					isTrueInst = true;
					continue;
				}
				if (lit.getAtom().getDecideStatus() == null) {
					numUndef++;
				}
			}
			if (isTrueInst) {
				continue; // Don't add true instances.
				// TODO They should be detected during literal evaluation, but it doesn't work as expected, see below.
			}
			final InstClause instClause = new InstClause(clause, numUndef);
			for (final Literal lit : clause) {
				// assert lit.getAtom().getDecideStatus() != lit;
				// TODO It happens that the assertion is violated. Not sure whether evaluation of literals (as terms)
				// works correctly, even with CC.
				if (lit.getAtom().getDecideStatus() == null) {
					isConflict = false;
					if (!mPotentialConflictAndUnitClauses.containsKey(lit)) {
						mPotentialConflictAndUnitClauses.put(lit, new LinkedHashSet<>());
					}
					mPotentialConflictAndUnitClauses.get(lit).add(instClause);
				}
			}
			if (isConflict) {
				return new Clause(clause.toArray(new Literal[clause.size()]));
			}
		}
		return null;
	}

	private class InstClause {
		private final List<Literal> mLits;
		protected int mNumUndefLits;

		InstClause(final List<Literal> lits, final int numUndefLits) {
			mLits = lits;
			mNumUndefLits = numUndefLits;
		}

		boolean isConflict() {
			return mNumUndefLits == 0;
		}

		boolean isUnit() {
			return mNumUndefLits == 1;
		}

		@Override
		public boolean equals(final Object other) {
			if (other instanceof InstClause) {
				if (mLits == ((InstClause) other).mLits) {
					return true;
				}
			}
			return false;
		}
	}
}
