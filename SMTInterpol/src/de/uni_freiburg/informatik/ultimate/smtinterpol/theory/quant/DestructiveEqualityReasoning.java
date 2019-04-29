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

import java.util.Arrays;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.logic.FunctionSymbol;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.smtinterpol.convert.Clausifier;
import de.uni_freiburg.informatik.ultimate.smtinterpol.convert.EqualityProxy;
import de.uni_freiburg.informatik.ultimate.smtinterpol.convert.SMTAffineTerm;
import de.uni_freiburg.informatik.ultimate.smtinterpol.convert.SharedTerm;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.DPLLAtom.NegLiteral;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.Literal;
import de.uni_freiburg.informatik.ultimate.smtinterpol.proof.SourceAnnotation;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.clauses.EprClauseState;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.linar.MutableAffineTerm;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.quant.QuantLiteral.NegQuantLiteral;

/**
 * Apply destructive equality reasoning to a quantified clause.
 * <p>
 * This is, if a quantified clause contains a literal (x != t), every occurrence of x is substituted by t, and the
 * literal is dropped.
 * 
 * @author Tanja Schindler
 *
 */
class DestructiveEqualityReasoning {

	private final QuantifierTheory mQuantTheory;
	private final Clausifier mClausifier;

	private final Literal[] mGroundLits;
	private final QuantLiteral[] mQuantLits;
	private final SourceAnnotation mSource;

	private Map<TermVariable, Term> mSigma;
	private boolean mIsChanged;
	private EprClauseState mState;
	private Set<Literal> mGroundLitsAfterDER;
	private Set<QuantLiteral> mQuantLitsAfterDER;

	DestructiveEqualityReasoning(QuantifierTheory quantTheory, Literal[] groundLits, QuantLiteral[] quantLits,
			SourceAnnotation source) {
		mQuantTheory = quantTheory;
		mClausifier = quantTheory.getClausifier();

		mGroundLits = groundLits;
		mQuantLits = quantLits;
		mSource = source;

		mSigma = new LinkedHashMap<>();
		mIsChanged = false;
		mState = EprClauseState.Normal;
	}

	/**
	 * Apply destructive equality reasoning.
	 * <p>
	 * If something has changed, the result can be obtained by calling getGroundLitsAfterDER() and
	 * getQuantLitsAfterDER(), respectively.
	 * 
	 * @return true if DER changed something, i.e., a variable has been removed; false otherwise.
	 */
	boolean applyDestructiveEqualityReasoning() {
		collectSubstitution();
		if (!mSigma.isEmpty()) {
			applySubstitution();
			mIsChanged = true;
		}
		return mIsChanged;
	}

	/**
	 * Return the state of the clause.
	 * 
	 * @return Fullfilled, if the clause is trivially true; Conflict, if the clause is trivially false; Normal
	 *         otherwise.
	 */
	public EprClauseState getState() {
		return mState;
	}

	/**
	 * Get the ground literals after destructive equality reasoning was performed.
	 * 
	 * @return an array containing the ground literals after DER. Can have length 0.
	 */
	Literal[] getGroundLitsAfterDER() {
		assert mState != EprClauseState.Fulfilled : "Should never be called on trivially true clauses!";
		if (!mIsChanged) {
			return mGroundLits;
		}
		return mGroundLitsAfterDER.toArray(new Literal[mGroundLitsAfterDER.size()]);
	}

	/**
	 * Get the quantified literals after destructive equality reasoning was performed.
	 * 
	 * @return an array containing the quantified literals after DER. Can have length 0.
	 */
	QuantLiteral[] getQuantLitsAfterDER() {
		assert mState != EprClauseState.Fulfilled : "Should never be called on trivially true clauses!";
		if (!mIsChanged) {
			return mQuantLits;
		}
		return mQuantLitsAfterDER.toArray(new QuantLiteral[mQuantLitsAfterDER.size()]);
	}

	/**
	 * Collect the substitution sigma.
	 * <p>
	 * Step 1: Go through all literals. For variables x,y,z, and a term t (can be a variable):<br>
	 * (i) For a literal (x != t), add {z -> t} to sigma if sigma*(x) = z.<br>
	 * (ii) For a literal (x != y), add {z -> x} to sigma if sigma*(y) = z.<br>
	 * First check (i) and only if it does not apply, check (ii).
	 * <p>
	 * Step 2: sigma := sigma*.
	 */
	private void collectSubstitution() {
		// Step 1:
		for (QuantLiteral qLit : mQuantLits) {
			if (qLit instanceof NegQuantLiteral) {
				final QuantLiteral atom = qLit.mAtom;
				if (atom instanceof QuantVarEquality) {
					final QuantVarEquality varEq = (QuantVarEquality) atom;
					final TermVariable var = varEq.getLeftVar();
					final TermVariable varRep = findVarRep(var);
					if (varRep != null) { // Case (i): No ground substitution for var so far.
						final Term subs = varEq.isBothVar() ? varEq.getRightVar() : varEq.getGroundTerm().getTerm();
						if (varRep != subs) { // Don't add a substitution x->x
							mSigma.put(varRep, subs);
						}
					} else {
						if (varEq.isBothVar()) {
							final TermVariable otherVar = varEq.getRightVar();
							final TermVariable otherVarRep = findVarRep(otherVar);
							if (otherVarRep != null) { // Case (ii): No ground substitution for the other var so far.
								if (otherVarRep != var) { // Don't add a substitution x->x
									mSigma.put(otherVarRep, var);
								}
							}
						}
					}
				}
			}
		}
		// Step 2:
		if (!mSigma.isEmpty()) {
			final Set<TermVariable> visited = new HashSet<>();
			for (final TermVariable var : mSigma.keySet()) {
				if (!visited.contains(var)) {
					final Set<TermVariable> varsWithSameSubs = new HashSet<>();
					Term subs = var;
					while (subs instanceof TermVariable && !visited.contains(subs)) {
						visited.add((TermVariable) subs);
						varsWithSameSubs.add((TermVariable) subs);
						if (mSigma.containsKey(subs)) {
							subs = mSigma.get(subs);
						}
					}
					for (final TermVariable equiVar : varsWithSameSubs) {
						if (equiVar == subs) { // Don't use a substitution x->x.
							mSigma.remove(equiVar);
						} else {
							mSigma.put(equiVar, subs);
						}
					}
				}
			}
		}
	}

	/**
	 * For a variable x, find sigma*(x).
	 * 
	 * We define sigma(x) = x if x has no substitution so far.
	 * 
	 * @return The TermVariable sigma*(x), if it exists, null if sigma*(x) is a ground Term.
	 */
	private TermVariable findVarRep(TermVariable var) {
		TermVariable nextVarRep = var;
		while (true) {
			if (mSigma.containsKey(nextVarRep)) {
				final Term subs = mSigma.get(nextVarRep);
				if (subs instanceof TermVariable) {
					nextVarRep = (TermVariable) subs;
				} else {
					return null;
				}
			} else {
				return nextVarRep;
			}
		}
	}

	/**
	 * Apply the substitution sigma collected from the disequalities in this clause, in order to get rid of some
	 * variables.
	 */
	private void applySubstitution() {
		assert !mSigma.isEmpty();
		mGroundLitsAfterDER = new LinkedHashSet<>();
		mQuantLitsAfterDER = new LinkedHashSet<>();
		mGroundLitsAfterDER.addAll(Arrays.asList(mGroundLits));
		for (final QuantLiteral qLit : mQuantLits) {
			final boolean isPos = !(qLit instanceof NegQuantLiteral);
			final QuantLiteral qAtom = qLit.getAtom();
			if (qAtom instanceof QuantVarEquality) { // Possible results: (var=var),(var=ground),(ground=ground).
				final QuantVarEquality varEq = (QuantVarEquality) qAtom;
				final TermVariable leftVar = varEq.getLeftVar();
				final TermVariable rightVar = varEq.isBothVar() ? varEq.getRightVar() : null;
				Term newLeft = mSigma.containsKey(leftVar) ? mSigma.get(leftVar) : leftVar;
				Term newRight = rightVar == null ? varEq.getGroundTerm().getTerm()
						: mSigma.containsKey(rightVar) ? mSigma.get(rightVar) : rightVar;
				if (leftVar == newLeft && rightVar == newRight) { // Nothing has changed.
					mState = addNewQuantLit(isPos, qAtom);
				} else if (newLeft == newRight) {
					if (isPos) { // Mark clauses that become trivially true after DER.
						mState = EprClauseState.Fulfilled;
					} // Don't add a trivially false literal.
				} else {
					if (!(newLeft instanceof TermVariable) && !(newRight instanceof TermVariable)) { // Result ground.
						final SharedTerm leftShared = mClausifier.getSharedTerm(newLeft, mSource);
						final SharedTerm rightShared = mClausifier.getSharedTerm(newRight, mSource);
						final EqualityProxy eqProx = leftShared.createEquality(rightShared);
						if (isPos && eqProx == EqualityProxy.getTrueProxy()
								|| !isPos && eqProx == EqualityProxy.getFalseProxy()) {
							// Mark clauses that become trivially true after DER.
							mState = EprClauseState.Fulfilled;
						} else if ((!isPos && eqProx == EqualityProxy.getTrueProxy())
								|| (isPos && eqProx == EqualityProxy.getFalseProxy())) {
							// Don't add a trivially false literal.
						} else {
							final Literal newAtom = eqProx.getLiteral(mSource);
							mState = addNewGroundLit(isPos, newAtom);
						}
					} else { // Result contains variables.
						if (!(newLeft instanceof TermVariable) && newRight instanceof TermVariable) {
							// Normalize QuantVarEquality.
							final Term temp = newLeft;
							newLeft = newRight;
							newRight = temp;
						}
						final Term newAtomTerm = mClausifier.getTheory().term("=", newLeft, newRight);
						final QuantLiteral newQuantAtom;
						if (mQuantTheory.getQuantLits().containsKey(newAtomTerm)) {
							// The QuantLiteral already exists.
							newQuantAtom = mQuantTheory.getQuantLits().get(newAtomTerm);
						} else if (newRight instanceof TermVariable) {
							assert !isPos;
							newQuantAtom =
									new QuantVarEquality(newAtomTerm, (TermVariable) newLeft, (TermVariable) newRight);
						} else {
							final EUTerm rightGround = mQuantTheory.getEUTermManager().getEUTerm(newRight, mSource);
							assert rightGround instanceof GroundTerm;
							newQuantAtom =
									new QuantVarEquality(newAtomTerm, (TermVariable) newLeft, (GroundTerm) rightGround);
						}
						mState = addNewQuantLit(isPos, newQuantAtom);
					}
				}
			} else if (qAtom instanceof QuantVarConstraint) {
				assert !isPos;
				// Possible results: (var<var),(var<ground),(ground<var),(ground<ground)
				final QuantVarConstraint varConstr = (QuantVarConstraint) qAtom;
				final TermVariable lowerVar = varConstr.isUpperBound() ? varConstr.getLowerVar() : null;
				final TermVariable upperVar = varConstr.isLowerBound() ? varConstr.getUpperVar() : null;
				Term newLower = lowerVar == null ? varConstr.getGroundBound().getTerm()
						: mSigma.containsKey(lowerVar) ? mSigma.get(lowerVar) : lowerVar;
				Term newUpper = upperVar == null ? varConstr.getGroundBound().getTerm()
						: mSigma.containsKey(upperVar) ? mSigma.get(upperVar) : upperVar;
				if (lowerVar == newLower && upperVar == newUpper) { // Nothing has changed.
					mState = addNewQuantLit(isPos, qAtom);
				} else if (newLower == newUpper) {
					// Don't add a trivially false literal.
				} else {
					if (!(newLower instanceof TermVariable) && !(newUpper instanceof TermVariable)) { // Result ground.
						final SMTAffineTerm sum = new SMTAffineTerm(newLower);
						sum.add(Rational.MONE, new SMTAffineTerm(newUpper));
						if (sum.isConstant()) {
							if (sum.getConstant().equals(Rational.ZERO) || sum.getConstant().isNegative()) {
								// Don't add a trivially false literal.
							} else { // Mark clauses that become trivially true after DER.
								mState = EprClauseState.Fulfilled;
							}
						} else {
							final MutableAffineTerm at = mClausifier.createMutableAffinTerm(sum, mSource);
							final Literal newAtom = mQuantTheory.mLinArSolve.generateConstraint(at, false);
							mState = addNewGroundLit(isPos, newAtom);
						}
					} else { // Result contains variables.
						final Term newAtomTerm = null;
						final QuantLiteral newQuantAtom;
						if (mQuantTheory.getQuantLits().containsKey(newAtomTerm)) {
							// The QuantLiteral already exists.
							newQuantAtom = mQuantTheory.getQuantLits().get(newAtomTerm);
						} else if (newLower instanceof TermVariable) {
							if (newUpper instanceof TermVariable) {
								newQuantAtom = new QuantVarConstraint(newAtomTerm, (TermVariable) newLower,
										(TermVariable) newUpper);
							} else {
								final EUTerm newGroundBound =
										mQuantTheory.getEUTermManager().getEUTerm(newUpper, mSource);
								assert newGroundBound instanceof GroundTerm;
								newQuantAtom = new QuantVarConstraint(newAtomTerm, (TermVariable) newLower, false,
										(GroundTerm) newGroundBound);
							}
						} else {
							assert newUpper instanceof TermVariable;
							final EUTerm newGroundBound = mQuantTheory.getEUTermManager().getEUTerm(newLower, mSource);
							assert newGroundBound instanceof GroundTerm;
							newQuantAtom = new QuantVarConstraint(newAtomTerm, (TermVariable) newUpper, true,
									(GroundTerm) newGroundBound);
						}
						mState = addNewQuantLit(isPos, newQuantAtom);
					}
				}
			} else if (qAtom instanceof QuantEUEquality) {
				// Possible results: (ground=ground), (eu=eu) with at least one variable
				final QuantEUEquality euEq = (QuantEUEquality) qAtom;
				final EUTerm newLeft = substituteInEUTerm(euEq.getLhs());
				final EUTerm newRight = substituteInEUTerm(euEq.getRhs());
				if (newLeft == euEq.getLhs() && newRight == euEq.getRhs()) { // Nothing has changed.
					mState = addNewQuantLit(isPos, qAtom);
				} else if (newLeft == newRight) {
					if (isPos) { // Mark clauses that become trivially true after DER.
						mState = EprClauseState.Fulfilled;
					} // Don't add trivially false literals.
				} else if (newLeft instanceof GroundTerm && newRight instanceof GroundTerm) {
					final SharedTerm leftShared = ((GroundTerm) newLeft).getSharedTerm();
					final SharedTerm rightShared = ((GroundTerm) newRight).getSharedTerm();
					final EqualityProxy eqProx = leftShared.createEquality(rightShared);
					if (isPos && eqProx == EqualityProxy.getTrueProxy()
							|| !isPos && eqProx == EqualityProxy.getFalseProxy()) {
						// Mark clauses that become trivially true after DER.
						mState = EprClauseState.Fulfilled;
					} else if ((!isPos && eqProx == EqualityProxy.getTrueProxy())
							|| (isPos && eqProx == EqualityProxy.getFalseProxy())) {
						// Don't add a trivially false literal.
					} else {
						final Literal newAtom = eqProx.getLiteral(mSource);
						mState = addNewGroundLit(isPos, newAtom);
					}
				} else {
					final Term newTerm = mClausifier.getTheory().term("=", newLeft.getTerm(), newRight.getTerm());
					final QuantLiteral newQuantAtom;
					if (mQuantTheory.getQuantLits().containsKey(newTerm)) {
						newQuantAtom = mQuantTheory.getQuantLits().get(newTerm);
					} else {
						newQuantAtom = new QuantEUEquality(newTerm, newLeft, newRight);
					}
					mState = addNewQuantLit(isPos, newQuantAtom);
				}
			} else {
				assert qAtom instanceof QuantEUBoundConstraint; // Possible results: (ground<=0),(quantaff<=0)
				final QuantEUBoundConstraint euConst = (QuantEUBoundConstraint) qAtom;
				final QuantAffineTerm quantAff = euConst.getAffineTerm();
				final EUTerm newLhs = substituteInEUTerm(quantAff);
				if (newLhs == quantAff) { // Nothing has changed.
					mState = addNewQuantLit(isPos, qAtom);
				} else if (newLhs instanceof GroundTerm) { // Result ground.
					final SMTAffineTerm sum = new SMTAffineTerm(newLhs.getTerm());
					if (sum.isConstant()) {
						if ((sum.getConstant().equals(Rational.ZERO) || sum.getConstant().isNegative()) == isPos) {
							// Mark clauses that become trivially true after DER.
							mState = EprClauseState.Fulfilled;
							return;
						} // Don't add a trivially false literal.
					} else {
						final MutableAffineTerm at = mClausifier.createMutableAffinTerm(sum, mSource);
						final Literal newAtom = mQuantTheory.mLinArSolve.generateConstraint(at, false);
						mState = addNewGroundLit(isPos, newAtom);
					}
				} else {
					final Term newTerm = mClausifier.getTheory().term("<=", newLhs.getTerm(),
							Rational.ZERO.toTerm(newLhs.getSort()));
					final QuantLiteral newQuantAtom;
					if (mQuantTheory.getQuantLits().containsKey(newTerm)) {
						newQuantAtom = mQuantTheory.getQuantLits().get(newTerm);
					} else {
						newQuantAtom = new QuantEUBoundConstraint(newTerm, newLhs);
					}
					mState = addNewQuantLit(isPos, newQuantAtom);
				}
			}
			if (mState == EprClauseState.Fulfilled) { // If the clause became trivially true, we stop.
				return;
			}
		}
		// Mark clauses that become trivially false after DER.
		if (mGroundLitsAfterDER.isEmpty() && mQuantLitsAfterDER.isEmpty()) {
			mState = EprClauseState.Conflict;
		}
	}

	/**
	 * Add a quantified literal that results from DER.
	 * 
	 * @param isPos
	 *            flag that marks if the literal is positive or negated.
	 * @param qAtom
	 *            the underlying quantified atom.
	 * @return Fulfilled if adding the literal has made the clause trivially true, Normal otherwise.
	 */
	private EprClauseState addNewQuantLit(final boolean isPos, final QuantLiteral qAtom) {
		assert !(qAtom instanceof NegQuantLiteral) : "Should only be called on atoms";
		if (isPos && mQuantLitsAfterDER.contains(qAtom.negate()) || !isPos && mQuantLitsAfterDER.contains(qAtom)) {
			return EprClauseState.Fulfilled; // Clause contains literal positively and negatively.
		} else {
			mQuantLitsAfterDER.add(isPos ? qAtom : qAtom.negate());
			return EprClauseState.Normal;
		}
	}

	/**
	 * Add a ground literal that results from DER.
	 * 
	 * @param isPos
	 *            flag that marks if the literal is positive or negated.
	 * @param qAtom
	 *            the underlying atom.
	 * @return Fulfilled if adding the literal has made the clause trivially true, Normal otherwise.
	 */
	private EprClauseState addNewGroundLit(final boolean isPos, final Literal atom) {
		assert !(atom instanceof NegLiteral) : "Should only be called on atoms";
		if (isPos && mGroundLitsAfterDER.contains(atom.negate()) || !isPos && mGroundLitsAfterDER.contains(atom)) {
			return EprClauseState.Fulfilled; // Clause contains literal positively and negatively.
		} else {
			mGroundLitsAfterDER.add(isPos ? atom : atom.negate());
			return EprClauseState.Normal;
		}
	}

	/**
	 * Substitute variables that are contained in the substitution sigma within an EUTerm.
	 * 
	 * TODO Can we use one method for this and instantiation?
	 * 
	 * @param euTerm
	 *            an EUTerm where we want to replace all variables in sigma.
	 * @return an EUTerm where the variables in sigma have been replaced by their substitution.
	 */
	private EUTerm substituteInEUTerm(final EUTerm euTerm) {
		if (euTerm instanceof GroundTerm) {
			return euTerm;
		} else if (euTerm instanceof QuantAppTerm) {
			final QuantAppTerm euApp = (QuantAppTerm) euTerm;
			final FunctionSymbol func = euApp.getFunc();
			final QuantAppArg[] quantArgs = euApp.getArgs();
			final QuantAppArg[] newArgs = new QuantAppArg[quantArgs.length];
			final Term[] newArgTerms = new Term[quantArgs.length];
			boolean isGround = true;
			for (int i = 0; i < quantArgs.length; i++) {
				if (quantArgs[i].isVar()) {
					final TermVariable var = quantArgs[i].getVar();
					if (mSigma.containsKey(var)) {
						final Term subs = mSigma.get(var);
						if (subs instanceof TermVariable) {
							newArgs[i] = new QuantAppArg((TermVariable) subs);
							isGround = false;
						} else {
							final EUTerm newEUArg = mQuantTheory.getEUTermManager().getEUTerm(subs, mSource);
							if (!(newEUArg instanceof GroundTerm)) {
								isGround = false;
							}
							newArgs[i] = new QuantAppArg(newEUArg);
						}
						newArgTerms[i] = subs;
					} else {
						newArgs[i] = quantArgs[i];
						newArgTerms[i] = quantArgs[i].getVar();
					}
				} else {
					final EUTerm newEUArg = substituteInEUTerm(quantArgs[i].getEUTerm());
					if (!(newEUArg instanceof GroundTerm)) {
						isGround = false;
					}
					newArgs[i] = new QuantAppArg(newEUArg);
					newArgTerms[i] = newEUArg.getTerm();
				}
			}
			final Term newTerm = mClausifier.getTheory().term(func, newArgTerms);
			if (isGround) {
				final Term[] newGroundArgs = new Term[quantArgs.length];
				for (int i = 0; i < quantArgs.length; i++) {
					newGroundArgs[i] = newArgs[i].getEUTerm().getTerm();
				}
				final Term newGroundApp = mClausifier.getTheory().term(func, newGroundArgs);
				return new GroundTerm(mClausifier, newTerm, mClausifier.getSharedTerm(newGroundApp, mSource));
			} else {
				return new QuantAppTerm(mClausifier, newTerm, func, newArgs);
			}
		} else {
			assert euTerm instanceof QuantAffineTerm;
			final QuantAffineTerm euAffine = (QuantAffineTerm) euTerm;
			final Map<EUTerm, Rational> newSummands = new LinkedHashMap<>();
			boolean isGround = true;
			for (final EUTerm smd : euAffine.getSummands().keySet()) {
				final EUTerm newSmd = substituteInEUTerm(smd);
				if (!(newSmd instanceof GroundTerm)) {
					isGround = false;
				}
				Rational newCoeff = euAffine.getSummands().get(newSmd);
				if (newSummands.containsKey(newSmd)) {
					newCoeff = newCoeff.add(newSummands.get(newSmd));
					if (newCoeff == Rational.ZERO) {
						newSummands.remove(newSmd);
					} else {
						newSummands.put(newSmd, newCoeff);
					}
				} else {
					newSummands.put(newSmd, newCoeff);
				}
			}
			final SMTAffineTerm newSMTAff = new SMTAffineTerm();
			for (final EUTerm euSmd : newSummands.keySet()) {
				newSMTAff.add(newSummands.get(euSmd), euSmd.getTerm());
			}
			newSMTAff.add(euAffine.getConstant());
			final Term newTerm = newSMTAff.toTerm(euAffine.getSort());
			if (isGround) {
				return new GroundTerm(mClausifier, newTerm, mClausifier.getSharedTerm(newTerm, mSource));
			} else {
				return new QuantAffineTerm(mClausifier, newTerm, newSummands, euAffine.getConstant());
			}
		}
	}
}
