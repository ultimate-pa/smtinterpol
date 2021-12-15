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
import java.util.Collections;
import java.util.LinkedHashSet;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.FormulaUnLet;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.logic.Theory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.convert.Clausifier;
import de.uni_freiburg.informatik.ultimate.smtinterpol.convert.EqualityProxy;
import de.uni_freiburg.informatik.ultimate.smtinterpol.convert.SMTAffineTerm;
import de.uni_freiburg.informatik.ultimate.smtinterpol.convert.TermCompiler;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.ILiteral;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.Literal;
import de.uni_freiburg.informatik.ultimate.smtinterpol.proof.IProofTracker;
import de.uni_freiburg.informatik.ultimate.smtinterpol.proof.SourceAnnotation;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.linar.MutableAffineTerm;

/**
 * Helper class for substitution in quantified clauses.
 *
 * @author Tanja Schindler
 *
 */
public class SubstitutionHelper {

	private final QuantifierTheory mQuantTheory;
	private final Clausifier mClausifier;
	private final IProofTracker mTracker;

	private final Literal[] mGroundLits;
	private final QuantLiteral[] mQuantLits;
	private final SourceAnnotation mSource;
	private final Map<TermVariable, Term> mSigma;

	private boolean mIsSubstitutionAllowed;

	public SubstitutionHelper(final QuantifierTheory quantTheory, final Literal[] groundLits,
			final QuantLiteral[] quantLits, final SourceAnnotation source, final Map<TermVariable, Term> sigma) {
		mQuantTheory = quantTheory;
		mClausifier = mQuantTheory.getClausifier();
		mTracker = mClausifier.getTracker();
		mGroundLits = groundLits;
		mQuantLits = quantLits;
		mSource = source;
		mSigma = sigma;
	}

	/**
	 * Apply the given substitution to the given clause. The resulting literals and the corresponding term can be
	 * retrieved afterwards.
	 *
	 * This method also performs simplifications on literals and on the clause. The steps are:<br>
	 * (1) Apply the substitution for the single literals, normalize and simplify the terms.<br>
	 * (2) Build the actual literals if no trivially true literals resulted from substitution.<br>
	 * (3) Remove duplicates and false literals (implicitly, i.e. only in the proof; they were not built).<br>
	 * (4) Build the final disjunction.
	 * 
	 * @return the result of the substitution and simplification.
	 */
	public SubstitutionResult substituteInClause() {

		assert !mSigma.isEmpty();
		mIsSubstitutionAllowed = true;

		final Term[] substitutedLitTerms = new Term[mGroundLits.length + mQuantLits.length];
		final Term[] provedLitTerms = new Term[mGroundLits.length + mQuantLits.length];
		// We also need duplicates here for proof production.
		final Set<ILiteral> resultingGroundLits = new LinkedHashSet<>();
		final Set<ILiteral> resultingQuantLits = new LinkedHashSet<>();

		final Theory theory = mQuantTheory.getTheory();

		// Ground literals remain unchanged.
		for (int i = 0; i < mGroundLits.length; i++) {
			final Literal lit = mGroundLits[i];
			final Term groundLitTerm = lit.getSMTFormula(theory, true);
			substitutedLitTerms[i] = groundLitTerm;
			provedLitTerms[i] = mTracker.reflexivity(groundLitTerm);
			resultingGroundLits.add(lit);
		}

		// Substitute in quantified literals
		final Term[] nonTrivialLitTermsAfterSimplification = new Term[mQuantLits.length];
		for (int i = 0; i < mQuantLits.length; i++) {
			final QuantLiteral lit = mQuantLits[i];
			final int pos = mGroundLits.length + i;
			if (Collections.disjoint(Arrays.asList(lit.getTerm().getFreeVars()), mSigma.keySet())) {
				// Nothing to substitute.
				substitutedLitTerms[pos] = lit.getSMTFormula(theory, true);
				provedLitTerms[pos] = mTracker.reflexivity(lit.getSMTFormula(theory, true));
				resultingQuantLits.add(lit);
			} else { // Build the new literals. Separate ground and quantified literals.

				// Substitute variables.
				final FormulaUnLet unletter = new FormulaUnLet();
				unletter.addSubstitutions(mSigma);
				final Term substituted = unletter.transform(lit.getTerm()); // TODO Maybe we should substitute the
				// annotation as well (for aux-lits)
				substitutedLitTerms[pos] = substituted;

				// Simplify the resulting term.
				assert substituted instanceof ApplicationTerm;

				Term simplified = normalizeAndSimplifyLitTerm((ApplicationTerm) substituted, lit);

				if (simplified == null) {
					mIsSubstitutionAllowed = false;
					return buildTrueResult();
				}

				if (mTracker.getProvedTerm(simplified) == theory.mTrue) { // Clause is trivially true.
					mClausifier.getLogger().debug("Quant: trivially true clause detected before building literals.");
					return buildTrueResult();
				} else if (mTracker.getProvedTerm(simplified) == theory.mFalse) {
					provedLitTerms[pos] = simplified;
				} else {
					nonTrivialLitTermsAfterSimplification[i] = simplified;
				}
			}
		}

		// Build the literals for the terms obtained after substitution and simplification (unless trivially false)
		for (int i = 0; i < mQuantLits.length; i++) {
			Term simplified = nonTrivialLitTermsAfterSimplification[i];
			if (simplified == null) {
				continue;
			}
			final ILiteral newAtom;
			boolean isPos = true;
			Term atomTerm = mTracker.getProvedTerm(simplified);
			assert atomTerm instanceof ApplicationTerm;
			if (((ApplicationTerm) atomTerm).getFunction().getName() == "not") {
				atomTerm = ((ApplicationTerm) atomTerm).getParameters()[0];
				isPos = false;
			}
			assert atomTerm instanceof ApplicationTerm;
			final ApplicationTerm atomApp = (ApplicationTerm) atomTerm;
			if (atomApp.getFunction().getName() == "<=") {
				if (atomApp.getFreeVars().length == 0) {
					final SMTAffineTerm lhs = new SMTAffineTerm(atomApp.getParameters()[0]);
					final MutableAffineTerm msum = mClausifier.createMutableAffinTerm(lhs, mSource);
					newAtom = mQuantTheory.getLinAr().generateConstraint(msum, false);
				} else {
					newAtom = mQuantTheory.getQuantInequality(isPos, atomApp.getParameters()[0], mSource);
				}
			} else if (atomApp.getFunction().getName() == "=") {
				final Term lhs = atomApp.getParameters()[0];
				final Term rhs = atomApp.getParameters()[1];
				if (atomApp.getFreeVars().length == 0) { // Ground equality or predicate.
					final EqualityProxy eq = mClausifier.createEqualityProxy(lhs, rhs, mSource);
					assert eq != EqualityProxy.getTrueProxy() && eq != EqualityProxy.getFalseProxy();
					newAtom = eq.getLiteral(mSource);
				} else {
					newAtom = mQuantTheory.getQuantEquality(lhs, rhs, mSource);
				}
			} else { // Predicates
				assert atomApp.getFreeVars().length == 0; // Quantified predicates are stored as equalities.
				assert atomApp.getSort() == theory.getBooleanSort();
				final Term sharedLhs = atomApp;
				final Term sharedRhs = theory.mTrue;
				final EqualityProxy eq = mClausifier.createEqualityProxy(sharedLhs, sharedRhs, mSource);
				assert eq != EqualityProxy.getTrueProxy() && eq != EqualityProxy.getFalseProxy();
				newAtom = eq.getLiteral(mSource);
			}
			// As in clausifier
			final Term atomIntern = mTracker.intern(atomApp, newAtom.getSMTFormula(theory, true));
			if (isPos) {
				simplified = mTracker.transitivity(simplified, atomIntern);
			} else {
				simplified = mTracker.congruence(simplified, new Term[] { atomIntern });
				/* (not (<= -x 0)) can be rewritten to (not (not (< x 0))); remove double negation */
				simplified = mClausifier.getSimplifier().convertNot(simplified);
			}
			provedLitTerms[mGroundLits.length + i] = simplified;

			final ILiteral newLiteral = isPos ? newAtom : newAtom.negate();
			if (newLiteral instanceof Literal) {
				final Literal newGroundLit = (Literal) newLiteral;
				if (resultingGroundLits.contains(newGroundLit.negate())) { // Clause simplifies to true
					mClausifier.getLogger()
							.debug("Quant: trivially true clause instance detected while building literals.");
					return buildTrueResult();
				} else {
					resultingGroundLits.add(newGroundLit);
				}
			} else {
				final QuantLiteral newQuantLit = (QuantLiteral) newLiteral;
				if (resultingQuantLits.contains(newQuantLit.negate())) { // Clause simplifies to true
					mClausifier.getLogger()
							.debug("Quant: trivially true clause instance detected while building literals.");
					return buildTrueResult();
				} else {
					resultingQuantLits.add(newQuantLit);
				}
			}
		}

		// Build the disjunction.
		final boolean isUnitClause = substitutedLitTerms.length == 1;
		final Term substitutedClause = isUnitClause ? substitutedLitTerms[0] : theory.term("or", substitutedLitTerms);
		Term simpClause;
		if (isUnitClause) {
			assert provedLitTerms.length == 1;
			simpClause = provedLitTerms[0];
		} else {
			simpClause = mTracker.congruence(mTracker.reflexivity(substitutedClause), provedLitTerms);
			simpClause = mTracker.orSimpClause(simpClause);
		}

		return new SubstitutionResult(substitutedClause, simpClause,
				resultingGroundLits.toArray(new Literal[resultingGroundLits.size()]),
				resultingQuantLits.toArray(new QuantLiteral[resultingQuantLits.size()]));
	}

	public boolean isSubstitutionAllowed() {
		return mIsSubstitutionAllowed;
	}

	/**
	 * Normalize an equality or inequality literal term.
	 * @return the simplified term and its rewrite proof, null if the substitution is not allowed.
	 */
	private Term normalizeAndSimplifyLitTerm(final ApplicationTerm litTerm, final QuantLiteral lit) {
		final Theory theory = mQuantTheory.getTheory();

		final ApplicationTerm atomTerm =
				litTerm.getFunction().getName() == "not" ? (ApplicationTerm) litTerm.getParameters()[0] : litTerm;
				assert atomTerm.getFunction().getName() == "<=" || atomTerm.getFunction().getName() == "=";

				final TermCompiler compiler = mClausifier.getTermCompiler();
				// First check literals where a variable has been substituted by lambda
				if (hasLambdaSubstitution(lit)) {
					// TODO Check proof production!
					if (lit.isArithmetical()) {
						final Term lambdaSimp;
						if (atomTerm.getFunction().getName() == "=") {
							assert QuantUtil.isLambda(atomTerm.getParameters()[0]);
							lambdaSimp = mTracker.intern(atomTerm, mQuantTheory.getTheory().mFalse);
						} else {
							final Term[] termLtTerm = QuantUtil.getArithmeticalTermLtTerm(lit, compiler);
							final Term groundLhs =
									termLtTerm[0].getFreeVars().length == 0 ? termLtTerm[0] : mSigma.get(termLtTerm[0]);
									final Term groundRhs =
											termLtTerm[1].getFreeVars().length == 0 ? termLtTerm[1] : mSigma.get(termLtTerm[1]);
											if (QuantUtil.isLambda(groundRhs)) {
												lambdaSimp = mTracker.intern(atomTerm, mQuantTheory.getTheory().mTrue);
											} else {
												assert QuantUtil.isLambda(groundLhs);
												lambdaSimp = mTracker.intern(atomTerm, mQuantTheory.getTheory().mFalse);
											}
						}
				return atomTerm != litTerm ? lambdaSimp
						: mClausifier.getSimplifier().convertNot(
								mTracker.congruence(mTracker.reflexivity(litTerm), new Term[] { lambdaSimp }));
					} else {
						if (QuantUtil.containsLambdasInArithmetic(atomTerm.getParameters()[0])
								|| QuantUtil.containsLambdasInArithmetic(atomTerm.getParameters()[1])) {
							return null;
						}
					}
				}
				// Term compiler normalizes and simplifies <= literals.
				if (atomTerm.getFunction().getName() == "<=") {
					return compiler.transform(litTerm);
				}

				// Other quantified literals are equalities
				assert atomTerm.getFunction().getName() == "=";
				final Term lhs = atomTerm.getParameters()[0];
				final Term rhs = atomTerm.getParameters()[1];
				if (QuantUtil.isAuxApplication(lhs)) {
					return mTracker.reflexivity(litTerm);
				}

				// Normalize lhs and rhs separately
				Term normalizedAtom;
				final Term normalizedLhs = compiler.transform(lhs);
				final Term normalizedRhs = compiler.transform(rhs);
				normalizedAtom =
						mTracker.congruence(mTracker.reflexivity(atomTerm), new Term[] { normalizedLhs, normalizedRhs });

				// Simplify equality literals similar to EqualityProxy. (TermCompiler already takes care of <= literals).
				Term simplifiedAtom = mTracker.getProvedTerm(normalizedAtom);
				assert simplifiedAtom instanceof ApplicationTerm;
				final ApplicationTerm appTerm = (ApplicationTerm) simplifiedAtom;
				if (appTerm.getFunction().getName() == "=") {
					final Term trivialEq = Clausifier.checkAndGetTrivialEquality(appTerm.getParameters()[0],
							appTerm.getParameters()[1], theory);
					if (trivialEq != null) {
						simplifiedAtom = trivialEq;
					}
				}
				if (simplifiedAtom != mTracker.getProvedTerm(normalizedAtom)) {
					normalizedAtom = mTracker.transitivity(normalizedAtom,
							mTracker.intern(mTracker.getProvedTerm(normalizedAtom), simplifiedAtom));
				}
				if (atomTerm != litTerm) {
					return mClausifier.getSimplifier()
							.convertNot(mTracker.congruence(mTracker.reflexivity(litTerm), new Term[] { normalizedAtom }));
				}
				return normalizedAtom;
	}

	private SubstitutionResult buildTrueResult() {
		return new SubstitutionResult(null, null, null, null);
	}

	/**
	 * This class is used to collect the result from substituting variables in a clause. It contains information about
	 * the substituted clause term, the simplified substituted term, and the corresponding literals.
	 */
	static class SubstitutionResult {
		final Term mSubstituted;
		final Term mSimplified;
		final Literal[] mGroundLits;
		final QuantLiteral[] mQuantLits;

		/**
		 * Build a new SubstitutionResult.
		 * 
		 * @param substituted
		 *            the substituted term.
		 * @param simplified
		 *            the simplified term, potentially annotated with a proof that it equals the substituted term
		 * @param groundLits
		 *            the resulting ground literals
		 * @param quantLits
		 *            the resulting quantified literals
		 */
		protected SubstitutionResult(final Term substituted, final Term simplified, final Literal[] groundLits,
				final QuantLiteral[] quantLits) {
			mSubstituted = substituted;
			mSimplified = simplified;
			mGroundLits = groundLits;
			mQuantLits = quantLits;
		}

		public boolean isTriviallyTrue() {
			return mSimplified == null;
		}

		public boolean isGround() {
			return isTriviallyTrue() || mQuantLits.length == 0;
		}

		public Term getSubstituted() {
			return mSubstituted;
		}

		public Term getSimplified() {
			return mSimplified;
		}

		public Literal[] getGroundLits() {
			return mGroundLits;
		}

		public QuantLiteral[] getQuantLits() {
			return mQuantLits;
		}
	}

	/**
	 * Check if a variable in the given quantified literal is substituted by lambda.
	 * 
	 * @param lit
	 *            the quantified literal.
	 * @param subs
	 *            a variable substitution.
	 * @return true if any of the free variables in lit is mapped to a lambda term in the substitution subs, false
	 *         otherwise.
	 */
	private boolean hasLambdaSubstitution(final QuantLiteral lit) {
		for (final TermVariable var : lit.getTerm().getFreeVars()) {
			if (QuantUtil.isLambda(mSigma.get(var))) {
				return true;
			}
		}
		return false;
	}
}
