/*
 * Copyright (C) 2026 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.smtinterpol.convert;

import java.util.Arrays;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.FormulaUnLet;
import de.uni_freiburg.informatik.ultimate.logic.SMTLIBConstants;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.logic.Theory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.ILiteral;
import de.uni_freiburg.informatik.ultimate.smtinterpol.proof.ProofTracker;
import de.uni_freiburg.informatik.ultimate.smtinterpol.proof.resolute.ProofLiteral;
import de.uni_freiburg.informatik.ultimate.smtinterpol.proof.resolute.ProofRules;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.quant.DestructiveEqualityReasoning.DERResult;

/**
 * Derives the sat-proof entries of a clause after destructive equality reasoning from the entries of the original
 * clause, without the model. See "DER stays in half 1" in SMTInterpol/doc/model-proof-plan.md.
 *
 * DER substitutes {@code σ} into {@code ψ = (x ≠ t) ∨ l_1 ∨ … ∨ l_n} and simplifies. All entries of the original
 * record are instantiated with the choose terms {@code θ}. For a substituted literal {@code l_i}, the proof of
 * {@code {~l_i[σ][θ]} ∪ R} is a case split on {@code σ(x)[θ] = θ(x)}: congruence relates {@code l_i[σ][θ]} and
 * {@code l_i[θ]}, the entry of {@code l_i} gives the target, and the entry of the DER literal discharges the
 * equality. The reversed simplification rewrite then gives the new literal.
 *
 * @author Jochen Hoenicke
 */
final class DERSatRecord {
	private final Clausifier mClausifier;
	private final ProofRules mRules;
	private final Theory mTheory;
	/** The entries of the original clause (instantiated with θ). */
	private final Map<ILiteral, Clausifier.SatEntry> mEntries;
	private final ProofLiteral[] mTarget;
	/** The DER substitution σ (eliminated variables only). */
	private final Map<TermVariable, Term> mSigma;
	/** Memo: a proof of {@code (= u[σ][θ] u[θ])} ∪ rest, per term u containing an eliminated variable. */
	private final Map<Term, Proved> mCongMemo = new HashMap<>();
	/** Memo: a proof of {@code (= σ(x)[θ] θ(x))} ∪ rest, per eliminated variable. */
	private final Map<TermVariable, Proved> mVarMemo = new HashMap<>();
	private final Set<TermVariable> mInProgress = new HashSet<>();

	/** A proof of a clause {@code {lit} ∪ rest}. */
	private static final class Proved {
		final Term mProof;
		final Set<ProofLiteral> mRest;

		Proved(final Term proof, final Set<ProofLiteral> rest) {
			mProof = proof;
			mRest = rest;
		}
	}

	private DERSatRecord(final Clausifier clausifier, final Clausifier.ClauseSatProof record,
			final Map<TermVariable, Term> sigma) {
		mClausifier = clausifier;
		mRules = ((ProofTracker) clausifier.mTracker).getProofRules();
		mTheory = clausifier.getTheory();
		mEntries = record.mLiterals;
		mTarget = record.mTarget;
		mSigma = sigma;
	}

	/**
	 * Derive the entries of the DER'd clause.
	 *
	 * @param record
	 *            the sealed record of the original clause.
	 * @param vars
	 *            the variables of the original clause, aligned with {@code der.getSubs()}.
	 * @param clauseLits
	 *            the literals of the original clause in the order DER processed them (ground literals first, then
	 *            quantified ones), aligned with {@code der.getNewLits()}.
	 * @return the entries keyed by the literals of the DER'd clause, or null if they cannot be derived.
	 */
	static Map<ILiteral, Clausifier.SatEntry> derive(final Clausifier clausifier,
			final Clausifier.ClauseSatProof record, final DERResult der, final TermVariable[] vars,
			final ILiteral[] clauseLits) {
		final Map<TermVariable, Term> sigma = new LinkedHashMap<>();
		final Term[] subs = der.getSubs();
		for (int i = 0; i < vars.length; i++) {
			if (subs[i] != vars[i]) {
				sigma.put(vars[i], subs[i]);
			}
		}
		return new DERSatRecord(clausifier, record, sigma).derive(der, clauseLits);
	}

	/**
	 * For a clause that DER made trivially true: fill in the record's ready-made proof, from the derived entry of the
	 * literal that became true, or of the two literals that became complementary.
	 *
	 * @return false if that is not possible.
	 */
	static boolean deriveTrivial(final Clausifier clausifier, final Clausifier.ClauseSatProof record,
			final DERResult der, final TermVariable[] vars, final ILiteral[] clauseLits) {
		final Map<TermVariable, Term> sigma = new LinkedHashMap<>();
		final Term[] subs = der.getSubs();
		for (int i = 0; i < vars.length; i++) {
			if (subs[i] != vars[i]) {
				sigma.put(vars[i], subs[i]);
			}
		}
		return new DERSatRecord(clausifier, record, sigma).deriveTrivial(record, der, clauseLits);
	}

	private boolean deriveTrivial(final Clausifier.ClauseSatProof record, final DERResult der,
			final ILiteral[] clauseLits) {
		// the per-literal information ends with the literal that made the clause true
		final ILiteral[] newLits = der.getNewLits();
		final int last = newLits.length - 1;
		final Clausifier.SatEntry lastEntry = entryFor(der, clauseLits, last);
		if (lastEntry == null) {
			return false;
		}
		if (newLits[last] == null) {
			// the literal simplified to true: lastEntry proves {~true} ∪ R
			return record.setReadyMadeFromTrueLiteral(lastEntry, mClausifier);
		}
		for (int j = 0; j < last; j++) {
			if (newLits[j] == newLits[last].negate()) {
				final Clausifier.SatEntry negEntry = entryFor(der, clauseLits, j);
				if (negEntry == null) {
					return false;
				}
				final ProofLiteral lit =
						Clausifier.toProofLiteral(instantiate(newLits[last].getSMTFormula(mTheory)));
				return record.setReadyMadeFromPair(lit, lastEntry, negEntry, mClausifier);
			}
		}
		return false;
	}

	/** The entry of the i-th literal of the DER'd clause (derived if DER changed it), or null. */
	private Clausifier.SatEntry entryFor(final DERResult der, final ILiteral[] clauseLits, final int i) {
		final Clausifier.SatEntry entry = mEntries.get(clauseLits[i]);
		if (entry == null || der.getNewLits()[i] == clauseLits[i]) {
			return entry;
		}
		return deriveEntry(clauseLits[i], entry, der.getSubstitutedLits()[i], der.getLitRewrites()[i]);
	}

	private Map<ILiteral, Clausifier.SatEntry> derive(final DERResult der, final ILiteral[] clauseLits) {
		final Term[] substituted = der.getSubstitutedLits();
		final Term[] rewrites = der.getLitRewrites();
		final ILiteral[] newLits = der.getNewLits();
		assert clauseLits.length == newLits.length;
		final Map<ILiteral, Clausifier.SatEntry> result = new LinkedHashMap<>();
		for (int i = 0; i < clauseLits.length; i++) {
			final ILiteral orig = clauseLits[i];
			final ILiteral newLit = newLits[i];
			if (newLit == null || result.containsKey(newLit)) {
				// simplified to false, or merged with an earlier literal
				continue;
			}
			final Clausifier.SatEntry entry = mEntries.get(orig);
			if (entry == null) {
				return null;
			}
			final Term substLit = substituted[i];
			final Term rewrite = rewrites[i];
			if (newLit == orig) {
				result.put(newLit, entry);
				continue;
			}
			final Clausifier.SatEntry derived = deriveEntry(orig, entry, substLit, rewrite);
			if (derived == null) {
				return null;
			}
			result.put(newLit, derived);
		}
		return result;
	}

	private Term instantiate(final Term t) {
		return mClausifier.instantiate(t);
	}

	/** {@code u[σ][θ]}. */
	private Term instantiateSigma(final Term u) {
		final FormulaUnLet unlet = new FormulaUnLet();
		unlet.addSubstitutions(mSigma);
		return instantiate(unlet.transform(u));
	}

	private boolean containsEliminated(final Term u) {
		for (final TermVariable tv : u.getFreeVars()) {
			if (mSigma.containsKey(tv)) {
				return true;
			}
		}
		return false;
	}

	private Term res(final Term pivot, final Term pos, final Term neg) {
		return mRules.resolutionRule(pivot, pos, neg);
	}

	/**
	 * The entry of the substituted literal {@code orig}, as entry of the new literal it became: a proof of
	 * {@code {~newLit[θ]} ∪ rest}.
	 */
	private Clausifier.SatEntry deriveEntry(final ILiteral orig, final Clausifier.SatEntry entry, final Term substLit,
			final Term rewrite) {
		final ProofLiteral lit = Clausifier.toProofLiteral(orig.getSMTFormula(mTheory));
		final Term atom = lit.getAtom();
		final Proved cong = proveCongruence(atom);
		if (cong == null) {
			return null;
		}
		final Term p = instantiateSigma(atom);
		final Term q = instantiate(atom);
		final Term eq = mTheory.term(SMTLIBConstants.EQUALS, p, q);
		final Set<ProofLiteral> rest = new LinkedHashSet<>(cong.mRest);
		// {~(= p q), ~lit[σ][θ], lit[θ]}
		Term proof = lit.getPolarity() ? mRules.iffElim2(eq) : mRules.iffElim1(eq);
		if (entry.mProof != null) {
			// entry: {~lit[θ]} ∪ R
			proof = lit.getPolarity() ? res(q, proof, entry.mProof) : res(q, entry.mProof, proof);
		}
		rest.addAll(Arrays.asList(entry.getRest(mTarget)));
		proof = res(eq, cong.mProof, proof);
		// reversed simplification {~newLit, lit[σ]}
		final Term reverse = mClausifier.mTracker.rewriteToClauseReverse(substLit, rewrite);
		if (reverse != null) {
			final Term reverseProof = instantiate(mClausifier.mTracker.getClauseProof(reverse));
			proof = lit.getPolarity() ? res(p, reverseProof, proof) : res(p, proof, reverseProof);
		}
		return new Clausifier.SatEntry(proof, rest.toArray(new ProofLiteral[rest.size()]));
	}

	/**
	 * Prove {@code (= u[σ][θ] u[θ])} by structural congruence; {@code u} contains an eliminated variable.
	 *
	 * @return the proof and its remaining literals (from the DER literals' entries), or null if not possible.
	 */
	private Proved proveCongruence(final Term u) {
		if (u instanceof TermVariable) {
			return proveVariable((TermVariable) u);
		}
		Proved result = mCongMemo.get(u);
		if (result != null || mCongMemo.containsKey(u)) {
			return result;
		}
		if (u instanceof ApplicationTerm) {
			final Term[] params = ((ApplicationTerm) u).getParameters();
			Term proof = mRules.cong(instantiateSigma(u), instantiate(u));
			final Set<ProofLiteral> rest = new LinkedHashSet<>();
			final Set<Term> resolved = new HashSet<>();
			for (final Term param : params) {
				final Term left = instantiateSigma(param);
				final Term eq = mTheory.term(SMTLIBConstants.EQUALS, left, instantiate(param));
				if (!resolved.add(eq)) {
					continue;
				}
				if (containsEliminated(param)) {
					final Proved sub = proveCongruence(param);
					if (sub == null) {
						proof = null;
						break;
					}
					proof = res(eq, sub.mProof, proof);
					rest.addAll(sub.mRest);
				} else {
					proof = res(eq, mRules.refl(left), proof);
				}
			}
			result = proof == null ? null : new Proved(proof, rest);
		}
		// a binder containing an eliminated variable: not supported (matches are rewritten to ite before)
		if (result != null || mInProgress.isEmpty()) {
			// a failure while some variable is in progress may be due to a cycle; don't remember it
			mCongMemo.put(u, result);
		}
		return result;
	}

	/**
	 * Prove {@code (= σ(x)[θ] θ(x))} from a DER literal {@code (x ≠ s)} (or {@code (s ≠ x)}) of the original clause
	 * with {@code s = σ(x)}, or, if DER composed its substitution, with {@code s[σ] = σ(x)}. (DER applies {@code σ}
	 * simultaneously, and it need not be idempotent: {@code {x ↦ y, y ↦ (f z)}} keeps {@code y}.)
	 */
	private Proved proveVariable(final TermVariable x) {
		final Proved memo = mVarMemo.get(x);
		if (memo != null || !mInProgress.add(x)) {
			return memo;
		}
		final Term sigmaX = instantiateSigma(x);
		final Term thetaX = instantiate(x);
		Proved result = null;
		for (final Map.Entry<ILiteral, Clausifier.SatEntry> e : mEntries.entrySet()) {
			final ProofLiteral lit = Clausifier.toProofLiteral(e.getKey().getSMTFormula(mTheory));
			final Clausifier.SatEntry entry = e.getValue();
			if (lit.getPolarity() || entry.mProof == null || !(lit.getAtom() instanceof ApplicationTerm)) {
				continue;
			}
			final ApplicationTerm atom = (ApplicationTerm) lit.getAtom();
			if (atom.getFunction().getName() != SMTLIBConstants.EQUALS || atom.getParameters().length != 2) {
				continue;
			}
			final Term a = atom.getParameters()[0];
			final Term b = atom.getParameters()[1];
			final Term s = a == x ? b : b == x ? a : null;
			if (s == null || s == x) {
				continue;
			}
			final Term sTheta = instantiate(s);
			final boolean direct = sTheta == sigmaX;
			if (!direct && (!containsEliminated(s) || instantiateSigma(s) != sigmaX)) {
				continue;
			}
			// entry: {(= a[θ] b[θ])} ∪ R; make it {(= s[θ] θ(x))} ∪ R
			Term proof = entry.mProof;
			if (a == x) {
				final Term eqXs = mTheory.term(SMTLIBConstants.EQUALS, thetaX, sTheta);
				proof = res(eqXs, proof, mRules.symm(sTheta, thetaX));
			}
			final Set<ProofLiteral> rest = new LinkedHashSet<>(Arrays.asList(entry.getRest(mTarget)));
			if (!direct) {
				// (= s[σ][θ] s[θ]) by congruence, then transitivity
				final Proved cong = proveCongruence(s);
				if (cong == null) {
					continue;
				}
				final Term trans = mRules.trans(sigmaX, sTheta, thetaX);
				proof = res(mTheory.term(SMTLIBConstants.EQUALS, sTheta, thetaX), proof,
						res(mTheory.term(SMTLIBConstants.EQUALS, sigmaX, sTheta), cong.mProof, trans));
				rest.addAll(cong.mRest);
			}
			result = new Proved(proof, rest);
			break;
		}
		mInProgress.remove(x);
		if (result != null) {
			mVarMemo.put(x, result);
		}
		return result;
	}
}
