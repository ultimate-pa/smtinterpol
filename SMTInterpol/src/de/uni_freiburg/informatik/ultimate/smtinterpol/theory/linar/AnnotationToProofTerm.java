/*
 * Copyright (C) 2009-2013 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.smtinterpol.theory.linar;

import java.util.ArrayDeque;
import java.util.HashMap;
import java.util.Iterator;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.logic.Annotation;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.Theory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.Literal;
import de.uni_freiburg.informatik.ultimate.smtinterpol.proof.ProofLiteral;
import de.uni_freiburg.informatik.ultimate.smtinterpol.proof.ProofRules;

/**
 * Class that generates a proof term for a LAAnnotation. This is called by
 * LAAnnotation.toTerm().
 *
 * @author Jochen Hoenicke
 */
public class AnnotationToProofTerm {
	private static final Annotation TRICHOTOMY = new Annotation(":trichotomy", null);

	/**
	 * For each (sub-)annotation we store a bit of information needed for the
	 * conversion process.
	 */
	class AnnotationInfo {
		/**
		 * Number of times this annotation is referenced in other annotation. This is
		 * one for the base annotation.
		 */
		int mCount;
		/**
		 * Number of times this annotation was visited in the conversion process. Only
		 * when it is visited for the last time, we do the actual conversion.
		 */
		int mVisited;
		/**
		 * SMT representation of the bound explained by this sub-annotation. This is
		 * null for the base annotation.
		 */
		ProofLiteral mLiteral;
	}

	/**
	 * Compute the gcd of all Farkas coefficients used in the annotation. This is
	 * used to make the Farkas coefficients integral.
	 *
	 * @param annot
	 *            the annotation.
	 * @return the gcd of all Farkas coefficients in annot.
	 */
	private Rational computeGcd(final LAAnnotation annot) {
		Rational gcd = null;
		Iterator<Rational> it = annot.getCoefficients().values().iterator();
		if (it.hasNext()) {
			gcd = it.next();
		}
		while (it.hasNext()) {
			gcd = gcd.gcd(it.next());
		}
		it = annot.getAuxAnnotations().values().iterator();
		if (gcd == null && it.hasNext()) {
			gcd = it.next();
		}
		while (it.hasNext()) {
			gcd = gcd.gcd(it.next());
		}
		assert gcd != null;
		return gcd;
	}

	/**
	 * Fill the literal and negLiteral field in annotation info.
	 *
	 * @param annot
	 *            the annotation.
	 * @param theory
	 *            the SMT theory.
	 * @param info
	 *            the information corresponding to the annotation.
	 */
	private void computeLiterals(final LAAnnotation annot, final Theory theory, final AnnotationInfo info) {
		final MutableAffineTerm at = new MutableAffineTerm();
		at.add(Rational.ONE, annot.getLinVar());
		at.add(annot.getBound().negate());
		if (!annot.isUpper()) {
			at.add(annot.getLinVar().getEpsilon());
		}
		final Term posTerm = at.toSMTLibLeq0(theory);
		info.mLiteral = new ProofLiteral(posTerm, annot.isUpper());
	}

	/**
	 * Convert the base annotation to a proof object.
	 *
	 * @param parent
	 *            the base annotation (i.e. its linvar is null).
	 * @param theory
	 *            the SMT theory.
	 * @return the proof term corresponding to the annotation.
	 */
	public Term convert(final LAAnnotation parent, final ProofRules proofRules) {
		assert (parent.getLinVar() == null);
		final Theory theory = proofRules.getTheory();
		final HashMap<LAAnnotation, AnnotationInfo> infos = new HashMap<>();

		// Count the occurrences of each annotation (and compute literals).
		final ArrayDeque<LAAnnotation> todo = new ArrayDeque<>();
		todo.add(parent);
		while (!todo.isEmpty()) {
			final LAAnnotation annot = todo.removeFirst();
			AnnotationInfo info = infos.get(annot);
			if (info == null) {
				info = new AnnotationInfo();
				infos.put(annot, info);
				if (annot.getLinVar() != null) {
					computeLiterals(annot, theory, info);
				}
				todo.addAll(annot.getAuxAnnotations().keySet());
			}
			info.mCount++;
		}

		Term proof = null;
		todo.add(parent);
		todo_loop: while (!todo.isEmpty()) {
			final LAAnnotation annot = todo.removeFirst();
			final AnnotationInfo info = infos.get(annot);
			info.mVisited++;
			if (info.mVisited < info.mCount) {
				continue;
			}

			// The annotation was visited for the final time.

			// Add its sub-annotations to the todo list.
			todo.addAll(annot.getAuxAnnotations().keySet());

			// Now convert it to a clause and add it to antes.
			final Rational gcd = computeGcd(annot);
			final int numdisjs = annot.getCoefficients().size() + annot.getAuxAnnotations().size()
					+ (info.mLiteral == null ? 0 : 1);
			int i = 0;
			final ProofLiteral[] proofLits = new ProofLiteral[numdisjs];
			final Term[] coeffs = new Term[numdisjs];
			if (info.mLiteral != null) {
				final Rational sign = annot.isUpper() ? Rational.MONE : Rational.ONE;
				proofLits[i] = info.mLiteral;
				coeffs[i] = sign.div(gcd).toTerm(getSort(theory));
				++i;
			}
			boolean trichotomy = false;
			for (final Map.Entry<Literal, Rational> me : annot.getCoefficients().entrySet()) {
				final Literal lit = me.getKey();
				if (lit instanceof LAEquality) {
					trichotomy = true;
				}
				proofLits[i] = new ProofLiteral(lit.getAtom().getSMTFormula(theory), lit == lit.getAtom());
				coeffs[i] = me.getValue().div(gcd).toTerm(getSort(theory));
				++i;
			}
			for (final Map.Entry<LAAnnotation, Rational> me : annot.getAuxAnnotations().entrySet()) {
				final AnnotationInfo auxInfo = infos.get(me.getKey());
				proofLits[i] = auxInfo.mLiteral.negate();
				coeffs[i] = me.getValue().div(gcd).toTerm(getSort(theory));
				++i;
			}
			// If the generated clause would just be of the form
			// ell \/ not ell, we omit the clause from the
			// proof.
			if (proofLits.length == 2 && proofLits[0].equals(proofLits[1].negate())) {
				continue todo_loop;
			}
			final Annotation[] annots = new Annotation[] { trichotomy ? TRICHOTOMY : new Annotation(":LA", coeffs) };
			final Term proofAntes = proofRules.oracle(proofLits, annots);
			if (proof == null) {
				proof = proofAntes;
			} else {
				// Since the base annotation should be translated first
				// this must be a sub-annotation, so we should have the
				// corresponding pivot literal.
				proof = proofRules.resolutionRule(info.mLiteral.getAtom(),
						info.mLiteral.getPolarity() ? proofAntes : proof,
						info.mLiteral.getPolarity() ? proof : proofAntes);
			}
		}
		return proof;
	}

	/**
	 * Helper method to retrieve a sort used to convert Rationals. By default, we
	 * try to print Rationals as integers. If this fails, we switch back to reals.
	 *
	 * @param t
	 *            The theory used to create sorts and terms.
	 * @return A sort to use for conversion of Rationals.
	 */
	private Sort getSort(final Theory t) {
		final Sort res = t.getSort("Int");
		return res == null ? t.getSort("Real") : res;
	}
}
