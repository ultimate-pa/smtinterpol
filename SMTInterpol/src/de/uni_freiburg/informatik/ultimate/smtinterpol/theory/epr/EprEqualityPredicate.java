package de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.FunctionSymbol;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.dawgs.Dawg;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.dawgs.IDawg;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.partialmodel.IEprLiteral;

public class EprEqualityPredicate extends EprPredicate {

	public EprEqualityPredicate(final FunctionSymbol fs, final EprTheory eprTheory) {
		super(fs, eprTheory);
		// TODO Auto-generated constructor stub
	}


	@Override
	public String toString() {
		return "EprEQPred";
	}

	public IDawg<ApplicationTerm, TermVariable> computeOverallSymmetricTransitiveClosureForPositiveEqualityPred(
			final IDawg<ApplicationTerm, TermVariable> dawg) {
		IDawg<ApplicationTerm, TermVariable> positivelySetPoints =
				mEprTheory.getDawgFactory().getEmptyDawg(mSignature);

		for (final IEprLiteral dsl : mEprLiterals) {
			if (dsl.getPolarity()) {
				//positive literal
				positivelySetPoints = positivelySetPoints.union(dsl.getDawg());
			}
		}

		final IDawg<ApplicationTerm, TermVariable> overallUnion = positivelySetPoints.union(dawg);

		final Dawg<ApplicationTerm, TermVariable> result = overallUnion.computeSymmetricTransitiveClosure();
		// the resulting dawg must denote a superset of the points denoted by the input dawg
		assert overallUnion.complement().intersect(dawg).isEmpty();
		return result;
	}
}
