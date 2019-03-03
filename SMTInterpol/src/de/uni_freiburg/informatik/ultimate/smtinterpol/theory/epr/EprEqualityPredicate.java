package de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.FunctionSymbol;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.dawgs.DawgFactory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.dawgs.dawgstates.DawgState;
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

	public DawgState<ApplicationTerm, Boolean> computeOverallSymmetricTransitiveClosureForPositiveEqualityPred(
			final DawgState<ApplicationTerm, Boolean> dawg) {
		final DawgFactory<ApplicationTerm, TermVariable> factory = mEprTheory.getDawgFactory();
		DawgState<ApplicationTerm, Boolean> positivelySetPoints =
				factory.createConstantDawg(mSignature, Boolean.FALSE);

		for (final IEprLiteral dsl : mEprLiterals) {
			if (dsl.getPolarity()) {
				//positive literal
				positivelySetPoints = factory.createUnion(positivelySetPoints, dsl.getDawg());
			}
		}

		final DawgState<ApplicationTerm, Boolean> overallUnion = factory.createUnion(positivelySetPoints, dawg);

		final DawgState<ApplicationTerm, Boolean> result = factory.computeSymmetricTransitiveClosure(overallUnion);
		// the resulting dawg must denote a superset of the points denoted by the input dawg
		assert factory.isEmpty(factory.createProduct(overallUnion, dawg, (inOverall, inDawg) -> !inOverall && inDawg));
		return result;
	}
}
