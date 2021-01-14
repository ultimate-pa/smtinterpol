package de.uni_freiburg.informatik.ultimate.smtinterpol.theory.bitvector;

import java.util.Arrays;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.ConstantTerm;
import de.uni_freiburg.informatik.ultimate.logic.FunctionSymbol;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermTransformer;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.logic.Theory;

public class CnfTransformer extends TermTransformer {
	@Override
	public void convert(final Term term) {
		if ((term instanceof ConstantTerm) || (term instanceof TermVariable)) {
			setResult(term);
			return;
		} else if (term instanceof ApplicationTerm) {
			final ApplicationTerm appTerm = (ApplicationTerm) term;
			enqueueWalker(new BuildApplicationTerm(appTerm));
			pushTerms(appTerm.getParameters());
		}
		super.convert(term);
	}

	@Override
	public void convertApplicationTerm(final ApplicationTerm appTerm, final Term[] newArgs) {
		// ersetzt appterm durch setResult
		Term newTerm = appTerm;
		// if (newArgs != appTerm.getParameters()) {
		final FunctionSymbol fun = appTerm.getFunction();
		final Theory theory = fun.getTheory();
		if (fun.getName().equals("or")) {
			for (int i = 0; i < appTerm.getParameters().length; i++) {
				if (appTerm.getParameters()[i] instanceof ApplicationTerm) {
					final ApplicationTerm disjunct = (ApplicationTerm) appTerm.getParameters()[i];
					if (disjunct.getFunction().getName().equals("and")) {
						// distributiciti
						final Term[] copy = new Term[appTerm.getParameters().length - 1];
						for (int k = 0, j = 0; k < appTerm.getParameters().length; k++) {
							if (k != i) {
								copy[j++] = appTerm.getParameters()[k];
							}
						}
						final Term paras = theory.or(copy);
						final Term lhs = theory.or(disjunct.getParameters()[0], paras);
						final Term rhsOR = theory.and(
								Arrays.copyOfRange(disjunct.getParameters(), 1, disjunct.getParameters().length));
						final Term rhs = theory.or(rhsOR, paras);
						newTerm = theory.and(lhs, rhs);
						enqueueWalker(new BuildApplicationTerm((ApplicationTerm) newTerm));
						pushTerm(lhs);
						pushTerm(rhs);
						setResult(newTerm);
						// setResult();
						return;
					}
				}
			}
		}
		if (newArgs != appTerm.getParameters()) {
			newTerm = theory.term(fun, newArgs);
		}
		setResult(newTerm);
	}
}
