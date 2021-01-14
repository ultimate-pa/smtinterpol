package de.uni_freiburg.informatik.ultimate.smtinterpol.theory.bitvector;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.ConstantTerm;
import de.uni_freiburg.informatik.ultimate.logic.FunctionSymbol;
import de.uni_freiburg.informatik.ultimate.logic.SMTLIBException;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermTransformer;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.logic.Theory;

public class CleanTransfomer extends TermTransformer {

	@Override
	public void convert(final Term term) {
		if ((term instanceof ConstantTerm) || (term instanceof TermVariable)) {
			setResult(term);
			return;
		}
		if (term instanceof ApplicationTerm) {
			final ApplicationTerm appTerm = (ApplicationTerm) term;

			enqueueWalker(new BuildApplicationTerm(appTerm));
			pushTerms(appTerm.getParameters());
			return;

		} else {
			throw new SMTLIBException("Not supported Term");
		}
		// super.convert(term);
	}

	@Override
	public void convertApplicationTerm(final ApplicationTerm appTerm, final Term[] newArgs) {
		// ersetzt appterm durch setResult
		Term newTerm = appTerm;

		final FunctionSymbol fun = appTerm.getFunction();
		final Theory theory = fun.getTheory();
		if (fun.getName().equals("or")) {
			for (int i = 0; i < appTerm.getParameters().length; i++) {
				if (appTerm.getParameters()[i] instanceof ApplicationTerm) {
					final ApplicationTerm disjunct = (ApplicationTerm) appTerm.getParameters()[i];
					if (disjunct.getFunction().getName().equals("or")) {
						final Term[] subforms =
								new Term[disjunct.getParameters().length + appTerm.getParameters().length];
						System.arraycopy(disjunct.getParameters(), 0, subforms, 0, disjunct.getParameters().length);
						System.arraycopy(appTerm.getParameters(), 0, subforms, disjunct.getParameters().length,
								appTerm.getParameters().length);
						newTerm = theory.or(subforms);
						pushTerm(newTerm);
						setResult(newTerm);
						return;
					}
				}
			}
		} else if (fun.getName().equals("and")) {
			for (int i = 0; i < appTerm.getParameters().length; i++) {
				if (appTerm.getParameters()[i] instanceof ApplicationTerm) {
					final ApplicationTerm disjunct = (ApplicationTerm) appTerm.getParameters()[i];
					if (disjunct.getFunction().getName().equals("and")) {
						final Term[] subforms =
								new Term[disjunct.getParameters().length + appTerm.getParameters().length];
						System.arraycopy(disjunct.getParameters(), 0, subforms, 0, disjunct.getParameters().length);
						System.arraycopy(appTerm.getParameters(), 0, subforms, disjunct.getParameters().length,
								appTerm.getParameters().length);
						newTerm = theory.and(subforms);
						pushTerm(newTerm);
						setResult(newTerm);
						return;
					}
				}
			}
		}
		newTerm = theory.term(fun, newArgs);
		setResult(newTerm);
	}
}
