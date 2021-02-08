package de.uni_freiburg.informatik.ultimate.smtinterpol.theory.bitvector;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.ConstantTerm;
import de.uni_freiburg.informatik.ultimate.logic.FunctionSymbol;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermTransformer;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.logic.Theory;

public class NnfTransformer extends TermTransformer {

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
		Term newTerm = appTerm;
		final FunctionSymbol fun = appTerm.getFunction();
		// if(fun.getName().equals("and"))
		final Theory theory = fun.getTheory();
		if (fun.getName().equals("not")) {
			if (appTerm.getParameters()[0] instanceof ApplicationTerm) {
				final ApplicationTerm negTerm = (ApplicationTerm) newArgs[0];
				if (negTerm.getFunction().getName().equals("and")) {
					final Term[] negated = new Term[negTerm.getParameters().length];
					for (int i = 0; i < negTerm.getParameters().length; i++) {
						negated[i] = theory.not(negTerm.getParameters()[i]);
					}
					newTerm = theory.or(negated);
					enqueueWalker(new BuildApplicationTerm((ApplicationTerm) newTerm));
					pushTerms(negated);
					setResult(newTerm);
					return;
				} else if (negTerm.getFunction().getName().equals("or")) {
					final Term[] negated = new Term[negTerm.getParameters().length];
					for (int i = 0; i < negTerm.getParameters().length; i++) {
						negated[i] = theory.not(negTerm.getParameters()[i]);
					}
					newTerm = theory.and(negated);
					enqueueWalker(new BuildApplicationTerm((ApplicationTerm) newTerm));
					pushTerms(negated);
					setResult(newTerm);
					return;
				} else if (negTerm.getFunction().getName().equals("not")) {
					setResult(negTerm.getParameters()[0]);
					return;
				}
			}
		}
		if (newArgs != appTerm.getParameters()) {
			newTerm = theory.term(fun, newArgs);
		}
		setResult(newTerm);
	}

}