package de.uni_freiburg.informatik.ultimate.smtinterpol.scripts;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.ConstantTerm;
import de.uni_freiburg.informatik.ultimate.logic.FormulaUnLet;
import de.uni_freiburg.informatik.ultimate.logic.FunctionSymbol;
import de.uni_freiburg.informatik.ultimate.logic.NoopScript;
import de.uni_freiburg.informatik.ultimate.logic.SMTLIBException;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermTransformer;
import de.uni_freiburg.informatik.ultimate.smtinterpol.convert.SMTAffineTerm;

public class LinearArithmeticChecker extends NoopScript {
	
	FormulaUnLet mUnletter = new FormulaUnLet();
	LinearChecker mChecker = new LinearChecker();
	long issues = 0;
	
	@Override
	public LBool assertTerm(final Term term) throws SMTLIBException {
		mChecker.transform(mUnletter.transform(term));
		return super.assertTerm(term);
	}

	@Override
	public void exit() {
		if (issues > 0) {
			System.out.println("Found " + issues + " problems.");
			System.exit(1);
		}
	}
	
	class LinearChecker extends TermTransformer {
		
		@Override
		public void convertApplicationTerm(ApplicationTerm appTerm, Term[] newArgs) {
			FunctionSymbol fs = appTerm.getFunction();
			if (fs.isIntern()) {
				switch (fs.getName()) {
				case "abs":
				case "mod":
				case "div":
					System.out.println("Non-linear function " + fs.getName() + " in benchmark");
					issues++;
					break;
				case "*": {
					Term leftArg = SMTAffineTerm.parseConstant(newArgs[0]);
					Term rightArg = SMTAffineTerm.parseConstant(newArgs[1]);
					if (newArgs.length != 2
							|| (!(leftArg instanceof ConstantTerm) && !(rightArg instanceof ConstantTerm))) {
						System.out.println("Non-linear term " + appTerm);
						issues++;
					}
					break;
				}
				case "/": {
					Term constant = SMTAffineTerm.parseConstant(appTerm);
					if (!(constant instanceof ConstantTerm)) {
						System.out.println("Non-constant division: " + appTerm);
						issues++;
					}
					break;
				}
				default:
					break;
				}
			}
			super.convertApplicationTerm(appTerm, newArgs);
		}
	}
}
