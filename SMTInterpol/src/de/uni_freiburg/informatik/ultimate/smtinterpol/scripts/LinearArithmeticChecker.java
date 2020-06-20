/*
 * Copyright (C) 2020 University of Freiburg
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
