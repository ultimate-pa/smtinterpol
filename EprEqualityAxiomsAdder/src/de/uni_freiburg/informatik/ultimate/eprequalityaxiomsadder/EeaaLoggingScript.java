package de.uni_freiburg.informatik.ultimate.eprequalityaxiomsadder;

import java.io.FileNotFoundException;
import java.math.BigInteger;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;

import de.uni_freiburg.informatik.ultimate.logic.LoggingScript;
import de.uni_freiburg.informatik.ultimate.logic.Logics;
import de.uni_freiburg.informatik.ultimate.logic.NoopScript;
import de.uni_freiburg.informatik.ultimate.logic.QuotedObject;
import de.uni_freiburg.informatik.ultimate.logic.SMTLIBException;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;

public class EeaaLoggingScript extends LoggingScript {
	
	public EeaaLoggingScript(Script script, String file, boolean autoFlush)
			throws FileNotFoundException {
		super(script, file, autoFlush);
		// TODO Auto-generated constructor stub
	}

	boolean mJustLeftDeclarations = true;
	
	String newEqualsSymbol = "EQ";

	private List<Sort> mDeclaredSorts = new ArrayList<Sort>();

	private Map<String, Sort[]> mDeclaredPredicates = new HashMap<String, Sort[]>();

	@Override
	public void setLogic(Logics logic) throws UnsupportedOperationException {
		// TODO Auto-generated method stub
		super.setLogic(logic);
	}
	
	

	@Override
	public void declareSort(String sort, int arity) throws SMTLIBException {
		super.declareSort(sort, arity);
		assert arity == 0;
		mDeclaredSorts.add(sort(sort));
	}



	@Override
	public void declareFun(String fun, Sort[] paramSorts, Sort resultSort) throws SMTLIBException {
		if (resultSort.getName().equals("Bool")) {
			assert !fun.equals(newEqualsSymbol) : "our new equals symbol is used for an epr predicate already";
			mDeclaredPredicates.put(fun, paramSorts);
		}
		super.declareFun(fun, paramSorts, resultSort);
	}

	@Override
	public void push(int levels) {
		if (! mJustLeftDeclarations) {
			super.push(levels);
		} else {
			echo(new QuotedObject("inserting equality axioms and declaration (begin)"));
			declareEq();
			insertAxioms();
			mJustLeftDeclarations = false;
			echo(new QuotedObject("inserting equality axioms and declaration (end)"));
			super.push(levels);
		}
	}

	@Override
	public LBool assertTerm(Term term) throws SMTLIBException {
		if (! mJustLeftDeclarations) {
			return super.assertTerm(term);
		} else {
			declareEq();
			insertAxioms();
			mJustLeftDeclarations = false;
			return super.assertTerm(term);
		}
	}



	@Override
	public Term term(String funcname, Term... params) throws SMTLIBException {
		if ("=".equals(funcname)) {
			return term(newEqualsSymbol, params);
		}
		return super.term(funcname, params);
	}



	@Override
	public Term term(String funcname, BigInteger[] indices, Sort returnSort, Term... params) throws SMTLIBException {
		if ("=".equals(funcname)) {
			return term(newEqualsSymbol, indices, returnSort, params);
		}
		return super.term(funcname, indices, returnSort, params);
	}



	private Term buildCongruenceAxiom(String predName, Sort[] predArgs) {
		TermVariable[] qVars1 = new TermVariable[predArgs.length];
		TermVariable[] qVars2 = new TermVariable[predArgs.length];
		TermVariable[] qVars = new TermVariable[predArgs.length * 2];
		for (int i = 0; i < predArgs.length; i++) {
			qVars1[i] = variable("x" + i, predArgs[i]);
			qVars2[i] = variable("y" + i, predArgs[i]);
			qVars[2*i] = qVars1[i];
			qVars[2*i + 1] = qVars2[i];
		}

		Term[] antecedentElements = new Term[predArgs.length];
		for (int i = 0; i < predArgs.length; i++) {
			antecedentElements[i] = term(newEqualsSymbol, qVars1[i], qVars2[i]);
		}
		assert antecedentElements.length > 0;
		Term antecedent = antecedentElements.length > 1 ? term("and", antecedentElements) : antecedentElements[0];
		return quantifier(FORALL, qVars, 
				term("=>", 
						antecedent,
						term("=>",
								term(predName, qVars1),
								term(predName, qVars2))));
	}



	private Term buildTransitivityAxiom(Sort s) {
		TermVariable qvar1 = variable("x", s);
		TermVariable qvar2 = variable("y", s);
		TermVariable qvar3 = variable("z", s);
		return quantifier(FORALL, 
				new TermVariable[] { qvar1, qvar2, qvar3 }, 
				term("=>", 
						term ("and", term(newEqualsSymbol, qvar1, qvar2), term(newEqualsSymbol, qvar2, qvar3)), 
						term(newEqualsSymbol, qvar1, qvar3)));

	}



	private Term buildSymmetryAxiom(Sort s) {
		TermVariable qvar1 = variable("x", s);
		TermVariable qvar2 = variable("y", s);
		return quantifier(FORALL, 
				new TermVariable[] { qvar1, qvar2 }, 
				term("=>", term(newEqualsSymbol, qvar1, qvar2), term(newEqualsSymbol, qvar1, qvar2)));
	}

	private Term buildReflAxiom(Sort s) {
		TermVariable qvar = variable("x", s);
		return quantifier(FORALL, new TermVariable[] { qvar }, term(newEqualsSymbol, qvar, qvar));
	}

	private void declareEq() {
		for (Sort ds : mDeclaredSorts) {
			super.declareFun(newEqualsSymbol, new Sort[] { ds, ds }, sort("Bool"));
		}
	}



	private void insertAxioms() {
		for (Sort ds : mDeclaredSorts) {
			super.assertTerm(buildReflAxiom(ds));
			super.assertTerm(buildSymmetryAxiom(ds));
			super.assertTerm(buildTransitivityAxiom(ds));
		}
		
		for (Entry<String, Sort[]> en : mDeclaredPredicates.entrySet()) {
			String predName = en.getKey();
			Sort[] predArgs = en.getValue();
			if (predArgs.length == 0) {
				continue;
			}
			super.assertTerm(buildCongruenceAxiom(predName, predArgs));
		}
		
	}

	
}
