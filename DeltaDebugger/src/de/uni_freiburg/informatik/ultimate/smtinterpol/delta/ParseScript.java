/*
 * Copyright (C) 2012-2013 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.smtinterpol.delta;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.logic.Assignments;
import de.uni_freiburg.informatik.ultimate.logic.Logics;
import de.uni_freiburg.informatik.ultimate.logic.Model;
import de.uni_freiburg.informatik.ultimate.logic.NoopScript;
import de.uni_freiburg.informatik.ultimate.logic.SMTLIBException;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;

public class ParseScript extends NoopScript {
	
	private final List<Cmd> mCmds = new ArrayList<Cmd>();
	
	public List<Cmd> getCmds() {
		return mCmds;
	}

	@Override
	public void setLogic(Logics logic) throws UnsupportedOperationException {
		super.setLogic(logic);
		mCmds.add(new SetLogic(logic));
	}

	@Override
	public void setOption(String opt, Object value)
		throws UnsupportedOperationException, SMTLIBException {
		mCmds.add(new SetterCmd("set-option", opt, value));
	}

	@Override
	public void setInfo(String info, Object value) {
		mCmds.add(new SetterCmd("set-info", info, value));
	}

	@Override
	public void declareSort(String sort, int arity) throws SMTLIBException {
		super.declareSort(sort, arity);
		mCmds.add(new DeclareSort(sort, arity));
	}

	@Override
	public void defineSort(String sort, Sort[] sortParams, Sort definition)
		throws SMTLIBException {
		super.defineSort(sort, sortParams, definition);
		mCmds.add(new DefineSort(sort, sortParams, definition));
	}

	@Override
	public void declareFun(String fun, Sort[] paramSorts, Sort resultSort)
		throws SMTLIBException {
		super.declareFun(fun, paramSorts, resultSort);
		mCmds.add(new DeclareFun(fun, paramSorts, resultSort));
	}

	@Override
	public void defineFun(String fun, TermVariable[] params, Sort resultSort,
			Term definition) throws SMTLIBException {
		super.defineFun(fun, params, resultSort, definition);
		mCmds.add(new DefineFun(fun, params, resultSort, definition));
	}

	@Override
	public void push(int levels) {
		super.push(levels);
		mCmds.add(new ScopeCmd("push", levels));
	}

	@Override
	public void pop(int levels) throws SMTLIBException {
		super.pop(levels);
		mCmds.add(new ScopeCmd("pop", levels));
	}

	@Override
	public LBool assertTerm(Term term) throws SMTLIBException {
		mCmds.add(new OneTermCmd("assert", term));
		return LBool.UNKNOWN;
	}

	@Override
	public LBool checkSat() {
		mCmds.add(new SimpleCmd("check-sat"));
		return LBool.UNKNOWN;
	}

	@Override
	public Term[] getAssertions() throws SMTLIBException { // NOPMD
		mCmds.add(new SimpleCmd("get-assertions"));
		return null;
	}

	@Override
	public Term getProof() throws SMTLIBException,
			UnsupportedOperationException {
		mCmds.add(new SimpleCmd("get-proof"));
		return null;
	}

	@Override
	public Term[] getUnsatCore() throws SMTLIBException,// NOPMD
			UnsupportedOperationException {
		mCmds.add(new SimpleCmd("get-unsat-core"));
		return null;
	}

	@Override
	public Map<Term, Term> getValue(Term[] terms) throws SMTLIBException,
			UnsupportedOperationException {
		mCmds.add(new TermListCmd("get-value", terms));
		return null;
	}

	@Override
	public Assignments getAssignment() throws SMTLIBException,
			UnsupportedOperationException {
		mCmds.add(new SimpleCmd("get-assignments"));
		return null;
	}

	@Override
	public Object getOption(String opt) throws UnsupportedOperationException {
		mCmds.add(new GetterCmd("get-option", opt));
		return null;
	}

	@Override
	public Object getInfo(String info) throws UnsupportedOperationException {
		mCmds.add(new GetterCmd("get-info", info));
		return null;
	}

	@Override
	public Term simplify(Term term) throws SMTLIBException {
		mCmds.add(new OneTermCmd("simplify", term));
		return null;
	}

	@Override
	public Term[] getInterpolants(// NOPMD
			Term[] partition, int[] startOfSubtree)
		throws SMTLIBException, UnsupportedOperationException {
		mCmds.add(new GetInterpolants(partition, startOfSubtree));
		return null;
	}

	@Override
	public void exit() {
		mCmds.add(new SimpleCmd("exit"));
	}

	@Override
	public Model getModel() throws SMTLIBException,
			UnsupportedOperationException {
		mCmds.add(new SimpleCmd("exit"));
		return null;
	}

	@Override
	public Iterable<Term[]> checkAllsat(Term[] predicates)
		throws SMTLIBException, UnsupportedOperationException {
		mCmds.add(new TermListCmd("check-allsat", predicates));
		return null;
	}
	
}
