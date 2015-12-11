package de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr;

import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.util.HashUtils;

public class TermTuple {

	public final int arity;
	public final Term[] terms;

	public TermTuple(Term[] terms, int arity) {
		this.terms = terms;
		this.arity = arity;
	}

	@Override
	public boolean equals(Object arg0) {
		if (!(arg0 instanceof TermTuple)) return false;
		TermTuple other = (TermTuple) arg0;
		if (other.arity != this.arity) return false;
		for (int i = 0; i < arity; i++) {
			if (other.terms[i].equals(this.terms[i])) return false;
		}
		return true;
	}

	@Override
	public int hashCode() {
		// TODO: double-check if this is a good hashing strategy
		return HashUtils.hashJenkins(31, (Object[]) terms);
	}

	@Override
	public String toString() {
		StringBuilder sb = new StringBuilder();
		sb.append("(");
		String comma = "";
		for (Term t : terms) {
			sb.append(comma + t.toString());
			comma = ", ";
		}
		sb.append("(");
		return sb.toString();
	}
}
