package de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.atoms;

import java.util.Arrays;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.Theory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.convert.SharedTerm;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.DPLLAtom;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.TermTuple;

/**
 * Represents an Atom that is known to the EprTheory.
 * Note that, although this class inherits from DPLLAtom, only some EprAtoms are known to 
 * the DPLLEngine, namely those that are of the form "(P c_1 ... c_n)" where P is an 
 * uninterpreted predicate and the c_i are constants. In contrast, every EprAtom that contains
 * a TermVariable is only known to the EprTheory.
 * 
 * @author Alexander Nutz
 *
 */
public abstract class EprAtom extends DPLLAtom {
	
	protected final Term mTerm;
	private TermTuple mArgsAsTermTuple = null;

	public EprAtom(Term term, int hash, int assertionstacklevel) {
		super(hash, assertionstacklevel);
		this.mTerm = term;
	}

	public Term[] getArguments() {
		return ((ApplicationTerm) mTerm).getParameters();
	}
	
	public TermTuple getArgumentsAsTermTuple() {
		if (mArgsAsTermTuple == null)
			mArgsAsTermTuple = new TermTuple(this.getArguments());
		return mArgsAsTermTuple;
	}

	@Override
	public String toString() {
		String res =  mTerm.toStringDirect();
		if (res.contains("AUX")) {
			EprPredicateAtom predAtom = (EprPredicateAtom) this;
			return "(AUX " + predAtom.getEprPredicate().hashCode() + " " + Arrays.toString(((ApplicationTerm) mTerm).getParameters()) + ")";
		}
		return res;
	}
	
	public Term getTerm() {
		return mTerm;
	}
}
