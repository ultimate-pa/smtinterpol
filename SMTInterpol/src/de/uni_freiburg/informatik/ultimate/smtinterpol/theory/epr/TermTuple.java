package de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.cclosure.CClosure;
import de.uni_freiburg.informatik.ultimate.util.HashUtils;

public class TermTuple {

	public final int arity;
	public final Term[] terms;

	public TermTuple(Term[] terms, int arity) {
		this.terms = terms;
		this.arity = arity;
	}

	public TermTuple(Term[] arguments) {
		this(arguments, arguments.length);
	}

	@Override
	public boolean equals(Object arg0) {
		if (!(arg0 instanceof TermTuple)) return false;
		TermTuple other = (TermTuple) arg0;
		if (other.arity != this.arity) return false;
		for (int i = 0; i < arity; i++) {
			if (!other.terms[i].equals(this.terms[i])) return false;
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
		sb.append(")");
		return sb.toString();
	}

//	/**
//	 * something like "is unifiable" i think..
//	 * @param tt
//	 * @param exceptedConstants
//	 * @return
//	 */
//	public boolean matches(TermTuple tt, HashMap<Integer, ArrayList<ApplicationTerm>> exceptedConstants) {
//		// TODO Auto-generated method stub
//		return false;
//	}
	
	
//	public HashMap<TermVariable, Term> match(TermTuple other) {
	public TTSubstitution match(TermTuple other) {
//		return match(other, new HashMap<TermVariable, Term>());
		return match(other, new TTSubstitution());
	}

	/**
	 * "this" must be a TermTuple over constants.
	 * @param other A TermTuple that may contain variables and constants
	 * @param newSubs a substitution that constrains the matching of variables
	 * @return a possibly more constrained substitution that is a unifier, null if there is no unifier
	 */
	public TTSubstitution match(
			TermTuple other,
			TTSubstitution subs) {
		assert this.arity == other.arity;

//		Term thisTerm = this.terms[0];
//		Term otherTerm = other.terms[0];
//
//		if (thisTerm.equals(otherTerm)) {
//			return new TermTuple(arguments)
//		} else if (otherTerm instanceof TermVariable) {
//
//		} else if (thisTerm instanceof TermVariable) {
//
//		} else return null;
	
		
//		HashMap<TermVariable, Term> resultSubs = 
//				new HashMap<TermVariable, Term>(subs);//TODO: probably remove this copying (inserted it just to be safe..)
		
		TermTuple thisTT = new TermTuple(terms);
		TermTuple otherTT = new TermTuple(other.terms);
		
		TTSubstitution resultSubs = subs; // TODO: or is a copy needed?
		for (int i = 0; i < this.terms.length; i++) {
//			Term thisTerm = this.terms[i];
//			Term otherTerm = other.terms[i];
			Term thisTerm = thisTT.terms[i];
			Term otherTerm = otherTT.terms[i];

			TermVariable tvTerm = null;
			Term termTerm = null;
			
			if (thisTerm.equals(otherTerm)) {
				//match -- > do nothing
				continue;
			} else if (otherTerm instanceof TermVariable) {
				tvTerm = (TermVariable) otherTerm;
				termTerm = thisTerm;
			} else if (thisTerm instanceof TermVariable) {
				tvTerm = (TermVariable) thisTerm;
				termTerm = otherTerm;
			} else {
				return null;
			}
			
			resultSubs.addSubs(tvTerm, termTerm);
				
//			Term substitute = subs.get(tvTerm);
//			if (substitute == null) {
//				Term trg = resultSubs.get(tvTerm);
//				if (trg == null) {
//					resultSubs.put((TermVariable) tvTerm, termTerm);
//				}  else if (trg != null && trg instanceof TermVariable) {
//					resultSubs.put((TermVariable) resultSubs.get(tvTerm), termTerm);
//				} else {
//					assert false : "not totally sure about this..";
//				return null;
//				}
//			} else if (thisTerm.equals(substitute)) {
//				//match -- > do nothing
//			} else {
//				return null; //no match
//			}
			
			thisTT = resultSubs.apply(thisTT);
			otherTT = resultSubs.apply(otherTT);
		}
//		assert this.applySubstitution(resultSubs).equals(other.applySubstitution(resultSubs)) 
		assert resultSubs.apply(this).equals(resultSubs.apply(other))
			: "the returned substitution should be a unifier";
		return resultSubs;
	}
	
	public boolean onlyContainsConstants() {
		//TODO cache
		boolean result = true;
		for (Term t : terms)
			result &= t.getFreeVars().length == 0;
		return result;
	}
	
	public TermTuple applySubstitution(HashMap<TermVariable, Term> sub) {
		Term[] newTerms = new Term[terms.length];
		for (int i = 0; i < newTerms.length; i++)
			if (terms[i] instanceof TermVariable
					&& sub.containsKey(terms[i]))
				newTerms[i] = sub.get(terms[i]);
			else
				newTerms[i] = terms[i];
		
		assert nonNull(newTerms) : "substitution created a null-entry";
		return new TermTuple(newTerms);
	}
	
	private boolean nonNull(Term[] trms) {
		for (Term t : trms)
			if (t == null)
				return false;
		return true;
	}
	
	public HashSet<TermVariable> getFreeVars() {
		HashSet<TermVariable> result = new HashSet<>();
		for (Term t : terms)
			if (t instanceof TermVariable)
				result.add((TermVariable) t);
		return result;
	}
	
	public boolean isGround() {
		return getFreeVars().size() == 0;
	}

	/**
	 * Are the possible instantiations of this TermTuple a superset of those of 
	 * the other TermTuple
	 * @param other
	 * @return
	 */
	public boolean isEqualOrMoreGeneralThan(TermTuple other) {
		for (int i = 0; i < terms.length; i++) {
			Term thisT = terms[i];
			Term otherT = other.terms[i];
			
			if (otherT instanceof TermVariable 
					&& !(thisT instanceof TermVariable)) {
				return false;
			}
		}
		if (this.getFreeVars().size() < other.getFreeVars().size())
			return false;
		//TODO: this is not yet a complete solution
		// example: P x x y , P x y y --> should say "no" here
		return true;
	}
}
