package de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.logic.Theory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.Clause;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.Literal;
import de.uni_freiburg.informatik.ultimate.smtinterpol.proof.ProofNode;
import de.uni_freiburg.informatik.ultimate.smtinterpol.proof.ResolutionNode;

public class EprClause extends Clause {
	
	Literal[] eprEqualityLiterals;
	Literal[] eprPredicateLiterals;
	Literal[] nonEprLiterals;
	
	Theory mTheory;

	HashMap<TermVariable, ArrayList<ApplicationTerm>> mExceptedPoints = new HashMap<TermVariable, ArrayList<ApplicationTerm>>();
	HashMap<Literal, HashMap<Integer, ArrayList<ApplicationTerm>>>	mExceptedPointsPerLiteral = 
			new HashMap<Literal, HashMap<Integer, ArrayList<ApplicationTerm>>>();

	public EprClause(Literal[] literals, Theory theory) {
		super(literals);
		mTheory = theory;
		sortEprLiterals(literals);
	}

	public EprClause(Literal[] literals, ProofNode proof, Theory theory) {
		super(literals, proof);
		mTheory = theory;
		sortEprLiterals(literals);
	}

	public EprClause(Literal[] literals, int stacklevel, Theory theory) {
		super(literals, stacklevel);
		mTheory = theory;
		sortEprLiterals(literals);
	}

	public EprClause(Literal[] literals, ResolutionNode proof, int stacklevel, Theory theory) {
		super(literals, proof, stacklevel);
		mTheory = theory;
		sortEprLiterals(literals);
	}

	private void sortEprLiterals(Literal[] literals) {
		int noEqualities = 0;
		int noPredicates = 0;
		int noOthers = 0;
		//TODO: is this (counting then making arrays) more efficient than using a list?
		for (Literal l : literals) {
			if (l.getAtom() instanceof EprEqualityAtom) {
				//TODO: this assert is probably too strict: we have to allow disequalities between quantified variables, right?
				assert l.getSign() == 1 : "Destructive equality reasoning should have eliminated this literal.";
				noEqualities++;
			} else if (l.getAtom() instanceof EprPredicateAtom) {
				noPredicates++;
			} else {
				noOthers++;
			}
		}
		
		eprEqualityLiterals = new Literal[noEqualities];
		eprPredicateLiterals = new Literal[noPredicates];
		nonEprLiterals = new Literal[noOthers];

		//TODO: reusing the counter as array index may be unnecessarily confusing..
		for (Literal l : literals) {
			if (l.getAtom() instanceof EprEqualityAtom) {
				eprEqualityLiterals[--noEqualities] = l;
			} else if (l.getAtom() instanceof EprPredicateAtom) {
				if (((EprPredicateAtom) l.getAtom()).isQuantified) {
					// Have the EprPredicates point to the clauses and literals they occur in.
					EprPredicate pred = ((EprPredicateAtom) l.getAtom()).eprPredicate;
					pred.addQuantifiedOccurence(l, this);
				}
				eprPredicateLiterals[--noPredicates] = l;
			} else {
				nonEprLiterals[--noOthers] = l;
			}
		}		
		
		for (Literal l : eprEqualityLiterals) {
			Term p0 = ((ApplicationTerm) ((EprEqualityAtom) l.getAtom()).mTerm).getParameters()[0];
			Term p1 = ((ApplicationTerm) ((EprEqualityAtom) l.getAtom()).mTerm).getParameters()[1];
			if (p0 instanceof TermVariable && p1 instanceof TermVariable) {
				throw new UnsupportedOperationException("todo: implement");
			} else if (p0 instanceof TermVariable) {
				updateExceptedPoints((TermVariable) p0, (ApplicationTerm) p1);
			} else if (p1 instanceof TermVariable) {
				updateExceptedPoints((TermVariable) p1, (ApplicationTerm) p0);
			} else {
				assert false: "this equation should have gone to CClosure Theory: " + l.getAtom();
			}
		}
		
		for (Literal l : eprPredicateLiterals) {
				updateExceptedPointsPerLiteral(l);
		}
	}

	private void updateExceptedPointsPerLiteral(Literal l) {
		HashMap<Integer, ArrayList<ApplicationTerm>> perLiteral = mExceptedPointsPerLiteral.get(l);
		if (perLiteral == null) {
			perLiteral = new HashMap<>();
			mExceptedPointsPerLiteral.put(l, perLiteral);
		}
		
		ApplicationTerm at = (ApplicationTerm) ((EprAtom) l.getAtom()).mTerm;
		for (int i = 0; i < at.getParameters().length; i++) {
			Term p = at.getParameters()[i];
			if (p instanceof TermVariable) {
				ArrayList<ApplicationTerm> exceptions = mExceptedPoints.get(p);
				perLiteral.put(i, exceptions);
			}
		}
	}

	private void updateExceptedPoints(TermVariable tv, ApplicationTerm at) {
		ArrayList<ApplicationTerm> exceptions = mExceptedPoints.get(tv);
		if (exceptions == null) {
			exceptions = new ArrayList<>();
			mExceptedPoints.put(tv, exceptions);
		}
		exceptions.add(at);
	}
	
	/**
	 * Checks if this clause is fulfilled in the current decide state wrt. the EPR theory.
	 * @return null if this clause is fulfilled, a conflict clause otherwise
	 */
	public Clause check() {

		ArrayDeque<HashSet<TermTuple>> conflictPointSets = new ArrayDeque<>();
		
		for (Literal l : eprPredicateLiterals) {
			EprPredicateAtom epa = (EprPredicateAtom) l.getAtom();
			EprPredicate ep = epa.eprPredicate;
			
			HashSet<TermTuple> potentialConflictPoints = l.getSign() == 1 ?
					ep.mNegativelySetPoints :
						ep.mPositivelySetPoints;
			
			conflictPointSets.add(potentialConflictPoints);
		}
		
		//TODO: take excepted points into account
		
		ArrayDeque<TermTuple> pointsFromLiterals = computePointsFromLiterals(eprPredicateLiterals);
		


		ArrayList<ArrayList<TermTuple>> instantiations = computeInstantiations(
				new ArrayList<ArrayList<TermTuple>>(), 
				conflictPointSets,
				pointsFromLiterals,
				new HashMap<TermVariable, ApplicationTerm>(),
				true);

		// if there is a fitting instantiation, it directly induces a conflict clause
		if (instantiations.isEmpty()) {
			return null;
		} else {
			ArrayList<EprPredicate> predicates = computePredicatesFromLiterals(eprPredicateLiterals);
			ArrayList<Boolean> polaritites = computePolaritiesFromLiterals(eprPredicateLiterals);
			return clauseFromInstantiation(predicates, instantiations.get(0), polaritites); 
		}
	}

	private Clause clauseFromInstantiation(ArrayList<EprPredicate> predicates, 
			ArrayList<TermTuple> points,
			ArrayList<Boolean> polarities) {
//		ArrayList<EprPredicateAtom> result = new ArrayList<EprPredicateAtom>();
		ArrayList<Literal> result = new ArrayList<Literal>();
		for (int i = 0; i < predicates.size(); i++) {
//			EprPredicateAtom epa = new EprPredicateAtom(
//					mTheory.term(predicates.get(i).functionSymbol, points.get(i).terms), 
//					0, 0, predicates.get(i));//TODO replace 0, 0
			EprPredicateAtom epa = predicates.get(i).getAtomForPoint(points.get(i));

			result.add(polarities.get(i) ? epa
							:epa.negate());
		}

		return new Clause(result.toArray(new Literal[result.size()]));
	}

	private ArrayList<EprPredicate> computePredicatesFromLiterals(Literal[] eprPredicateLiterals2) {
		//TODO cache/precompute this
		ArrayList<EprPredicate> result = new ArrayList<EprPredicate>();
		for (Literal l : eprPredicateLiterals2) {
			result.add(((EprPredicateAtom) l.getAtom()).eprPredicate);
		}
		return result;
	}

	private ArrayList<Boolean> computePolaritiesFromLiterals(Literal[] eprPredicateLiterals2) {
		//TODO cache/precompute this
		ArrayList<Boolean> result = new ArrayList<Boolean>();
		for (Literal l : eprPredicateLiterals2) {
			result.add(l.getSign() == 1);
		}
		return result;
	}
	private ArrayDeque<TermTuple> computePointsFromLiterals(Literal[] predicateLiterals) {
		//TODO cache/precompute this
		ArrayDeque<TermTuple> result = new ArrayDeque<>();
		for (Literal l : predicateLiterals) {
			result.add(
					new TermTuple(
							((ApplicationTerm) 
									((EprPredicateAtom) l.getAtom()).mTerm)
							.getParameters()));
			
		}
		return result;
	}

	/**
	 *  compute a filtered cross product
	 * @param pointsFromLiterals 
	 */
	private ArrayList<ArrayList<TermTuple>> computeInstantiations(
			ArrayList<ArrayList<TermTuple>> instantiations,
			ArrayDeque<HashSet<TermTuple>> conflictPointSets, 
			ArrayDeque<TermTuple> pointsFromLiterals,
			HashMap<TermVariable, ApplicationTerm> substitution,
			boolean isFirstCall) {
		//TODO: might be better to rework this as NonRecursive
		
//		if (instantiations.isEmpty() && !isFirstCall)
//			return instantiations;
		if (conflictPointSets.isEmpty())
			return instantiations;

		HashSet<TermTuple> currentPoints = conflictPointSets.pollFirst();
		TermTuple currentPfl = pointsFromLiterals.pollFirst();
		
//		if (currentPoints.isEmpty())
//			return new ArrayList<ArrayList<TermTuple>>();
		
		//if the toMatch part is constant, it only trivially matches itself.. //seems bullshit..
//		if (currentPfl.onlyContainsConstants()) {
//			//TODO: is there a nicer way?
//			currentPoints = new HashSet<>();
//			currentPoints.add(currentPfl);
//		}
		
		for (TermTuple tt : currentPoints) {
			HashMap<TermVariable, ApplicationTerm> newSubs = new HashMap<TermVariable, ApplicationTerm>(substitution);
			newSubs = tt.match(currentPfl, newSubs);
			if (newSubs != null) {
				ArrayList<ArrayList<TermTuple>> instantiationsNew = new ArrayList<ArrayList<TermTuple>>();
				if (isFirstCall) {
					ArrayList<TermTuple> l = new ArrayList<TermTuple>();
					l.add(tt);
					instantiationsNew.add(l);
				} else {
					for (ArrayList<TermTuple> in : instantiations) {
						ArrayList<TermTuple> inNew = new ArrayList<>(in);
						inNew.add(tt);
						instantiationsNew.add(inNew);
					}
				}
//				instantiations.addAll(
				return computeInstantiations(
//								new ArrayList<ArrayList<TermTuple>>(instantiations), 
								instantiationsNew,
								new ArrayDeque<HashSet<TermTuple>>(conflictPointSets),
								new ArrayDeque<TermTuple>(pointsFromLiterals),
								newSubs,
								false
						);
			}
		}
		return new ArrayList<ArrayList<TermTuple>>();
//		return instantiations;
//		return null;
	}
}
