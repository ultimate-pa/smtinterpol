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
package de.uni_freiburg.informatik.ultimate.smtinterpol.proofcheck;

import java.util.ArrayDeque;

import de.uni_freiburg.informatik.ultimate.logic.AnnotatedTerm;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.ConstantTerm;
import de.uni_freiburg.informatik.ultimate.logic.QuantifiedFormula;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.logic.Theory;

/**
 * This class is used to convert a substitution proof step (@eq).
 * 
 * NOTE: Currently substitution is applied only within ApplicationTerm.
 *       There are, however, methods for unpacking AnnotatedTerm and
 *       QuantifiedFormula. The latter was never tested, since it was not
 *       supported. For AnnotatedTerm, there was only the ':quoted' annotation,
 *       which must not be unpacked. So if there should be support for a new
 *       annotation, this case must be excluded.
 *       The places are marked with <quantifiers> and <annotations>,
 *       respectively.
 * 
 * @author Christian Schilling
 */
public class SubstitutionConverter extends AConverter {
	// <annotations> or <quantifiers>
	/*
	private static final int G_UNEXPANDED = 0;
	private static final int G_EXPANDED = 1;
	private static final int G_REPLACED = 2;
	*/
	
	/**
	 * @param appendable appendable to write the proof to
	 * @param theory the theory
	 * @param converter term converter
	 * @param simplifier computation simplifier
	 */
	public SubstitutionConverter(final Appendable appendable,
			final Theory theory, final TermConverter converter,
			final ComputationSimplifier simplifier) {
		super(appendable, theory, converter, simplifier);
	}
	
	/**
	 * This method converts a term with respect to a rewrite equality.
	 * All occurrences of the left-hand side term are replaced by the term
	 * on the right-hand side.
	 * Since the substitution may replace only parts of the original formula,
	 * the result must be computed.
	 * 
	 * @param origin term that is rewritten
	 * @param rewrite equality rule
	 * @return the term with substituted parts
	 */
	public Term convert(final Term origin, final ApplicationTerm rewrite) {
		assert ((rewrite.getFunction().getName() == "=")
				&& (rewrite.getParameters().length == 2));
		final Term lhs = rewrite.getParameters()[0];
		final Term rhs = rewrite.getParameters()[1];
		
		/*
		 * NOTE: This assertion is not relied on and should only detect useless
		 *       proof steps.
		 */
		assert (lhs != rhs) : "Rewrite has equal lhs and rhs.";
		
		// trivial case: whole formula is substituted
		if (origin == lhs) {
			return rhs;
		}
		
		// <annotations> or <quantifiers>: excluded, currently not reasonable
		if ((origin instanceof AnnotatedTerm)
				|| (origin instanceof QuantifiedFormula)) {
			throw new IllegalArgumentException(
					"AnnotatedTerm or QuantifiedFormula cannot be partially "
					+ "substituted in the current version.");
		}
		
		// compute substitution result
		final Term result = substitute(origin, lhs, rhs).getTerm();
		assert (result != null);
		
		return result;
	}
	
	/**
	 * This method substitutes every occurrence in the original term.
	 * To do this, the term is transformed into a term tree on-the-fly (see
	 * {@link ATermNode} for details regarding the tree) in a top-bottom manner
	 * using a stack. There are two possibilities:
	 * 
	 * 1) Whenever an occurrence of the pattern was found, the current path is
	 * pruned and the parent node is informed about a change in its child node.
	 * If all child nodes have been expanded, the parent node rewrites its own
	 * term to capture the substitution and recursively informs its own parent
	 * node.
	 * 
	 * 2) All child nodes expanded themselves to the leaf level. In this case
	 * the parent node needs not change its term and just must inform its
	 * parent node.
	 * 
	 * This way in the end the root node is reached again and the method
	 * terminates.
	 * 
	 * @param origin original term
	 * @param pattern pattern that is replaced
	 * @param replace term that is inserted for the pattern
	 * @return the root node, which contains the replaced formula
	 */
	private ATermNode substitute(final Term origin, final Term pattern,
			final Term replace) {
		ATermNode node;
		assert ((origin instanceof ApplicationTerm)
				|| (origin instanceof AnnotatedTerm)
				|| (origin instanceof QuantifiedFormula));
		if (origin instanceof ApplicationTerm) {
			node = new AppTermNode(null, (ApplicationTerm)origin);
		} else if (origin instanceof AnnotatedTerm) {
			// <annotations>
			assert false;
			return null;
			// node = new AnnotTermNode(null, (AnnotatedTerm)origin);
		} else {
			// <quantifiers>
			assert (origin instanceof QuantifiedFormula);
			assert false;
			return null;
			// node = new QuantTermNode(null, (QuantifiedFormula)origin);
		}
		
		final ArrayDeque<ATermNode> stack =
				new ArrayDeque<SubstitutionConverter.ATermNode>();
		stack.push(node);
		
		// search in the term tree and replace all occurrences of the pattern
		while (true) {
			node = stack.pop();
			final Term next = node.next();
			// no parameters left, finalize node
			if (next == null) {
				final ATermNode parent = node.mParent;
				// root node, stop
				if (parent == null) {
					break;
				} else {
					// go on with parent node; also inform about changes
					if (node.isNew()) {
						parent.replace(node.getTerm());
					}
					node = parent;
				}
			} else {
				// still parameters left
				// pattern fits, term is replaced
				if (next == pattern) {
					node.replace(replace);
				} else {
					// else a new node is constructed
					if (next instanceof ApplicationTerm) {
						node = new AppTermNode(node,
								(ApplicationTerm)next);
					} //NOCHECKSTYLE
					// <annotations>
					/*
					else if (next instanceof AnnotatedTerm) {
						node = new AnnotTermNode(node,
								(AnnotatedTerm)next);
					}
					*/
					// <quantifiers>
					/*
					else if (next instanceof QuantifiedFormula) {
						node = new QuantTermNode(node,
								(QuantifiedFormula)next);
					}
					*/
					// other terms should not occur or are not interesting
					else {
						assert ((next instanceof ConstantTerm)
								|| (next instanceof TermVariable)
								// <annotations>
								|| (next instanceof AnnotatedTerm)
								// <quantifiers>
								|| (next instanceof QuantifiedFormula)
								);
					}
				}
			}
			stack.push(node);
		}
		
		// root node with substitutions applied
		return node;
	}
	
	/**
	 * This class is used to construct an on-the-fly term tree.
	 * It contains the following information: its parent node, its term,
	 * if its term changed, and the next child node (only reasonable for an
	 * ApplicationTerm).
	 */
	private abstract class ATermNode {
		// parent node, null for the root
		ATermNode mParent;
		
		/**
		 * @param parent the parent node (null for root node)
		 */
		public ATermNode(final ATermNode parent) {
			mParent = parent;
		}
		
		/**
		 * This method indicates if the term has changed.
		 * 
		 * @return true iff term has changed
		 */
		abstract boolean isNew();
		
		/**
		 * This is the getter for the term. It returns the original term if no
		 * change occurred and the changed term otherwise.
		 * 
		 * @return the associated term
		 */
		abstract Term getTerm();
		
		/**
		 * This method returns the next child node or null if all of them have
		 * been visited. A child is the next parameter for an ApplicationTerm
		 * and the sub-term for an AnnotatedTerm or a QuantifiedFormula.
		 * 
		 * @return the next parameter if possible, null otherwise
		 */
		abstract Term next();
		
		/**
		 * This method replaces the current child node with the given term.
		 * 
		 * @param replace new parameter term
		 */
		abstract void replace(Term replace);
	}
	
	/**
	 * This class is represents an ApplicationTerm in the term tree.
	 */
	private class AppTermNode extends ATermNode {
		// associated term
		final ApplicationTerm mTerm;
		// next expanded parameter
		int mParams;
		// array of new parameters, null if no change occurred so far
		Term[] mReplace;
		
		/**
		 * @param parent the parent node (null for root node)
		 * @param term the associated term
		 */
		public AppTermNode(final ATermNode parent,
				final ApplicationTerm term) {
			super(parent);
			mTerm = term;
			mParams = term.getParameters().length;
			mReplace = null;
		}
		
		@Override
		boolean isNew() {
			return (mReplace != null);
		}
		
		@Override
		Term getTerm() {
			// no change, use old term
			if (mReplace == null) {
				return mTerm;
			} else {
				// inner term has changed, create new term
				// fill the parameter array (some elements may be null)
				final Term[] oldParams = mTerm.getParameters();
				for (int i = mReplace.length - 1; i >= 0; --i) {
					if (mReplace[i] == null) {
						mReplace[i] = oldParams[i];
					}
				}
				return mTheory.term(mTerm.getFunction(), mReplace);
			}
		}
		
		@Override
		Term next() {
			// finished expansion
			if (mParams == 0) {
				return null;
			} else {
				// still parameters to go
				assert (mParams > 0);
				return mTerm.getParameters()[--mParams];
			}
		}
		
		@Override
		void replace(final Term replace) {
			assert (replace != null);
			
			// no replacement before, initialize array
			if (mReplace == null) {
				mReplace = new Term[mTerm.getParameters().length];
			}
			mReplace[mParams] = replace;
		}
		
		@Override
		public String toString() {
			final StringBuilder builder = new StringBuilder();
			
			builder.append('{');
			builder.append(mTerm.toStringDirect());
			builder.append(", ");
			builder.append(Integer.toString(mParams));
			builder.append(", ");
			if (mReplace == null) {
				builder.append("null");
			} else {
				builder.append(mReplace);
			}
			builder.append('}');
			
			return builder.toString();
		}
	}
	
	// <annotations>
//	/**
//	 * This class is represents an AnnotatedTerm in the term tree.
//	 */
//	private class AnnotTermNode extends ATermNode {
//		// associated term
//		AnnotatedTerm m_term;
//		// status
//		int m_status;
//		
//		/**
//		 * @param parent the parent node (null for root node)
//		 * @param term the associated term
//		 */
//		public AnnotTermNode(final ATermNode parent,
//				final AnnotatedTerm term) {
//			super(parent);
//			m_term = term;
//			m_status = G_UNEXPANDED;
//		}
//		
//		@Override
//		boolean isNew() {
//			return (m_status == G_REPLACED);
//		}
//		
//		@Override
//		Term getTerm() {
//			return m_term;
//		}
//		
//		@Override
//		Term next() {
//			// sub-term already expanded
//			if (m_status != G_UNEXPANDED) {
//				return null;
//			}
//			// expand sub-term
//			else {
//				m_status = G_EXPANDED;
//				return m_term.getSubterm();
//			}
//		}
//		
//		@Override
//		void replace(final Term replace) {
//			assert ((m_status != G_REPLACED) && (replace != null));
//			m_status = G_REPLACED;
//			
//			m_term = (AnnotatedTerm)
//					m_theory.annotatedTerm(m_term.getAnnotations(), replace);
//		}
//		
//		@Override
//		public String toString() {
//			final StringBuilder builder = new StringBuilder();
//			
//			builder.append("{");
//			builder.append(m_term.toStringDirect());
//			builder.append(", ");
//			builder.append(m_status == G_UNEXPANDED ? "unexpanded" :
//				m_status == G_EXPANDED ? "expanded" : "changed");
//			builder.append("}");
//			
//			return builder.toString();
//		}
//	}
	
	// <quantifiers>
//	/**
//	 * This class is represents a QuantifiedFormula in the term tree.
//	 */
//	private class QuantTermNode extends ATermNode {
//		// associated term
//		QuantifiedFormula m_term;
//		// status
//		int m_status;
//		
//		/**
//		 * @param parent the parent node (null for root node)
//		 * @param term the associated term
//		 */
//		public QuantTermNode(final ATermNode parent,
//				final QuantifiedFormula term) {
//			super(parent);
//			m_term = term;
//			m_status = G_UNEXPANDED;
//		}
//		
//		@Override
//		boolean isNew() {
//			return (m_status == G_REPLACED);
//		}
//		
//		@Override
//		Term getTerm() {
//			return m_term;
//		}
//		
//		@Override
//		Term next() {
//			// sub-term already expanded
//			if (m_status != G_UNEXPANDED) {
//				return null;
//			}
//			// expand sub-term
//			else {
//				m_status = G_EXPANDED;
//				return m_term.getSubformula();
//			}
//		}
//		
//		@Override
//		void replace(final Term replace) {
//			assert ((m_status != G_REPLACED) && (replace != null));
//			m_status = G_REPLACED;
//			
//			if (m_term.getQuantifier() == QuantifiedFormula.EXISTS) {
//				m_term = (QuantifiedFormula)
//						m_theory.exists(m_term.getVariables(), replace);
//			}
//			else if (m_term.getQuantifier() == QuantifiedFormula.FORALL) {
//				m_term = (QuantifiedFormula)
//						m_theory.forall(m_term.getVariables(), replace);
//			}
//			else {
//				throw new UnsupportedOperationException(
//						"The quantifier is not supported.");
//			}
//		}
//		
//		@Override
//		public String toString() {
//			final StringBuilder builder = new StringBuilder();
//			
//			builder.append("{");
//			builder.append(m_term.toStringDirect());
//			builder.append(", ");
//			builder.append(m_status == G_UNEXPANDED ? "unexpanded" :
//				m_status == G_EXPANDED ? "expanded" : "changed");
//			builder.append("}");
//			
//			return builder.toString();
//		}
//	}
}
