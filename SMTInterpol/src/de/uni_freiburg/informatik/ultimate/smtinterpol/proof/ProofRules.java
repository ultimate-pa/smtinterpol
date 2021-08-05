package de.uni_freiburg.informatik.ultimate.smtinterpol.proof;

import java.util.HashSet;

import de.uni_freiburg.informatik.ultimate.logic.AnnotatedTerm;
import de.uni_freiburg.informatik.ultimate.logic.Annotation;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.PrintTerm;
import de.uni_freiburg.informatik.ultimate.logic.SMTLIBConstants;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.Theory;

public class ProofRules {
	public final static String RES = "res";
	public final static String ASSUME = "assume";
	public final static String FALSEE = "false-";
	public final static String TRUEI = "true+";
	public final static String NOTI = "not+";
	public final static String NOTE = "not-";
	public final static String ORI = "or+";
	public final static String ORE = "or-";
	public final static String ANDI = "and+";
	public final static String ANDE = "and-";
	public final static String IMPI = "=>+";
	public final static String IMPE = "=>-";
	public final static String IFFI1 = "=+1";
	public final static String IFFI2 = "=+2";
	public final static String IFFE1 = "=-1";
	public final static String IFFE2 = "=-2";
	public final static String XORI = "xor+";
	public final static String XORE = "xor-";
	public final static String FORALLI = "forall+";
	public final static String FORALLE = "forall-";
	public final static String EXISTSI = "exists+";
	public final static String EXISTSE = "exists-";
	// equality chains of length >=3
	public final static String EQI = "=+";
	public final static String EQE = "=-";
	public final static String DISTINCTI = "distinct+";
	public final static String DISTINCTE = "distinct-";

	public final static String ITE1 = "ite1";
	public final static String ITE2 = "ite2";
	public final static String REFL = "refl";
	public final static String SYMM = "symm";
	public final static String TRANS = "trans";
	public final static String CONG = "cong";
	public final static String EXPAND = "expand";
	public final static String DELANNOT = "del!";
	/**
	 * sort name for proofs.
	 */
	public final static String PROOF = "Proof";

	public final static String PREFIX = "..";

	public final static String ANNOT_VARS = ":vars";
	public final static String ANNOT_VALUES = ":values";
	public final static String ANNOT_POS = ":pos";
	public final static String ANNOT_UNIT = ":unit";

	public static void setupTheory(final Theory t) {

		if (t.getDeclaredSorts().containsKey(PREFIX + PROOF)) {
			return;
		}

		t.declareInternalSort(PREFIX + PROOF, 0, 0);
		final Sort proofSort = t.getSort(PREFIX + PROOF);
		final Sort boolSort = t.getBooleanSort();
		final Sort[] generic = t.createSortVariables("X");
		final Sort[] proof1 = new Sort[] { proofSort };
		final Sort[] bool1 = new Sort[] { boolSort };
		final Sort[] bool3 = new Sort[] { boolSort, boolSort, boolSort };
		final Sort[] sort0 = new Sort[0];

		t.declareInternalFunction(PREFIX + RES, new Sort[] { boolSort, proofSort, proofSort }, proofSort, 0);
		t.declareInternalFunction(PREFIX + ASSUME, bool1, proofSort, 0);
		t.declareInternalFunction(PREFIX + FALSEE, sort0, proofSort, 0);
		t.declareInternalFunction(PREFIX + TRUEI, sort0, proofSort, 0);
		t.declareInternalFunction(PREFIX + NOTI, bool1, proofSort, 0);
		t.declareInternalFunction(PREFIX + NOTE, bool1, proofSort, 0);
		t.declareInternalFunction(PREFIX + ORI, bool1, proofSort, 0);
		t.declareInternalFunction(PREFIX + ORE, bool1, proofSort, 0);
		t.declareInternalFunction(PREFIX + ANDI, bool1, proofSort, 0);
		t.declareInternalFunction(PREFIX + ANDE, bool1, proofSort, 0);
		t.declareInternalFunction(PREFIX + IMPI, bool1, proofSort, 0);
		t.declareInternalFunction(PREFIX + IMPE, bool1, proofSort, 0);
		t.declareInternalFunction(PREFIX + IFFI1, bool1, proofSort, 0);
		t.declareInternalFunction(PREFIX + IFFI2, bool1, proofSort, 0);
		t.declareInternalFunction(PREFIX + IFFE1, bool1, proofSort, 0);
		t.declareInternalFunction(PREFIX + IFFE2, bool1, proofSort, 0);
		t.declareInternalFunction(PREFIX + XORI, bool3, proofSort, 0);
		t.declareInternalFunction(PREFIX + XORE, bool3, proofSort, 0);
		t.declareInternalFunction(PREFIX + FORALLI, bool1, proofSort, 0);
		t.declareInternalFunction(PREFIX + FORALLE, bool1, proofSort, 0);
		t.declareInternalFunction(PREFIX + EXISTSI, bool1, proofSort, 0);
		t.declareInternalFunction(PREFIX + EXISTSE, bool1, proofSort, 0);
		t.declareInternalFunction(PREFIX + EQI, bool1, proofSort, 0);
		t.declareInternalFunction(PREFIX + EQE, bool1, proofSort, 0);
		t.declareInternalFunction(PREFIX + DISTINCTI, bool1, proofSort, 0);
		t.declareInternalFunction(PREFIX + DISTINCTE, bool1, proofSort, 0);
		t.declareInternalPolymorphicFunction(PREFIX + ITE1, generic, generic, proofSort, 0);
		t.declareInternalPolymorphicFunction(PREFIX + ITE2, generic, generic, proofSort, 0);
		t.declareInternalPolymorphicFunction(PREFIX + REFL, generic, generic, proofSort, 0);
		t.declareInternalFunction(PREFIX + SYMM, bool1, proofSort, 0);
		t.declareInternalFunction(PREFIX + TRANS, bool1, proofSort, 0);
		t.declareInternalFunction(PREFIX + CONG, bool1, proofSort, 0);
		t.declareInternalPolymorphicFunction(PREFIX + EXPAND, generic, generic, proofSort, 0);
		t.declareInternalFunction(PREFIX + DELANNOT, bool1, proofSort, 0);
	}

	public static Term resolutionRule(final Term pivot, final Term proofPos, final Term proofNeg) {
		final Theory t = pivot.getTheory();
		return t.term(PREFIX + RES, pivot, proofPos, proofNeg);
	}

	public static Term asserted(final Term t) {
		return t.getTheory().term(PREFIX + ASSUME, t);
	}

	public static Term trueIntro(final Theory t) {
		return t.term(PREFIX + TRUEI);
	}

	public static Term falseElim(final Theory t) {
		return t.term(PREFIX + FALSEE);
	}

	public static Term notIntro(final Term notTerm) {
		assert ((ApplicationTerm) notTerm).getFunction().getName() == SMTLIBConstants.NOT;
		final Theory t = notTerm.getTheory();
		return t.term(PREFIX + NOTI, notTerm);
	}

	public static Term notElim(final Term notTerm) {
		assert ((ApplicationTerm) notTerm).getFunction().getName() == SMTLIBConstants.NOT;
		final Theory t = notTerm.getTheory();
		return t.term(PREFIX + NOTE, notTerm);
	}

	public static Term orIntro(final int pos, final Term orTerm) {
		assert ((ApplicationTerm) orTerm).getFunction().getName() == SMTLIBConstants.OR;
		final Theory t = orTerm.getTheory();
		return t.term(PREFIX + ORI, t.annotatedTerm(new Annotation[] { new Annotation(ANNOT_POS, pos) }, orTerm));
	}

	public static Term orElim(final Term orTerm) {
		assert ((ApplicationTerm) orTerm).getFunction().getName() == SMTLIBConstants.OR;
		final Theory t = orTerm.getTheory();
		return t.term(PREFIX + ORE, orTerm);
	}

	public static Term andIntro(final Term andTerm) {
		assert ((ApplicationTerm) andTerm).getFunction().getName() == SMTLIBConstants.AND;
		final Theory t = andTerm.getTheory();
		return t.term(PREFIX + ANDI, andTerm);
	}

	public static Term andElim(final int pos, final Term andTerm) {
		assert ((ApplicationTerm) andTerm).getFunction().getName() == SMTLIBConstants.AND;
		final Theory t = andTerm.getTheory();
		return t.term(PREFIX + ANDE, t.annotatedTerm(new Annotation[] { new Annotation(ANNOT_POS, pos) }, andTerm));
	}

	public static Term impIntro(final int pos, final Term impTerm) {
		assert ((ApplicationTerm) impTerm).getFunction().getName() == SMTLIBConstants.IMPLIES;
		final Theory t = impTerm.getTheory();
		return t.term(PREFIX + IMPI, t.annotatedTerm(new Annotation[] { new Annotation(ANNOT_POS, pos) }, impTerm));
	}

	public static Term impElim(final Term impTerm) {
		assert ((ApplicationTerm) impTerm).getFunction().getName() == SMTLIBConstants.IMPLIES;
		final Theory t = impTerm.getTheory();
		return t.term(PREFIX + IMPE, impTerm);
	}

	public static Term iffIntro1(final Term iffTerm) {
		assert ((ApplicationTerm) iffTerm).getFunction().getName() == SMTLIBConstants.EQUALS;
		final Theory t = iffTerm.getTheory();
		return t.term(PREFIX + IFFI1, iffTerm);
	}

	public static Term iffIntro2(final Term iffTerm) {
		assert ((ApplicationTerm) iffTerm).getFunction().getName() == SMTLIBConstants.EQUALS;
		final Theory t = iffTerm.getTheory();
		return t.term(PREFIX + IFFI2, iffTerm);
	}

	public static Term iffElim1(final Term iffTerm) {
		assert ((ApplicationTerm) iffTerm).getFunction().getName() == SMTLIBConstants.EQUALS;
		final Theory t = iffTerm.getTheory();
		return t.term(PREFIX + IFFE1, iffTerm);
	}

	public static Term iffElim2(final Term iffTerm) {
		assert ((ApplicationTerm) iffTerm).getFunction().getName() == SMTLIBConstants.EQUALS;
		final Theory t = iffTerm.getTheory();
		return t.term(PREFIX + IFFE2, iffTerm);
	}

	public static Term xorUnit(final Term term) {
		return term.getTheory().annotatedTerm(new Annotation[] { new Annotation(ANNOT_UNIT, null) }, term);
	}

	private static Term xorAxiom(final String name, final Term xorTerm1, final Term xorTerm2, final Term xorTerm3) {
		final Theory t = xorTerm1.getTheory();
		final Term[] xorArgs = new Term[] { xorTerm1, xorTerm2, xorTerm3 };
		for (int i = 0; i < 3; i++) {
			if ((!(xorArgs[i] instanceof ApplicationTerm)
					|| ((ApplicationTerm) xorArgs[i]).getFunction().getName() != SMTLIBConstants.XOR)
				&& (!(xorArgs[i] instanceof AnnotatedTerm)
						|| ((AnnotatedTerm) xorArgs[i]).getAnnotations()[0].getKey() != ANNOT_UNIT)) {
				xorArgs[i] = t.annotatedTerm(new Annotation[] { new Annotation(ANNOT_UNIT, null) }, xorArgs[i]);
			}
		}
		assert checkXorParams(xorArgs);
		return t.term(name, xorArgs);
	}

	public static Term xorIntro(final Term xorTerm1, final Term xorTerm2, final Term xorTerm3) {
		return xorAxiom(PREFIX + XORI, xorTerm1, xorTerm2, xorTerm3);
	}

	public static Term xorElim(final Term xorTerm1, final Term xorTerm2, final Term xorTerm3) {
		return xorAxiom(PREFIX + XORE, xorTerm1, xorTerm2, xorTerm3);
	}

	public static Term equalsIntro(final Term eqTerm) {
		assert ((ApplicationTerm) eqTerm).getFunction().getName() == SMTLIBConstants.EQUALS;
		final Theory t = eqTerm.getTheory();
		return t.term(PREFIX + EQI, eqTerm);
	}

	public static Term equalsElim(final int pos1, final int pos2, final Term eqTerm) {
		assert ((ApplicationTerm) eqTerm).getFunction().getName() == SMTLIBConstants.EQUALS;
		assert 0 <= pos1 && pos1 < ((ApplicationTerm) eqTerm).getParameters().length;
		assert 0 <= pos2 && pos2 < ((ApplicationTerm) eqTerm).getParameters().length;
		final Theory t = eqTerm.getTheory();
		return t.term(PREFIX + EQE,
				t.annotatedTerm(new Annotation[] { new Annotation(ANNOT_POS, new Integer[] { pos1, pos2 }) }, eqTerm));
	}

	public static Term distinctIntro(final Term disTerm) {
		assert ((ApplicationTerm) disTerm).getFunction().getName() == SMTLIBConstants.DISTINCT;
		final Theory t = disTerm.getTheory();
		return t.term(PREFIX + DISTINCTI, disTerm);
	}

	public static Term distinctElim(final int pos1, final int pos2, final Term disTerm) {
		assert ((ApplicationTerm) disTerm).getFunction().getName() == SMTLIBConstants.DISTINCT;
		assert 0 <= pos1 && pos1 < ((ApplicationTerm) disTerm).getParameters().length;
		assert 0 <= pos2 && pos2 < ((ApplicationTerm) disTerm).getParameters().length;
		final Theory t = disTerm.getTheory();
		return t.term(PREFIX + DISTINCTE,
				t.annotatedTerm(new Annotation[] { new Annotation(ANNOT_POS, new Integer[] { pos1, pos2 }) }, disTerm));
	}

	public static Term refl(final Term term) {
		final Theory t = term.getTheory();
		return t.term(PREFIX + REFL, term);
	}

	public static Term symm(final Term term1, final Term term2) {
		final Theory t = term1.getTheory();
		return t.term(PREFIX + SYMM, t.term(SMTLIBConstants.EQUALS, term1, term2));
	}

	public static Term trans(final Term... terms) {
		assert terms.length > 2;
		final Theory t = terms[0].getTheory();
		return t.term(PREFIX + TRANS, t.term(SMTLIBConstants.EQUALS, terms));
	}

	public static Term cong(final Term term1, final Term term2) {
		final Theory t = term1.getTheory();
		return t.term(PREFIX + CONG, t.term(SMTLIBConstants.EQUALS, term1, term2));
	}

	public static Term expand(final Term term) {
		final Theory t = term.getTheory();
		return t.term(PREFIX + EXPAND, term);
	}

	public static Term ite1(final Term iteTerm) {
		assert ((ApplicationTerm) iteTerm).getFunction().getName() == SMTLIBConstants.ITE;
		final Theory t = iteTerm.getTheory();
		return t.term(PREFIX + ITE1, iteTerm);
	}

	public static Term ite2(final Term iteTerm) {
		assert ((ApplicationTerm) iteTerm).getFunction().getName() == SMTLIBConstants.ITE;
		final Theory t = iteTerm.getTheory();
		return t.term(PREFIX + ITE2, iteTerm);
	}

	public static Term delAnnot(final AnnotatedTerm annotTerm) {
		final Theory t = annotTerm.getTheory();
		return t.term(PREFIX + DELANNOT, annotTerm);
	}

	public void printProof(final Appendable appender, final Term proof) {
		new PrintProof().append(appender, proof);
	}

	public static boolean checkXorParams(final Term[] params) {
		final HashSet<Term> xorSum = new HashSet<>();
		for (int i = 0; i < params.length; i++) {
			Term[] args;
			if (params[i] instanceof AnnotatedTerm) {
				/* unit xor argument */
				final AnnotatedTerm annotTerm = (AnnotatedTerm) params[i];
				final Annotation[] annots = annotTerm.getAnnotations();
				assert annots.length == 1 && annots[0].getKey() == ANNOT_UNIT && annots[0].getValue() == null;
				args = new Term[] { annotTerm.getSubterm() };
			} else {
				final ApplicationTerm xorTerm = (ApplicationTerm) params[i];
				assert xorTerm.getFunction().getName() == SMTLIBConstants.XOR;
				args = xorTerm.getParameters();
			}

			for (final Term arg : args) {
				if (xorSum.contains(arg)) {
					xorSum.remove(arg);
				} else {
					xorSum.add(arg);
				}
			}
		}
		return xorSum.isEmpty();
	}

	public static boolean isProofRule(final String rule, final Term proof) {
		return proof instanceof ApplicationTerm
				&& ((ApplicationTerm) proof).getFunction().getName().equals(PREFIX + rule);
	}

	public static class PrintProof extends PrintTerm {

		private void addChildParams(final Term child, final String expected) {
			if (child instanceof ApplicationTerm) {
				final ApplicationTerm subterm = (ApplicationTerm) child;
				assert subterm.getFunction().getName() == expected;
				final Term[] subParams = subterm.getParameters();
				for (int i = subParams.length - 1; i >= 0; i--) {
					mTodo.add(subParams[i]);
					mTodo.add(" ");
				}
			} else {
				mTodo.add(child);
				mTodo.add(" ::");
			}
		}

		@Override
		public void walkTerm(final Term proof) {
			if (proof instanceof ApplicationTerm) {
				final ApplicationTerm appTerm = (ApplicationTerm) proof;
				final Term[] params = appTerm.getParameters();
				switch (appTerm.getFunction().getName()) {
				case PREFIX + RES: {
					assert params.length == 3;
					mTodo.add(")");
					for (int i = params.length - 1; i >= 0; i--) {
						mTodo.add(params[i]);
						mTodo.add(" ");
					}
					mTodo.add("(" + RES);
					return;
				}
				case PREFIX + ASSUME: {
					assert params.length == 1;
					mTodo.add(")");
					mTodo.add(params[0]);
					mTodo.add("(" + ASSUME + " ");
					return;
				}
				case PREFIX + NOTI: {
					assert params.length == 1;
					mTodo.add(")");
					addChildParams(params[0], SMTLIBConstants.NOT);
					mTodo.add("(" + NOTI);
					return;
				}
				case PREFIX + NOTE: {
					assert params.length == 1;
					mTodo.add(")");
					addChildParams(params[0], SMTLIBConstants.NOT);
					mTodo.add("(" + NOTE);
					return;
				}
				case PREFIX + ORI: {
					assert params.length == 1;
					final AnnotatedTerm annotTerm = (AnnotatedTerm) params[0];
					final Annotation[] annots = annotTerm.getAnnotations();
					assert annots.length == 1 && annots[0].getKey().equals(ANNOT_POS);
					mTodo.add(")");
					addChildParams(annotTerm.getSubterm(), SMTLIBConstants.OR);
					mTodo.add(annots[0].getValue());
					mTodo.add("(" + ORI + " ");
					return;
				}
				case PREFIX + ORE: {
					assert params.length == 1;
					mTodo.add(")");
					addChildParams(params[0], SMTLIBConstants.OR);
					mTodo.add("(" + ORE);
					return;
				}
				case PREFIX + ANDI: {
					assert params.length == 1;
					mTodo.add(")");
					addChildParams(params[0], SMTLIBConstants.AND);
					mTodo.add("(" + ANDI);
					return;
				}
				case PREFIX + ANDE: {
					assert params.length == 1;
					final AnnotatedTerm annotTerm = (AnnotatedTerm) params[0];
					final Annotation[] annots = annotTerm.getAnnotations();
					assert annots.length == 1 && annots[0].getKey().equals(ANNOT_POS);
					mTodo.add(")");
					addChildParams(annotTerm.getSubterm(), SMTLIBConstants.AND);
					mTodo.add(annots[0].getValue());
					mTodo.add("(" + ANDE + " ");
					return;
				}
				case PREFIX + IMPI: {
					assert params.length == 1;
					final AnnotatedTerm annotTerm = (AnnotatedTerm) params[0];
					final Annotation[] annots = annotTerm.getAnnotations();
					assert annots.length == 1 && annots[0].getKey().equals(ANNOT_POS);
					mTodo.add(")");
					addChildParams(annotTerm.getSubterm(), SMTLIBConstants.IMPLIES);
					mTodo.add(annots[0].getValue());
					mTodo.add("(" + IMPI + " ");
					return;
				}
				case PREFIX + IMPE: {
					assert params.length == 1;
					mTodo.add(")");
					addChildParams(params[0], SMTLIBConstants.IMPLIES);
					mTodo.add("(" + IMPE);
					return;
				}
				case PREFIX + IFFI1: {
					assert params.length == 1;
					mTodo.add(")");
					addChildParams(params[0], SMTLIBConstants.EQUALS);
					mTodo.add("(" + IFFI1);
					return;
				}
				case PREFIX + IFFI2: {
					assert params.length == 1;
					mTodo.add(")");
					addChildParams(params[0], SMTLIBConstants.EQUALS);
					mTodo.add("(" + IFFI2);
					return;
				}
				case PREFIX + IFFE1: {
					assert params.length == 1;
					mTodo.add(")");
					addChildParams(params[0], SMTLIBConstants.EQUALS);
					mTodo.add("(" + IFFE1);
					return;
				}
				case PREFIX + IFFE2: {
					assert params.length == 1;
					mTodo.add(")");
					addChildParams(params[0], SMTLIBConstants.EQUALS);
					mTodo.add("(" + IFFE2);
					return;
				}
				case PREFIX + REFL: {
					assert params.length == 1;
					mTodo.add(")");
					mTodo.add(params[0]);
					mTodo.add("(" + REFL + " ");
					return;
				}
				case PREFIX + SYMM: {
					assert params.length == 1;
					mTodo.add(")");
					addChildParams(params[0], SMTLIBConstants.EQUALS);
					mTodo.add("(" + SYMM);
					return;
				}
				case PREFIX + TRANS: {
					assert params.length == 1;
					mTodo.add(")");
					addChildParams(params[0], SMTLIBConstants.EQUALS);
					mTodo.add("(" + TRANS);
					return;
				}
				case PREFIX + CONG: {
					assert params.length == 1;
					mTodo.add(")");
					addChildParams(params[0], SMTLIBConstants.EQUALS);
					mTodo.add("(" + CONG);
					return;
				}
				case PREFIX + DELANNOT: {
					assert params.length == 1;
					mTodo.add(")");
					mTodo.add(params[0]);
					mTodo.add("(" + DELANNOT + " ");
					return;
				}
				default:
					break;
				}
			}
			super.walkTerm(proof);
		}
	}
}
