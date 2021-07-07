package de.uni_freiburg.informatik.ultimate.smtinterpol.proof;

import java.util.HashSet;

import de.uni_freiburg.informatik.ultimate.logic.AnnotatedTerm;
import de.uni_freiburg.informatik.ultimate.logic.Annotation;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.PrintTerm;
import de.uni_freiburg.informatik.ultimate.logic.SMTLIBConstants;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.logic.Theory;

public class ProofRules {
	public final static String RES = "res";
	public final static String INSTANTIATE = "instantiate";
	public final static String ASSERT = "assert";
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
	public final static String TRANS = "trans";
	public final static String SYMM = "symm";
	public final static String CONG = "cong";
	public final static String EXPAND = "expand";
	public final static String ANNOT = "del!";
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

		if (t.getDeclaredSorts().containsKey(PREFIX+PROOF)) {
			return;
		}

		t.declareInternalSort(PREFIX + PROOF, 0, 0);
		final Sort proofSort = t.getSort(PREFIX + PROOF);
		final Sort boolSort = t.getBooleanSort();
		final Sort[] proof1 = new Sort[] { proofSort };
		final Sort[] bool1 = new Sort[] { boolSort };
		final Sort[] bool3 = new Sort[] { boolSort, boolSort, boolSort };
		final Sort[] sort0 = new Sort[0];

		t.declareInternalFunction(PREFIX + RES, new Sort[] { boolSort, proofSort, proofSort }, proofSort, 0);
		t.declareInternalFunction(PREFIX + INSTANTIATE, proof1, proofSort, 0);
		t.declareInternalFunction(PREFIX + ASSERT, proof1, proofSort, 0);
		t.declareInternalFunction(PREFIX + FALSEE, sort0, proofSort, 0);
		t.declareInternalFunction(PREFIX + TRUEI, sort0, proofSort, 0);
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
		t.declareInternalFunction(PREFIX + ITE1, bool1, proofSort, 0);
		t.declareInternalFunction(PREFIX + ITE2, bool1, proofSort, 0);
		t.declareInternalFunction(PREFIX + TRANS, bool1, proofSort, 0);
		t.declareInternalFunction(PREFIX + SYMM, bool1, proofSort, 0);
		t.declareInternalFunction(PREFIX + CONG, bool1, proofSort, 0);
		t.declareInternalFunction(PREFIX + EXPAND, bool1, proofSort, 0);
		t.declareInternalFunction(PREFIX + ANNOT, bool1, proofSort, 0);
	}

	public static Term resolutionRule(final Term pivot, final Term proofPos, final Term proofNeg) {
		final Theory t = pivot.getTheory();
		return t.term(PREFIX + RES, pivot, proofPos, proofNeg);
	}

	public static Term instantiationRule(final TermVariable[] vars, final Term[] values, final Term subproof) {
		final Theory t = subproof.getTheory();
		final Annotation[] annotation = new Annotation[] { new Annotation(ANNOT_VARS, vars),
				new Annotation(ANNOT_VALUES, values) };
		return t.term(PREFIX + INSTANTIATE, t.annotatedTerm(annotation, subproof));
	}

	public static Term asserted(final Term t) {
		return t.getTheory().term(PREFIX + ASSERT, t);
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

	private static Term xorAxiom(final String name, final Term xorTerm1, final Term xorTerm2, final Term xorTerm3) {
		final Theory t = xorTerm1.getTheory();
		final Term[] xorArgs = new Term[] { xorTerm1, xorTerm2, xorTerm3 };
		for (int i = 0; i < 3; i++) {
			if (!(xorArgs[i] instanceof ApplicationTerm)
					|| ((ApplicationTerm) xorArgs[i]).getFunction().getName() != SMTLIBConstants.XOR) {
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

	public static Term trans(Term... terms) {
		assert terms.length != 2;
		final Theory t = terms[0].getTheory();
		if (terms.length == 1) {
			terms = new Term[] { terms[0], terms[0] };
		}
		return t.term(PREFIX + TRANS, t.term(SMTLIBConstants.EQUALS, terms));
	}

	public static Term symm(final Term term1, final Term term2) {
		final Theory t = term1.getTheory();
		return t.term(PREFIX + SYMM, t.term(SMTLIBConstants.EQUALS, term1, term2));
	}

	public static Term cong(final Term term1, final Term term2) {
		final Theory t = term1.getTheory();
		return t.term(PREFIX + CONG, t.term(SMTLIBConstants.EQUALS, term1, term2));
	}

	public static Term expand(final Term term) {
		final Theory t = term.getTheory();
		return t.term(PREFIX + EXPAND, term);
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

	public ProofLiteral[] computeClause(final Term axiom) {
		final ApplicationTerm appTerm = (ApplicationTerm) axiom;
		final Term[] params = appTerm.getParameters();
		switch (appTerm.getFunction().getName()) {
		case PREFIX + ASSERT: {
			assert params.length == 1;
			// t
			return new ProofLiteral[] { new ProofLiteral(params[0], true) };
		}
		case PREFIX + NOTI: {
			assert params.length == 1;
			final ApplicationTerm subterm = (ApplicationTerm) params[0];
			assert subterm.getFunction().getName() == SMTLIBConstants.NOT;
			final Term[] subParams = subterm.getParameters();

			// (not t), t
			return new ProofLiteral[] { new ProofLiteral(subterm, true), new ProofLiteral(subParams[0], true) };
		}
		case PREFIX + NOTE: {
			assert params.length == 1;
			final ApplicationTerm subterm = (ApplicationTerm) params[0];
			assert subterm.getFunction().getName() == SMTLIBConstants.NOT;
			final Term[] subParams = subterm.getParameters();

			// ~(not t), ~t
			return new ProofLiteral[] { new ProofLiteral(subterm, false), new ProofLiteral(subParams[0], false) };
		}
		case PREFIX + ORI: {
			assert params.length == 1;
			final AnnotatedTerm annotTerm = (AnnotatedTerm) params[0];
			final Annotation[] annots = annotTerm.getAnnotations();
			assert annots.length == 1 && annots[0].getKey().equals(ANNOT_POS);
			final ApplicationTerm subterm = (ApplicationTerm) annotTerm.getSubterm();
			assert subterm.getFunction().getName() == SMTLIBConstants.OR;
			final int pos = (Integer) annots[0].getValue();
			final Term[] subParams = subterm.getParameters();
			assert pos >= 0 && pos < subParams.length;

			// (or t1 ... tn), ~tpos
			return new ProofLiteral[] { new ProofLiteral(subterm, true), new ProofLiteral(subParams[pos], false) };
		}
		case PREFIX + ORE: {
			assert params.length == 1;
			final ApplicationTerm subterm = (ApplicationTerm) params[0];
			assert subterm.getFunction().getName() == SMTLIBConstants.OR;
			final Term[] subParams = subterm.getParameters();

			// ~(or t1 ... tn), t1, ..., tn
			final ProofLiteral[] clause = new ProofLiteral[subParams.length + 1];
			clause[0] = new ProofLiteral(subterm, false);
			for (int i = 0; i < subParams.length; i++) {
				clause[i + 1] = new ProofLiteral(subParams[i], true);
			}
			return clause;
		}
		case PREFIX + ANDI: {
			assert params.length == 1;
			final ApplicationTerm subterm = (ApplicationTerm) params[0];
			assert subterm.getFunction().getName() == SMTLIBConstants.AND;
			final Term[] subParams = subterm.getParameters();

			// (and t1 ... tn), ~t1, ..., ~tn
			final ProofLiteral[] clause = new ProofLiteral[subParams.length + 1];
			clause[0] = new ProofLiteral(subterm, true);
			for (int i = 0; i < subParams.length; i++) {
				clause[i + 1] = new ProofLiteral(subParams[i], false);
			}
			return clause;
		}
		case PREFIX + ANDE: {
			assert params.length == 1;
			final AnnotatedTerm annotTerm = (AnnotatedTerm) params[0];
			final Annotation[] annots = annotTerm.getAnnotations();
			assert annots.length == 1 && annots[0].getKey().equals(ANNOT_POS);
			final ApplicationTerm subterm = (ApplicationTerm) annotTerm.getSubterm();
			assert subterm.getFunction().getName() == SMTLIBConstants.AND;
			final int pos = (Integer) annots[0].getValue();
			final Term[] subParams = subterm.getParameters();
			assert pos >= 0 && pos < subParams.length;

			// ~(and t1 ... tn), tpos
			return new ProofLiteral[] { new ProofLiteral(subterm, false), new ProofLiteral(subParams[pos], true) };
		}
		case PREFIX + IMPI: {
			assert params.length == 1;
			final AnnotatedTerm annotTerm = (AnnotatedTerm) params[0];
			final Annotation[] annots = annotTerm.getAnnotations();
			assert annots.length == 1 && annots[0].getKey().equals(ANNOT_POS);
			final ApplicationTerm subterm = (ApplicationTerm) annotTerm.getSubterm();
			assert subterm.getFunction().getName() == SMTLIBConstants.IMPLIES;
			final int pos = (Integer) annots[0].getValue();
			final Term[] subParams = subterm.getParameters();
			assert pos >= 0 && pos < subParams.length;

			// (=> t1 ... tn), tpos (~tpos if pos == n)
			return new ProofLiteral[] { new ProofLiteral(subterm, true),
					new ProofLiteral(subParams[pos], pos < subParams.length - 1) };
		}
		case PREFIX + IMPE: {
			assert params.length == 1;
			final ApplicationTerm subterm = (ApplicationTerm) params[0];
			assert subterm.getFunction().getName() == SMTLIBConstants.IMPLIES;
			final Term[] subParams = subterm.getParameters();

			// ~(=> t1 ... tn), ~t1, ..., ~tn-1, tn
			final ProofLiteral[] clause = new ProofLiteral[subParams.length + 1];
			clause[0] = new ProofLiteral(subterm, false);
			for (int i = 0; i < subParams.length; i++) {
				clause[i + 1] = new ProofLiteral(subParams[i], i == subParams.length - 1);
			}
			return clause;
		}
		case PREFIX + IFFI1: {
			assert params.length == 1;
			final ApplicationTerm subterm = (ApplicationTerm) params[0];
			assert subterm.getFunction().getName() == SMTLIBConstants.EQUALS;
			final Term[] subParams = subterm.getParameters();
			assert subParams.length == 2;

			// (= t1 t2), t1, t2
			return new ProofLiteral[] { new ProofLiteral(subterm, true),
					new ProofLiteral(subParams[0], true),
					new ProofLiteral(subParams[1], true) };
		}
		case PREFIX + IFFI2: {
			assert params.length == 1;
			final ApplicationTerm subterm = (ApplicationTerm) params[0];
			assert subterm.getFunction().getName() == SMTLIBConstants.EQUALS;
			final Term[] subParams = subterm.getParameters();
			assert subParams.length == 2;

			// (= t1 t2), ~t1, ~t2
			return new ProofLiteral[] { new ProofLiteral(subterm, true),
					new ProofLiteral(subParams[0], false),
					new ProofLiteral(subParams[1], false) };
		}
		case PREFIX + IFFE1: {
			assert params.length == 1;
			final ApplicationTerm subterm = (ApplicationTerm) params[0];
			assert subterm.getFunction().getName() == SMTLIBConstants.EQUALS;
			final Term[] subParams = subterm.getParameters();
			assert subParams.length == 2;

			// ~(= t1 t2), t1, ~t2
			return new ProofLiteral[] { new ProofLiteral(subterm, false),
					new ProofLiteral(subParams[0], true),
					new ProofLiteral(subParams[1], false) };
		}
		case PREFIX + IFFE2: {
			assert params.length == 1;
			final ApplicationTerm subterm = (ApplicationTerm) params[0];
			assert subterm.getFunction().getName() == SMTLIBConstants.EQUALS;
			final Term[] subParams = subterm.getParameters();
			assert subParams.length == 2;

			// ~(= t1 t2), ~t1, t2
			return new ProofLiteral[] { new ProofLiteral(subterm, false),
					new ProofLiteral(subParams[0], false),
					new ProofLiteral(subParams[1], true) };
		}
		case PREFIX + XORI: {
			assert params.length == 3;
			assert checkXorParams(params);
			// (xor set0), (xor set1), ~(xor set2)
			final ProofLiteral[] clause = new ProofLiteral[3];
			for (int i = 0; i < 3; i++) {
				Term atom = params[i];
				if (atom instanceof AnnotatedTerm) {
					assert ((AnnotatedTerm) atom).getAnnotations()[0].getKey() == "unit";
					atom = ((AnnotatedTerm) atom).getSubterm();
				}
				clause[i] = new ProofLiteral(atom, i < 2);
			}
			return clause;
		}
		case PREFIX + XORE: {
			assert params.length == 3;
			assert checkXorParams(params);
			// ~(xor set0), ~(xor set1), ~(xor set2)
			final ProofLiteral[] clause = new ProofLiteral[3];
			for (int i = 0; i < 3; i++) {
				Term atom = params[i];
				if (atom instanceof AnnotatedTerm) {
					assert ((AnnotatedTerm) atom).getAnnotations()[0].getKey() == "unit";
					atom = ((AnnotatedTerm) atom).getSubterm();
				}
				clause[i] = new ProofLiteral(atom, false);
			}
			return clause;
		}
		case PREFIX + EQI: {
			assert params.length == 1;
			final ApplicationTerm subterm = (ApplicationTerm) params[0];
			assert subterm.getFunction().getName() == SMTLIBConstants.EQUALS;
			final Term[] subParams = subterm.getParameters();
			final Theory t = axiom.getTheory();

			// (= t1 ... tn), ~(= t1 t2), ~(tn-1 tn)
			final ProofLiteral[] clause = new ProofLiteral[subParams.length];
			clause[0] = new ProofLiteral(subterm, true);
			for (int i = 0; i < subParams.length - 1; i++) {
				clause[i + 1] = new ProofLiteral(t.term(SMTLIBConstants.EQUALS, subParams[i], subParams[i + 1]), false);
			}
			return clause;
		}
		case PREFIX + EQE: {
			assert params.length == 1;
			final AnnotatedTerm annotTerm = (AnnotatedTerm) params[0];
			final Annotation[] annots = annotTerm.getAnnotations();
			assert annots.length == 1 && annots[0].getKey().equals(ANNOT_POS);
			final ApplicationTerm subterm = (ApplicationTerm) annotTerm.getSubterm();
			assert subterm.getFunction().getName() == SMTLIBConstants.EQUALS;
			final Term[] subParams = subterm.getParameters();
			final Object[] positions = (Object[]) annots[0].getValue();
			assert positions.length == 2;
			final int pos0 = (Integer) positions[0];
			final int pos1 = (Integer) positions[1];
			assert 0 <= pos0 && pos0 < subParams.length && 0 <= pos1 && pos1 < subParams.length;
			final Theory t = axiom.getTheory();

			// ~(= t1 ... tn), (= ti tj)
			return new ProofLiteral[] { new ProofLiteral(subterm, false),
					new ProofLiteral(t.term(SMTLIBConstants.EQUALS, subParams[pos0], subParams[pos1]), true) };
		}
		case PREFIX + DISTINCTI: {
			assert params.length == 1;
			final ApplicationTerm subterm = (ApplicationTerm) params[0];
			assert subterm.getFunction().getName() == SMTLIBConstants.DISTINCT;
			final Term[] subParams = subterm.getParameters();
			final Theory t = axiom.getTheory();
			final int len = subParams.length;

			// (distinct t1 ... tn), (= t1 t2),...
			final ProofLiteral[] clause = new ProofLiteral[1 + len * (len - 1) / 2];
			clause[0] = new ProofLiteral(subterm, true);
			int pos = 0;
			for (int i = 0; i < len - 1; i++) {
				for (int j = i + 1; j < len; j++) {
					clause[pos++] = new ProofLiteral(t.term(SMTLIBConstants.EQUALS, subParams[i], subParams[j]), true);
				}
			}
			assert pos == clause.length;
			return clause;
		}
		case PREFIX + DISTINCTE: {
			assert params.length == 1;
			final AnnotatedTerm annotTerm = (AnnotatedTerm) params[0];
			final Annotation[] annots = annotTerm.getAnnotations();
			assert annots.length == 1 && annots[0].getKey().equals(ANNOT_POS);
			final ApplicationTerm subterm = (ApplicationTerm) annotTerm.getSubterm();
			assert subterm.getFunction().getName() == SMTLIBConstants.DISTINCT;
			final Term[] subParams = subterm.getParameters();
			final Object[] positions = (Object[]) annots[0].getValue();
			assert positions.length == 2;
			final int pos0 = (Integer) positions[0];
			final int pos1 = (Integer) positions[1];
			assert 0 <= pos0 && pos0 < subParams.length && 0 <= pos1 && pos1 < subParams.length;
			final Theory t = axiom.getTheory();

			// ~(distinct t1 ... tn), ~(= ti tj)
			return new ProofLiteral[] { new ProofLiteral(subterm, false),
					new ProofLiteral(t.term(SMTLIBConstants.EQUALS, subParams[pos0], subParams[pos1]), false) };
		}
		case PREFIX + ITE1: {
			assert params.length == 1;
			final ApplicationTerm subterm = (ApplicationTerm) params[0];
			assert subterm.getFunction().getName() == SMTLIBConstants.ITE;
			final Term[] subParams = subterm.getParameters();
			assert subParams.length == 3;
			final Theory t = axiom.getTheory();

			// (= (ite c t e) t), ~c
			return new ProofLiteral[] { new ProofLiteral(t.term(SMTLIBConstants.EQUALS, params[0], subParams[1]), true),
					new ProofLiteral(subParams[0], false) };
		}
		case PREFIX + ITE2: {
			assert params.length == 1;
			final ApplicationTerm subterm = (ApplicationTerm) params[0];
			assert subterm.getFunction().getName() == SMTLIBConstants.ITE;
			final Term[] subParams = subterm.getParameters();
			assert subParams.length == 3;
			final Theory t = axiom.getTheory();

			// (= (ite c t e) e), c
			return new ProofLiteral[] { new ProofLiteral(t.term(SMTLIBConstants.EQUALS, params[0], subParams[2]), true),
					new ProofLiteral(subParams[0], true) };
		}
		case PREFIX + ANNOT: {
			assert params.length == 1;
			final AnnotatedTerm annotTerm = (AnnotatedTerm) params[0];
			final Term subterm = annotTerm.getSubterm();
			final Theory t = axiom.getTheory();

			// (= (! t :...) t)
			return new ProofLiteral[] { new ProofLiteral(t.term(SMTLIBConstants.EQUALS, annotTerm, subterm), true) };
		}
		case PREFIX + TRANS: {
			assert params.length == 1;
			final ApplicationTerm subterm = (ApplicationTerm) params[0];
			assert subterm.getFunction().getName() == SMTLIBConstants.EQUALS;
			Term subParams[] = subterm.getParameters();
			if (subParams.length == 2) {
				// hack for reflexivity
				assert subParams[0] == subParams[1];
				subParams = new Term[] { subParams[0] };
			}
			final int len = subParams.length;
			final Theory t = axiom.getTheory();

			// (= a0 alen-1), ~(= a0 a1), ..., ~(= alen-2 alen-1)
			final ProofLiteral[] clause = new ProofLiteral[len];
			clause[0] = new ProofLiteral(t.term(SMTLIBConstants.EQUALS, subParams[0], subParams[len - 1]), true);
			for (int i = 0; i < len -1; i++)  {
				clause[i + 1] = new ProofLiteral(t.term(SMTLIBConstants.EQUALS, subParams[i], subParams[i + 1]), false);
			}
			return clause;
		}
		case PREFIX + SYMM: {
			assert params.length == 1;
			final ApplicationTerm subterm = (ApplicationTerm) params[0];
			assert subterm.getFunction().getName() == SMTLIBConstants.EQUALS;
			final Term subParams[] = subterm.getParameters();
			assert subParams.length == 2;
			final Theory t = axiom.getTheory();

			// (= a0 a1), ~(= a1 a0)
			return new ProofLiteral[] {
					new ProofLiteral(subterm, true),
					new ProofLiteral(t.term(SMTLIBConstants.EQUALS, subParams[1], subParams[0]), false)
			};
		}
		case PREFIX + CONG: {
			assert params.length == 1;
			final ApplicationTerm subterm = (ApplicationTerm) params[0];
			assert subterm.getFunction().getName() == SMTLIBConstants.EQUALS;
			final Term subParams[] = subterm.getParameters();
			assert subParams.length == 2;
			final ApplicationTerm appTerm0 = (ApplicationTerm) subParams[0];
			final ApplicationTerm appTerm1 = (ApplicationTerm) subParams[1];
			assert (appTerm0.getFunction() == appTerm1.getFunction());
			final Term[] params0 = appTerm0.getParameters();
			final Term[] params1 = appTerm1.getParameters();
			assert params0.length == params1.length;
			final Theory t = axiom.getTheory();

			// (= (f a0...an) (f b0... bn)), ~(= a0 b0), ..., ~(= an bn)
			final ProofLiteral[] clause = new ProofLiteral[params0.length + 1];
			clause[0] = new ProofLiteral(subterm, true);
			for (int i = 0; i < params0.length; i++) {
				clause[i + 1] = new ProofLiteral(t.term(SMTLIBConstants.EQUALS, params0[i], params1[i]), false);
			}
			return clause;
		}
		default:
			throw new AssertionError("Unknown axiom "+ axiom);
		}
	}

	public class ProofLiteral {
		Term mAtom;
		boolean mPositive;

		public ProofLiteral(final Term atom, final boolean positive) {
			mAtom = atom;
			mPositive = positive;
		}

		public ProofLiteral negate() {
			return new ProofLiteral(mAtom, !mPositive);
		}

		@Override
		public int hashCode() {
			return mAtom.hashCode() ^ (mPositive ? 0 : 0xffffffff);
		}

		@Override
		public boolean equals(final Object other) {
			if (!(other instanceof ProofLiteral)) {
				return false;
			}
			final ProofLiteral otherLit = (ProofLiteral) other;
			return mAtom == otherLit.mAtom && mPositive == otherLit.mPositive;
		}

		@Override
		public String toString() {
			return mPositive ? mAtom.toString() : "~" + mAtom.toString();
		}
	}

	class PrintProof extends PrintTerm {
		@Override
		public void walkTerm(final Term proof) {
			if (proof instanceof ApplicationTerm) {
				final ApplicationTerm appTerm = (ApplicationTerm) proof;
				final Term[] params = appTerm.getParameters();
				switch (appTerm.getFunction().getName()) {
				case PREFIX + RES: {
					assert params.length == 3;
					mTodo.push(")");
					for (int i = params.length - 1; i >= 0; i--) {
						mTodo.push(params[i]);
						mTodo.push(" ");
					}
					mTodo.push("(" + RES);
					return;
				}
				case PREFIX + INSTANTIATE: {
					assert params.length == 1;
					final AnnotatedTerm annotTerm = (AnnotatedTerm) params[0];
					final Annotation[] annots = annotTerm.getAnnotations();
					assert annots.length == 2 && annots[0].getKey().equals(ANNOT_VARS)
							&& annots[0].getKey().equals(ANNOT_VALUES);
					final TermVariable[] vars = (TermVariable[]) annots[0].getValue();
					final Term[] terms = (Term[]) annots[1].getValue();
					assert vars.length == terms.length && vars.length > 0;
					mTodo.push(")");
					mTodo.push(annotTerm.getSubterm());
					String separator = ")) ";
					for (int i = terms.length - 1; i >= 0; i--) {
						mTodo.push(separator);
						mTodo.push(terms[i]);
						mTodo.push(" ");
						mTodo.push(terms[i]);
						separator = ") (";
					}
					mTodo.push("(" + INSTANTIATE + " ((");
					return;
				}
				case PREFIX + ASSERT: {
					assert params.length == 1;
					mTodo.push(")");
					mTodo.push(params[0]);
					mTodo.push("(" + ASSERT + " ");
					return;
				}
				case PREFIX + NOTI: {
					assert params.length == 1;
					final ApplicationTerm subterm = (ApplicationTerm) params[0];
					assert subterm.getFunction().getName() == SMTLIBConstants.NOT;
					final Term[] subParams = subterm.getParameters();
					mTodo.push(")");
					for (int i = subParams.length - 1; i >= 0; i--) {
						mTodo.push(subParams[i]);
						mTodo.push(" ");
					}
					mTodo.push("(" + NOTI);
					return;
				}
				case PREFIX + NOTE: {
					assert params.length == 1;
					final ApplicationTerm subterm = (ApplicationTerm) params[0];
					assert subterm.getFunction().getName() == SMTLIBConstants.NOT;
					final Term[] subParams = subterm.getParameters();
					mTodo.push(")");
					for (int i = subParams.length - 1; i >= 0; i--) {
						mTodo.push(subParams[i]);
						mTodo.push(" ");
					}
					mTodo.push("(" + NOTE);
					return;
				}
				case PREFIX + ORI: {
					assert params.length == 1;
					final AnnotatedTerm annotTerm = (AnnotatedTerm) params[0];
					final Annotation[] annots = annotTerm.getAnnotations();
					assert annots.length == 1 && annots[0].getKey().equals(ANNOT_POS);
					final ApplicationTerm subterm = (ApplicationTerm) annotTerm.getSubterm();
					assert subterm.getFunction().getName() == SMTLIBConstants.OR;
					final Term[] subParams = subterm.getParameters();
					mTodo.push(")");
					for (int i = subParams.length - 1; i >= 0; i--) {
						mTodo.push(subParams[i]);
						mTodo.push(" ");
					}
					mTodo.push(annots[0].getValue());
					mTodo.push("(" + ORI + " ");
					return;
				}
				case PREFIX + ORE: {
					assert params.length == 1;
					final ApplicationTerm subterm = (ApplicationTerm) params[0];
					assert subterm.getFunction().getName() == SMTLIBConstants.OR;
					final Term[] subParams = subterm.getParameters();
					mTodo.push(")");
					for (int i = subParams.length - 1; i >= 0; i--) {
						mTodo.push(subParams[i]);
						mTodo.push(" ");
					}
					mTodo.push("(" + ORE);
					return;
				}
				case PREFIX + ANDI: {
					assert params.length == 1;
					final ApplicationTerm subterm = (ApplicationTerm) params[0];
					assert subterm.getFunction().getName() == SMTLIBConstants.AND;
					final Term[] subParams = subterm.getParameters();
					mTodo.push(")");
					for (int i = subParams.length - 1; i >= 0; i--) {
						mTodo.push(subParams[i]);
						mTodo.push(" ");
					}
					mTodo.push("(" + ANDI);
					return;
				}
				case PREFIX + ANDE: {
					assert params.length == 1;
					final AnnotatedTerm annotTerm = (AnnotatedTerm) params[0];
					final Annotation[] annots = annotTerm.getAnnotations();
					assert annots.length == 1 && annots[0].getKey().equals(ANNOT_POS);
					final ApplicationTerm subterm = (ApplicationTerm) annotTerm.getSubterm();
					assert subterm.getFunction().getName() == SMTLIBConstants.AND;
					final Term[] subParams = subterm.getParameters();
					mTodo.push(")");
					for (int i = subParams.length - 1; i >= 0; i--) {
						mTodo.push(subParams[i]);
						mTodo.push(" ");
					}
					mTodo.push(annots[0].getValue());
					mTodo.push("(" + ANDE + " ");
					return;
				}
				case PREFIX + IMPI: {
					assert params.length == 1;
					final AnnotatedTerm annotTerm = (AnnotatedTerm) params[0];
					final Annotation[] annots = annotTerm.getAnnotations();
					assert annots.length == 1 && annots[0].getKey().equals(ANNOT_POS);
					final ApplicationTerm subterm = (ApplicationTerm) annotTerm.getSubterm();
					assert subterm.getFunction().getName() == SMTLIBConstants.IMPLIES;
					final Term[] subParams = subterm.getParameters();
					mTodo.push(")");
					for (int i = subParams.length - 1; i >= 0; i--) {
						mTodo.push(subParams[i]);
						mTodo.push(" ");
					}
					mTodo.push(annots[0].getValue());
					mTodo.push("(" + IMPI + " ");
					return;
				}
				case PREFIX + IMPE: {
					assert params.length == 1;
					final ApplicationTerm subterm = (ApplicationTerm) params[0];
					assert subterm.getFunction().getName() == SMTLIBConstants.IMPLIES;
					final Term[] subParams = subterm.getParameters();
					mTodo.push(")");
					for (int i = subParams.length - 1; i >= 0; i--) {
						mTodo.push(subParams[i]);
						mTodo.push(" ");
					}
					mTodo.push("(" + IMPE);
					return;
				}
				case PREFIX + IFFI1: {
					assert params.length == 1;
					final ApplicationTerm subterm = (ApplicationTerm) params[0];
					assert subterm.getFunction().getName() == SMTLIBConstants.EQUALS;
					final Term[] subParams = subterm.getParameters();
					assert subParams.length == 2;
					mTodo.push(")");
					for (int i = subParams.length - 1; i >= 0; i--) {
						mTodo.push(subParams[i]);
						mTodo.push(" ");
					}
					mTodo.push("(" + IFFI1);
					return;
				}
				case PREFIX + IFFI2: {
					assert params.length == 1;
					final ApplicationTerm subterm = (ApplicationTerm) params[0];
					assert subterm.getFunction().getName() == SMTLIBConstants.EQUALS;
					final Term[] subParams = subterm.getParameters();
					assert subParams.length == 2;
					mTodo.push(")");
					for (int i = subParams.length - 1; i >= 0; i--) {
						mTodo.push(subParams[i]);
						mTodo.push(" ");
					}
					mTodo.push("(" + IFFI2);
					return;
				}
				case PREFIX + IFFE1: {
					assert params.length == 1;
					final ApplicationTerm subterm = (ApplicationTerm) params[0];
					assert subterm.getFunction().getName() == SMTLIBConstants.EQUALS;
					final Term[] subParams = subterm.getParameters();
					assert subParams.length == 2;
					mTodo.push(")");
					for (int i = subParams.length - 1; i >= 0; i--) {
						mTodo.push(subParams[i]);
						mTodo.push(" ");
					}
					mTodo.push("(" + IFFE1);
					return;
				}
				case PREFIX + IFFE2: {
					assert params.length == 1;
					final ApplicationTerm subterm = (ApplicationTerm) params[0];
					assert subterm.getFunction().getName() == SMTLIBConstants.EQUALS;
					final Term[] subParams = subterm.getParameters();
					assert subParams.length == 2;
					mTodo.push(")");
					for (int i = subParams.length - 1; i >= 0; i--) {
						mTodo.push(subParams[i]);
						mTodo.push(" ");
					}
					mTodo.push("(" + IFFE2);
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
