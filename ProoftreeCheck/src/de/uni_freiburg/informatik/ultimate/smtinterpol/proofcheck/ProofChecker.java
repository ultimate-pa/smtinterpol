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

import java.io.BufferedWriter;
import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.Map.Entry;

import de.uni_freiburg.informatik.ultimate.logic.AnnotatedTerm;
import de.uni_freiburg.informatik.ultimate.logic.Annotation;
import de.uni_freiburg.informatik.ultimate.logic.FormulaUnLet;
import de.uni_freiburg.informatik.ultimate.logic.Logics;
import de.uni_freiburg.informatik.ultimate.logic.SMTLIBException;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.smtinterpol.smtlib2.SMTInterpol;

/**
 * This is the main controller to check the correctness of an SMTInterpol proof
 * by translating and transferring it to Isabelle.
 * 
 * NOTE: Quantifiers were not supported up until this implementation, so they
 * are not supported. However, the most important places that must be changed
 * to support them are marked with '<quantifiers>'
 * (ProofConverter, TermConverter, and SubstitutionConverter only). 
 * 
 * @author Christian Schilling <schillic@informatik.uni-freiburg.de>
 */
public class ProofChecker extends SMTInterpol {
	// name of the parsed file (needed for output)
	private final String mFileName;
	// name of the lemma theory file
	private final String mLemmaFileName;
	// files for the proof to be written to
	private final BufferedWriter mFile, mLemmaFile;
	// term converter
	private TermConverter mConverter;
	// proof converter
	private ProofConverter mProofConverter;
	// true iff Isabelle shall be invoked directly during the process 
	private final boolean mUseIsabelle;
	// true iff output file is printed in more convenient human-readable way
	private final boolean mPrettyOutput;
	// true iff fast proofs shall be printed
	private final boolean mFastProofs;
	// true iff only the partial proof is given
	private final boolean mPartialProof;
	// set of already bound :named definitions (for more than one check-sat)
	private final HashSet<String> mNamedSet;
	// number, prefix, and map for the assertions
	private int mAssertionNumber;
	protected static final String ASSERTION_PREFIX = "smt_prm";
	private final HashMap<Term, Integer> mAssertion2index;
	protected static final String PARTIAL_ANNOTATION = ":named";
	
	/**
	 * @param fileName name of the parsed file
	 * @param useIsabelle true iff Isabelle shall be invoked as well
	 * @param prettyOutput true iff output file shall be 
	 */
	public ProofChecker(final String fileName, final boolean useIsabelle,
			final boolean prettyOutput, final boolean fastProofs,
			final boolean partialProof) {
		super();
		
		// write Isabelle files
		mFileName = fileName;
		mLemmaFileName = fileName + "_lemma";
		try {
			final File isaFile = createIsabelleFile();
			mFile = new BufferedWriter(new FileWriter(isaFile));
			final File lemmaFile = createTheoryFile();
			mLemmaFile = new BufferedWriter(new FileWriter(lemmaFile));
		} catch (final IOException e) {
			throw new RuntimeException(e);
		}
		
		mUseIsabelle = useIsabelle;
		mPrettyOutput = prettyOutput;
		mFastProofs = fastProofs;
		mPartialProof = partialProof;
		mNamedSet = new HashSet<String>();
		mAssertionNumber = 0;
		mAssertion2index = mPartialProof
				? null
				: new HashMap<Term, Integer>();
		
		// set proof producing options (never overwritten)
		if (mPartialProof) {
			super.setOption(":produce-interpolants", true);
			super.setOption(":produce-proofs", false);
		} else {
			super.setOption(":produce-proofs", true);
		}
		
		super.setOption(":interactive-mode", true);
	}
	
	/**
	 * {@inheritDoc}
	 * 
	 * The method is overwritten to prohibit change of proof production.
	 */
	@Override
	public void setOption(String opt, Object value)
		throws UnsupportedOperationException, SMTLIBException {
		if ((opt.equals(":produce-proofs"))
				|| (opt.equals(":interactive-mode"))
				|| (opt.equals(":produce-interpolants"))) {
			return;
		}
		
		super.setOption(opt, value);
	}
	
	/**
	 * NOTE: Setting the logics more than once messes up the Isabelle files.
	 */
	@Override
	public void setLogic(Logics logic) {
		super.setLogic(logic);
		
		// write Isabelle header
		try {
			// import linear arithmetic theory only when necessary
			final String imports;
			if (logic.isArithmetic()) {
				imports = "XLinearArithmetic";
			} else {
				imports = "XBool";
			}
			
			// main file
			mFile.append("theory SMTTheory\nimports ");
			mFile.append(imports);
			mFile.append(" ");
			mFile.append(mLemmaFileName);
			mFile.append("\nbegin\n");
			
			// lemma file
			mLemmaFile.append("theory ");
			mLemmaFile.append(mLemmaFileName);
			mLemmaFile.append("\nimports ");
			mLemmaFile.append(imports);
			mLemmaFile.append("\nbegin\n");
		} catch (final IOException e) {
			throw new RuntimeException(e);
		}
		
		// set up the term converter
		mConverter = new TermConverter(mFile, logic, mPrettyOutput);
		mProofConverter = new ProofConverter(mFile, super.getTheory(),
				mPrettyOutput, mConverter, mFastProofs, mPartialProof,
				mLemmaFile);
	}
	
	@Override
	public void defineFun(String fun, TermVariable[] params, Sort resultSort,
			Term definition) throws SMTLIBException {
		super.defineFun(fun, params, resultSort, definition);
		
		assert (mConverter != null);
		final String name = mConverter.toCompatibleString(fun);
		final String arrow = mPrettyOutput ? "\\<Rightarrow>" : "=>";
		
		try {
			mLemmaFile.append("\ndefinition ");
			mLemmaFile.append(name);
			mLemmaFile.append("::\"");
			for (int i = 0; i < params.length; ++i) {
				mLemmaFile.append(mConverter.getSingleSortString(
						params[i].getDeclaredSort()));
				mLemmaFile.append(arrow);
			}
			mLemmaFile.append(
					mConverter.getSingleSortString(resultSort));
			mLemmaFile.append("\" where ");
			mLemmaFile.append(name);
			mLemmaFile.append("_def:\"");
			mLemmaFile.append(name);
			mLemmaFile.append(" == ");
			if (params.length > 0) {
				String append = "%";
				for (int i = 0; i < params.length; ++i) {
					mLemmaFile.append(append);
					append = " ";
					mConverter.convertToAppendable(params[i], mLemmaFile);
				}
				mLemmaFile.append(". ");
			}
			mConverter.convertToAppendable(definition, mLemmaFile);
			mLemmaFile.append("\"\n");
		} catch (final IOException e) {
			throw new RuntimeException(e);
		}
	}
	
	/**
	 * {@inheritDoc}
	 * 
	 * The term must be recognized later in @asserted proof nodes
	 * In the extended proof mode, the term is put in a hash map.
	 * In the partial proof mode the term is annotated with a unique string,
	 * since it may change.
	 */
	@Override
	public LBool assertTerm(Term term) throws SMTLIBException,
			UnsupportedOperationException {
		if (mPartialProof) {
			if (term instanceof AnnotatedTerm) {
				final AnnotatedTerm aTerm = (AnnotatedTerm)term;
				// unpack :named annotation and pack it into a new one
				if ((aTerm.getAnnotations().length == 1)
					&& (aTerm.getAnnotations()[0].getKey().
							equals(PARTIAL_ANNOTATION))) {
					term = aTerm.getSubterm();
				}
			}
			return super.assertTerm(annotate(term,
					new Annotation(PARTIAL_ANNOTATION, ASSERTION_PREFIX
							+ ++mAssertionNumber)));
		}
		mAssertion2index.put(new FormulaUnLet().unlet(term),
				++mAssertionNumber);
		return super.assertTerm(term);
	}
	
	/**
	 * {@inheritDoc}
	 * 
	 * The method is overwritten to extract the proof.
	 * Both the theorem and the proof are translated into a form Isabelle
	 * understands and then Isabelle checks the proof.
	 */
	@Override
	public LBool checkSat() throws SMTLIBException {
		final LBool result = super.checkSat();
		
		// write unsatisfiability proof
		if (result == LBool.UNSAT) {
			final Term proof = super.getProof();
			
			try {
				// convert theorem and proof to a form Isabelle understands
				convertTheorem();
				mProofConverter.convert(proof, mAssertion2index);
			} catch (final IOException e) {
				e.printStackTrace();
				
				// close the writer before returning
				try {
					mFile.close();
					mLemmaFile.close();
				} catch (final IOException eWriter) {
					eWriter.printStackTrace();
				}
			}
		}
		
		return result;
	}
	
	@Override
	public void exit() {
		// write last line and close files
		try {
			mFile.append("\nend");
			mFile.close();
			
			mLemmaFile.append("\nend");
			mLemmaFile.close();
			
			// call Isabelle on the proof file
			if (mUseIsabelle) {
				callIsabelle(createIsabelleFile().getName());
			}
		} catch (final IOException e) {
			e.printStackTrace();
		}
		
		super.exit();
	}
	
	/**
	 * This method adds a function declaration to the lemma file.
	 * 
	 * @param fun the function name
	 * @param paramSorts the parameter sorts
	 * @param resultSort the result sort
	 * @param lineFeed true iff a line feed should be printed
	 */
	private void declareConst(final String fun, final Sort[] paramSorts,
			final Sort resultSort, final boolean lineFeed) {
		assert (mConverter != null);
		final String name = mConverter.toCompatibleString(fun);
		final String arrow = mPrettyOutput ? "\\<Rightarrow>" : "=>";
		
		try {
			mLemmaFile.append("consts ");
			mLemmaFile.append(name);
			mLemmaFile.append("::\"");
			for (int i = 0; i < paramSorts.length; ++i) {
				mLemmaFile.append(
						mConverter.getSingleSortString(paramSorts[i]));
				mLemmaFile.append(arrow);
			}
			mLemmaFile.append(
					mConverter.getSingleSortString(resultSort));
			if (lineFeed) {
				mLemmaFile.append("\"\n");
			} else {
				mLemmaFile.append("\"");
			}
		} catch (final IOException e) {
			throw new RuntimeException(e);
		}
	}
	
	/**
	 * This method converts an SMT-LIB theorem to an Isabelle theorem.
	 * The SMT-LIB theorem is given in the form of asserted formulae.
	 * 
	 * @throws IOException thrown by appendable
	 */
	public void convertTheorem() throws IOException {
		// theorem
		mFile.append("\ntheorem\n");
		
		// antecedents
		mFile.append("assumes ");
		String append = "";
		if (mPartialProof) {
			for (final Term term : super.getAssertions()) {
				mFile.append(append);
				append = "and ";
				
				// give the premise a name
				assert (term instanceof AnnotatedTerm);
				final AnnotatedTerm aTerm = (AnnotatedTerm)term;
				final Annotation[] annotations = aTerm.getAnnotations();
				assert (annotations.length == 1);
				assert annotations[0].getKey().equals(PARTIAL_ANNOTATION);
				
				mFile.append(annotations[0].getValue().toString());
				mFile.append(": \"");
				
				final LinkedList<NamedWrapper> namedFuns =
						mConverter.convertAssertion(aTerm.getSubterm());
				// add functions bound by :named annotation
				for (final NamedWrapper wrapper : namedFuns) {
					addNamedBond(wrapper);
				}
				
				mFile.append("\"\n");
			}
		} else {
			assert (mAssertion2index.size() <= super.getAssertions().length);
			for (final Entry<Term, Integer> entry : mAssertion2index.entrySet()) {
				mFile.append(append);
				append = "and ";
				
				mFile.append(ASSERTION_PREFIX);
				mFile.append(Integer.toString(entry.getValue()));
				mFile.append(": \"");
				
				final LinkedList<NamedWrapper> namedFuns =
						mConverter.convertAssertion(entry.getKey());
				// add functions bound by :named annotation
				for (final NamedWrapper wrapper : namedFuns) {
					addNamedBond(wrapper);
				}
				
				mFile.append("\"\n");
			}
		}
		
		// consequent
		mFile.append("shows \"False\"\n");
	}
	
	/**
	 * This method adds a function definition via the :named annotation
	 * to the Isabelle lemma file.
	 * 
	 * @param wrapper function wrapper
	 */
	private void addNamedBond(final NamedWrapper wrapper) {
		// ignore already defined terms
		if (!mNamedSet.add(wrapper.mName)) {
			return;
		}
		
		// constant declaration
		declareConst(wrapper.mName, new Sort[0],
				wrapper.mSubterm.getSort(), false);
		
		// constant definition
		assert (mConverter != null);
		final String name = mConverter.toCompatibleString(wrapper.mName);
		
		try {
			mLemmaFile.append(" defs ");
			mLemmaFile.append(name);
			mLemmaFile.append("_def: \"");
			mLemmaFile.append(name);
			mLemmaFile.append(" == ");
			mConverter.convertWithTypes(wrapper.mSubterm, mLemmaFile);
			mLemmaFile.append("\"\n");
		} catch (final IOException e) {
			throw new RuntimeException(e);
		}
	}
	
	/**
	 * This method creates a file for Isabelle to the disc.
	 * 
	 * @return empty file
	 * @throws IOException thrown iff creation fails
	 */
	private File createIsabelleFile() throws IOException {
		return new File(mFileName + ".thy");
	}
	
	/**
	 * This method creates a file for the lemmata to the disc.
	 * 
	 * @return empty file
	 * @throws IOException thrown iff creation fails
	 */
	private File createTheoryFile() throws IOException {
		return new File(mLemmaFileName + ".thy");
	}
	
	/**
	 * This method calls Isabelle on the written proof file and receives the
	 * result (which is: has Isabelle accepted the proof or not).
	 * 
	 * @param filename the file name
	 * @throws IOException thrown iff reading Isabelle output fails
	 */
	private void callIsabelle(String filename) throws IOException {
		Runtime.getRuntime().exec(new String[]{"isabelle", "emacs", filename});
	}
}
