/*
 * Copyright (C) 2014 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.smtinterpol.option;

import de.uni_freiburg.informatik.ultimate.smtinterpol.Config;
import de.uni_freiburg.informatik.ultimate.smtinterpol.LogProxy;
import de.uni_freiburg.informatik.ultimate.smtinterpol.proof.Transformations.AvailableTransformations;
import de.uni_freiburg.informatik.ultimate.smtinterpol.smtlib2.SMTInterpol.CheckType;

/**
 * Options specific to the solver but independent of the front end.  To speed up
 * several tasks we provide caches for some of the options.
 * @author Juergen Christ
 */
public class SolverOptions {

	private final LongOption mTimeout = new LongOption(0, true, "Soft timeout "
			+ "in milliseconds for individual check-sat calls.  Values <= 0 "
			+ "deactivate the timeout.");
	private final BooleanOption mProduceProofs = new BooleanOption(false, false,
			"Produce proofs for unsatisfiable formulas.");
	private final LongOption mRandomSeed = new LongOption(Config.RANDOM_SEED,
			true, "Seed for the internal pseudo-random number generator.");
	private final BooleanOption mInterpolantCheckMode = new BooleanOption(
			false, false, "Check generated interpolants.");
	private final BooleanOption mProduceInterpolants = new BooleanOption(
			false, false, "Enable interpolant production.");
	private final BooleanOption mModelCheckMode = new BooleanOption(
			false, true,
			"Check satisfiable formulas against the produced model.");
	private final EnumOption<AvailableTransformations> mProofTrans = new
			EnumOption<AvailableTransformations>(AvailableTransformations.NONE,
					true, AvailableTransformations.class,
					"Algorithm used to transform the resolution proof tree.");
	private final BooleanOption mModelsPartial = new BooleanOption(false, true,
			"Don't totalize models.");
	private final EnumOption<CheckType> mCheckType = new EnumOption<CheckType>(
			CheckType.FULL, true, CheckType.class,
			"Strength of check used in check-sat command.");
	private final BooleanOption mSimpIps = new BooleanOption(false, true,
			"Apply strong context simplification to generated interpolants.");
	private final BooleanOption mProofCheckMode = new BooleanOption(false,
			false, "Check the produced proof for unsatisfiable formulas.");
	private final EnumOption<CheckType> mSimpCheckType = 
			new EnumOption<CheckType>(CheckType.QUICK, true, CheckType.class,
					"Strength of checks used by the strong context simplifier "
							+ "used in the simplify command");

	SolverOptions(OptionMap options, LogProxy logger) {
		// general standard compliant options
		options.addOption(":verbosity", new VerbosityOption(logger));
		options.addOption(":timeout", mTimeout);
		options.addOption(":random-seed", mRandomSeed);
		options.addOption(":interactive-mode", new BooleanOption(false, false,
				"Store asserted formulas for later retrieval."));
		// model options
		options.addOption(":produce-models", new BooleanOption(false, true,
				"Produce models for satisfiable formulas"));
		options.addOption(":models-partial", mModelsPartial);
		options.addOption(":model-check-mode", mModelCheckMode);
		options.addOption(":produce-assignments", new BooleanOption(false,
				false, "Produce assignments of named Boolean terms for "
				+ "satisfiable formulas"));
		
		// proof options
		options.addOption(":produce-proofs", mProduceProofs);
		options.addOption(":proof-transformation", mProofTrans);
		options.addOption(":proof-check-mode", mProofCheckMode);
		
		// interpolant options
		options.addOption(":produce-interpolants", mProduceInterpolants);
		options.addOption(":interpolant-check-mode", mInterpolantCheckMode);
		options.addOption(":simplify-interpolants", mSimpIps);
		
		// unsat core options
		options.addOption(":produce-unsat-cores", new BooleanOption(
				false, false, "Enable production of unsatisfiable cores."));
		options.addOption(":unsat-core-check-mode", new BooleanOption(
				false, false, "Check generated unsat cores"));
		
		// general non-standard options
		options.addOption(":check-type", mCheckType);
		
		// simplifier options
		options.addOption(":simplify-check-type", mSimpCheckType);
		options.addOption(":simplify-repeatedly", new BooleanOption(true, true,
				"Simplify until the fixpoint is reached."));
	}
	
	public final CheckType getCheckType() {
		return mCheckType.getValue();
	}
	
	public final void setCheckType(CheckType newCheckType) {
		mCheckType.set(newCheckType);
	}
	
	public final boolean isInterpolantCheckModeActive() {
		return mInterpolantCheckMode.getValue();
	}
	
	public final boolean isModelCheckModeActive() {
		return mModelCheckMode.getValue();
	}
	
	public final boolean isModelsPartial() {
		return mModelsPartial.getValue();
	}
	
	public final boolean isProduceInterpolants() {
		return mProduceInterpolants.getValue();
	}
	
	public final boolean isProduceProofs() {
		return mProduceProofs.getValue();
	}
	
	public final boolean isProofCheckModeActive() {
		return mProofCheckMode.getValue();
	}
	
	public final AvailableTransformations getProofTransformation() {
		return mProofTrans.getValue();
	}
	
	public final long getRandomSeed() {
		return mRandomSeed.getValue();
	}
	
	public final boolean isSimplifyInterpolants() {
		return mSimpIps.getValue();
	}
	
	public final long getTimeout() {
		return mTimeout.getValue();
	}
	
	public CheckType getSimplifierCheckType() {
		return mSimpCheckType.getValue();
	}
	
}
