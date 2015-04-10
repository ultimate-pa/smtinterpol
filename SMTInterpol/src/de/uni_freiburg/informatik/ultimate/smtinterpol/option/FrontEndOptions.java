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

import java.io.PrintWriter;

/**
 * Collection of options specific to the usage of a {@link ParseEnvironment}.
 * @author Juergen Christ
 */
public class FrontEndOptions {
	private final BooleanOption mPrintSuccess;
	private ChannelOption mOut;
	private final BooleanOption mPrintTermsCSE;

	private final static String REG_OUT_CHANNEL_NAME = ":regular-output-channel";
	private final static String REG_OUT_CHANNEL_DEF = "stdout";
	private final static String REG_OUT_CHANNEL_DESC =
			"Where to print command responces to.  Use \"stdout\" for standard "
				+ "output and \"stderr\" for standard error.";

	FrontEndOptions(OptionMap options) {
		mPrintSuccess = (BooleanOption) options.getOption(":print-success");
		mPrintTermsCSE = (BooleanOption) options.getOption(":print-terms-cse");
	}

	FrontEndOptions(OptionMap options, boolean active) {
		mPrintSuccess = new BooleanOption(true, true, "Print \"success\" after "
				+ "successful command executions that would otherwise not "
				+ "produce feedback.");
		mPrintTermsCSE = new BooleanOption(true, true,
				"Eliminate common subexpressions before printing terms.");
		options.addOption(":print-success", mPrintSuccess);
		if (active)
			activateFrontEnd(options);
		else
			options.addOption(REG_OUT_CHANNEL_NAME,
				new StringOptionWithWarning(REG_OUT_CHANNEL_DEF, true,
						REG_OUT_CHANNEL_DESC, 
						"Front End not active.  Option change will not have an effect!",
						options.getLogProxy()));
		options.addOption(":print-terms-cse", mPrintTermsCSE);
	}
	
	void activateFrontEnd(OptionMap options) {
		mOut = new ChannelOption(REG_OUT_CHANNEL_DEF, true, REG_OUT_CHANNEL_DESC);
		options.addOption(REG_OUT_CHANNEL_NAME, mOut);
	}
	
	public final boolean isPrintSuccess() {
		return mPrintSuccess.getValue();
	}
	
	public PrintWriter getOutChannel() {
		return mOut.getChannel();
	}
	
	public final boolean isPrintTermsCSE() {
		return mPrintTermsCSE.getValue();
	}
}
