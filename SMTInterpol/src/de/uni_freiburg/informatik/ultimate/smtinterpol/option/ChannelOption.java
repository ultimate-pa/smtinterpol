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

import java.io.FileWriter;
import java.io.IOException;
import java.io.PrintWriter;

import de.uni_freiburg.informatik.ultimate.logic.SMTLIBException;

/**
 * An option specialized for output channels.  This option supports strings to
 * describe the channels according to SMTLIB specifications, i.e., either file
 * names, "stdout", or "stderr".  This option is designed to be usable either
 * for direct storage of a PrintWriter or a wrapped PrintWriter used, e.g., by
 * a {@link DefaultLogger}. 
 * @author Juergen Christ.
 *
 */
public class ChannelOption extends Option {

	/**
	 * A wrapper for a PrintWriter.
	 * @author Juergen Christ
	 */
	public static interface ChannelHolder {
		PrintWriter getChannel();
		void setChannel(PrintWriter writer);
	}
	
	private String mName;
	private final String mDefaultName;
	private final ChannelHolder mHolder;

	public ChannelOption(String defaultChannel, ChannelHolder holder,
			boolean onlineModifiable, String description) {
		super(onlineModifiable, description);
		mHolder = holder;
		createChannel(defaultChannel);
		mName = mDefaultName = defaultChannel;
	}
	@Override
	public Option copy() {
		return this; // Cannot copy channel option.  Does not make sense!
	}
	@Override
	public void set(Object value) {
		String val = value.toString();
		createChannel(val);
		mName = val;
	}

	@Override
	public Object get() {
		return mName;
	}

	@Override
	public void reset() {
		createChannel(mName);
		mName = mDefaultName;
	}

	@Override
	public Object defaultValue() {
		return mDefaultName;
	}
	
	private void createChannel(String file) {
		if ("stdout".equals(file))
			mHolder.setChannel(new PrintWriter(System.out));
		else if ("stderr".equals(file))
			mHolder.setChannel(new PrintWriter(System.err));
		else {
			try {
				mHolder.setChannel(new PrintWriter(new FileWriter(file)));
			} catch (IOException eIO) {
				throw new SMTLIBException(eIO);
			}
		}
	}

}
