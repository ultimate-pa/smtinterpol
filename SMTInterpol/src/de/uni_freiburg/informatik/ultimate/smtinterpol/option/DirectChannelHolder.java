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

import de.uni_freiburg.informatik.ultimate.smtinterpol.option.ChannelOption.ChannelHolder;

/**
 * A direct wrapper around a PrintWriter.
 * @author Juergen Christ
 */
public class DirectChannelHolder implements ChannelHolder {
	private PrintWriter mWriter;
	public PrintWriter getChannel() {
		return mWriter;
	}
	public void setChannel(PrintWriter writer) {
		mWriter = writer;
	}
}
