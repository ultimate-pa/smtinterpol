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
package de.uni_freiburg.informatik.ultimate.smtinterpol.delta;

import java.io.PrintWriter;
//import java.util.Arrays;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.logic.PrintTerm;
import de.uni_freiburg.informatik.ultimate.logic.Term;

public class GetInterpolants extends Cmd {
	
	private Term[] mPartition, mOldPartition;
	private int[] mSos, mOldSos;
	
	public GetInterpolants(Term[] partition, int[] sos) {
		mPartition = partition;
		mSos = sos;
	}

	@Override
	public void dump(PrintWriter writer) {
		// Copied from LoggingScript...
		writer.print("(get-interpolants ");
		PrintTerm pt = new PrintTerm();
		pt.append(writer, mPartition[0]);
		for (int i = 1; i < mPartition.length; ++i) {
			int prevStart = mSos[i - 1];
			while (mSos[i] < prevStart) {
				writer.print(')');
				prevStart = mSos[prevStart - 1];
			}
			writer.print(' ');
			if (mSos[i] == i)
				writer.print('(');
			pt.append(writer, mPartition[i]);
		}
		writer.println(')');
	}
	
	public Term[] getPartition() {
		return mPartition;
	}
	public int[] getStartOfSubtree() {
		return mSos;
	}
	
	public void setNewPartition(Term[] newPartition) {
		mOldPartition = mPartition;
		mPartition = newPartition;
	}
	public void setNewStartOfSubtree(int[] newSos) {
		mOldSos = mSos;
		mSos = newSos;
	}
	
	public void failure() {
		mPartition = mOldPartition;
		mSos = mOldSos;
	}
	public void success() {
//		System.err.println("New partition: " + Arrays.toString(mPartition) + "/" + Arrays.toString(mSos));
		mOldPartition = null;
		mOldSos = null;
	}
	
	public String toString() {
		return "GET_INTERPOLANTS";
	}

	@Override
	public void checkFeature(Map<String, Cmd> features) {
		features.remove(":produce-interpolants");
	}

}
