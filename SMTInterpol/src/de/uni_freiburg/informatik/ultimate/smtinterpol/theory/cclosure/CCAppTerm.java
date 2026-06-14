/*
 * Copyright (C) 2009-2012 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.smtinterpol.theory.cclosure;

import java.util.ArrayDeque;
import java.util.HashMap;

import de.uni_freiburg.informatik.ultimate.logic.FunctionSymbol;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.util.HashUtils;

public class CCAppTerm extends CCTerm {
	final FunctionSymbol mFunc;
	final CCTerm[] mArgs;
	/**
	 * The constant offset that is added to each argument: argument {@code i} of the represented application is
	 * {@code mArgs[i] + mArgOffsets[i]}. This lets a term like {@code f(x+5)} use the offset-free CCTerm {@code x} as
	 * its argument while remembering the {@code +5}. The array is {@code null} when every offset is zero (the common
	 * case), so plain congruence closure pays no extra cost.
	 */
	Rational[] mArgOffsets;
	Term mSmtTerm;

	CongruenceTrigger mCongTrigger;
	FindTriggerTrigger mFindTrigger;

	public CCAppTerm(FunctionSymbol fsym, final CCTerm[] args,
			final CClosure engine, final boolean isFromQuant) {
		super(HashUtils.hashJenkins(fsym.hashCode(), (Object[]) args), isFromQuant ? CCAppTerm.computeAge(args) : 0);
		mFunc = fsym;
		mArgs = args;
	}

	private final static int computeAge(CCTerm[] args) {
		int age = 1;
		for (int i = 0; i < args.length; i++) {
			age = Math.max(age, args[i].mAge + 1);
		}
		return age;
	}

	public FunctionSymbol getFunctionSymbol() {
		return mFunc;
	}

	public CCTerm[] getArguments() {
		return mArgs;
	}

	public CCTerm getArgument(int argPosition) {
		return mArgs[argPosition];
	}

	/**
	 * @return the constant offset added to the argument at the given position, i.e. the argument of the application is
	 *         {@code getArgument(argPosition) + getArgOffset(argPosition)}. Returns {@link Rational#ZERO} when no
	 *         offsets are stored.
	 */
	public Rational getArgOffset(int argPosition) {
		return mArgOffsets == null ? Rational.ZERO : mArgOffsets[argPosition];
	}

	/**
	 * The argument at the given position as a {@link CCParameter}, i.e. {@link #getArgument(int)} together with its
	 * structural {@link #getArgOffset(int)}. This is the uniform "an argument is a value up to a constant" view; a bare
	 * {@link CCTerm} is returned when the argument has no offset.
	 */
	public CCParameter getArgParam(int argPosition) {
		return CCParameter.of(mArgs[argPosition], getArgOffset(argPosition));
	}

	@Override
	public String toString() {
		final StringBuilder sb = new StringBuilder();
		final HashMap<CCAppTerm, Integer> visited = new HashMap<>();
		final ArrayDeque<Object> todo = new ArrayDeque<>();
		todo.add(this);
		while (!todo.isEmpty()) {
			final Object item = todo.removeLast();
			if (item instanceof String) {
				sb.append(item);
			} else if (item instanceof CCAppTerm) {
				final CCAppTerm app = (CCAppTerm) item;
				final Integer id = visited.get(item);
				if (id != null) {
					sb.append("@" + id);
				} else {
					visited.put(app, visited.size());
					todo.add(")");
					for (int i = app.mArgs.length - 1; i >= 0; i--) {
						if (!app.getArgOffset(i).equals(Rational.ZERO)) {
							todo.add("+" + app.getArgOffset(i));
						}
						todo.add(app.mArgs[i]);
						todo.add(" ");
					}
					todo.add(app.mFunc.getApplicationString());
					todo.add("(");
				}
			} else if (item instanceof CCBaseTerm) {
				sb.append(item);
			} else {
				throw new AssertionError("Unknown CCTerm " + item);
			}
		}
		return sb.toString();
	}
}
