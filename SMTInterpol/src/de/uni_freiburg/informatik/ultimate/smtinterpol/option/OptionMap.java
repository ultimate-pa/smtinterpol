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

import java.math.BigInteger;
import java.util.LinkedHashMap;
import java.util.Map.Entry;

import de.uni_freiburg.informatik.ultimate.logic.SMTLIBException;

public class OptionMap {
	private static abstract class Option {
		protected final OptionHandler mHandler;
		protected final int mUserData;
		private final OptionChangeStage mStage;
		private final String mDescription;
		public Option(OptionHandler handler, int userData,
				OptionChangeStage stage, String description) {
			mHandler = handler;
			mUserData = userData;
			mStage = stage;
			mDescription = description;
		}
		public abstract void setValue(String option, Object value);
		public abstract Object getValue(String option);
		public final OptionChangeStage getStage() {
			return mStage;
		}
		public final String getDescription() {
			return mDescription;
		}
	}
	
	private static class BooleanOption extends Option {
		
		public BooleanOption(OptionHandler handler, int userData,
				OptionChangeStage stage, String description) {
			super(handler, userData, stage, description);
		}

		@Override
		public void setValue(String option, Object value) {
			boolean val = true;
			if (value instanceof Boolean)
				val = ((Boolean) value).booleanValue();
			else if (value instanceof String) {
				// Unfortunately, Boolean.parseBoolean(String) is too crude.
				String sval = (String) value;
				if (sval.equalsIgnoreCase("true"))
					val = true;
				else if (sval.equalsIgnoreCase("false"))
					val = false;
				else
					throw new SMTLIBException("Not a Boolean value " + value);
			}
			mHandler.setBooleanOption(option, val, mUserData);
		}

		@Override
		public Object getValue(String option) {
			return mHandler.getBooleanOption(option, mUserData);
		}
		
	}
	
	private static class StringOption extends Option {

		public StringOption(OptionHandler handler, int userData,
				OptionChangeStage stage, String description) {
			super(handler, userData, stage, description);
		}

		@Override
		public void setValue(String option, Object value) {
			String val =
					value instanceof String ? (String) value : String.valueOf(value);
			mHandler.setStringOption(option, val, mUserData);
		}

		@Override
		public Object getValue(String option) {
			return mHandler.getStringOption(option, mUserData);
		}
		
	}
	
	private static class NumericOption extends Option {

		public NumericOption(OptionHandler handler, int userData,
				OptionChangeStage stage, String description) {
			super(handler, userData, stage, description);
		}

		@Override
		public void setValue(String option, Object value) {
			BigInteger val = null;
			if (value instanceof BigInteger)
				val = (BigInteger) value;
			else if (value instanceof Integer)
				val = BigInteger.valueOf(((Integer) value).longValue());
			else if (value instanceof Long)
				val = BigInteger.valueOf(((Long) value).longValue());
			else if (value instanceof String) {
				try {
					val = new BigInteger((String) value);
				} catch (NumberFormatException enfe) {
					throw new SMTLIBException("Not a number: " + value, enfe);
				}
			}
			mHandler.setNumeralOption(option, val, mUserData);
		}

		@Override
		public Object getValue(String option) {
			return mHandler.getNumeralOption(option, mUserData);
		}
		
	}
	
	static enum OptionChangeStage {
		PRE_SET_LOGIC(1, "Option can only be set before set-logic") {
			@Override
			public String toSExpr() {
				return ":pre-set-logic";
			}
		},
		BEFORE_MODIFY_ASSERTION_STACK(2, "Option can only be set before "
				+ "the assertion stack gets changed") {
			@Override
			public String toSExpr() {
				return ":before-modify-assertion-stack";
			}
		},
		AFTER_MODIFY_ASSERTIONSTACK(4, "Option can only be set after the "
				+ "assertion stack gets changed") {
			@Override
			public String toSExpr() {
				return ":after-modify-assertion-stack";
			}
		},
		ALWAYS(7, "Option can always be changed") {
			@Override
			public String toSExpr() {
				return ":always";
			}
		};
		
		private OptionChangeStage(int stage, String msg) {
			mStage = stage;
			mMsg = msg;
		}
		private final int mStage;
		private final String mMsg;
		public String isChangeable(OptionChangeStage current) {
			return (current.mStage & mStage) == 0 ? mMsg : null;
		}
		public abstract String toSExpr();
	}
	
	private final LinkedHashMap<String, Option> mOptions;
	private OptionChangeStage mStage;
	
	public OptionMap() {
		mOptions = new LinkedHashMap<String, Option>();
		mStage = OptionChangeStage.PRE_SET_LOGIC;
	}
	
	public void setLogic() {
		mStage = OptionChangeStage.BEFORE_MODIFY_ASSERTION_STACK;
	}
	
	public void modifyAssertionStack() {
		mStage = OptionChangeStage.AFTER_MODIFY_ASSERTIONSTACK;
	}
	
	public void registerBooleanOption(String option, OptionHandler handler,
			int userData, OptionChangeStage stage, String description) {
		if (mOptions.containsKey(option))
			throw new SMTLIBException("Option \"" + option + "\" already exists");
		mOptions.put(option,
				new BooleanOption(handler, userData, stage, description));
	}
	
	public void registerStringOption(String option, OptionHandler handler,
			int userData, OptionChangeStage stage, String description) {
		if (mOptions.containsKey(option))
			throw new SMTLIBException("Option \"" + option + "\" already exists");
		mOptions.put(option,
				new StringOption(handler, userData, stage, description));
	}
	
	public void registerNumericOption(String option, OptionHandler handler,
			int userData, OptionChangeStage stage, String description) {
		if (mOptions.containsKey(option))
			throw new SMTLIBException("Option \"" + option + "\" already exists");
		mOptions.put(option,
				new NumericOption(handler, userData, stage, description));
	}
	
	private Option findOption(String option) {
		Option o = mOptions.get(option);
		if (o == null)
			throw new SMTLIBException("Unknown option: \"" + option + "\"");
		return o;
	}
	
	public void setOption(String option, Object value) {
		Option o = findOption(option);
		String msg = o.getStage().isChangeable(mStage);
		if (msg != null)
			throw new SMTLIBException(msg);
		o.setValue(option, value);
	}
	
	public Object getOption(String option) {
		Option o = findOption(option);
		return o.getValue(option);
	}
	
	public String getInfo() {
		StringBuilder sb = new StringBuilder();
		String spacer = "";
		for (String key : mOptions.keySet()) {
			sb.append(spacer).append(key);
			spacer = " ";
		}
		return sb.toString();
	}
	
	public String getInfo(String option) {
		Option o = findOption(option);
		return o.getDescription() + " " + o.getStage().toSExpr();
	}
}
