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

import java.util.LinkedHashMap;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.logic.SMTLIBException;
import de.uni_freiburg.informatik.ultimate.smtinterpol.DefaultLogger;
import de.uni_freiburg.informatik.ultimate.smtinterpol.LogProxy;

/**
 * A map to handle all options supported by SMTInterpol.  The map provides
 * general methods to set and get values for options based on the options name.
 * If the option is unknown, the methods will throw an
 * UnsupportedOperationException.
 * 
 * The options are group into front end options and solver options.  The front
 * end options contain all options only used by the {@link ParseEnvironment}.
 * The solver options contain all options used by the solver whether created to
 * be used from command line or through its API.
 * 
 * The diagnostic output channel option has a special role.  Since we are
 * working with {@link LogProxy}s, we might not be able to change the logging
 * destination.  Thus, only if the logger to be used is a {@link DefaultLogger},
 * we set up this option.
 * 
 * The front end options are not set up by default.  If they are needed, the
 * method {@link #createFrontEndOptions()} has to be called.
 * 
 * The map maintains a flag representing the current state of the solver.  If
 * this flag is turned on, all options that are not configured to be online
 * modifiable cannot be modified anymore.  Attempting to do so will throw a
 * {@link SMTLIBException}.
 * @author Juergen Christ
 */
public class OptionMap {

	/**
	 * When copying this map, the options stored in this map can be either stay
	 * unchanged or be reset to their default value.  This is controlled by this
	 * enum.  The names are pretty self-expanatory.
	 * @author Juergen Christ
	 */
	public enum CopyMode {
		CURRENT_VALUE,
		RESET_TO_DEFAULT,
		/**
		 * Reset all options except for :regular-output-channel,
		 * :diagnostic-output-channel, and :verbosity.
		 */
		RESET_EXCEPT_CHANNELS
	}
	
	private final LinkedHashMap<String, Option> mOptions;
	private final SolverOptions mSolverOptions;
	private FrontEndOptions mFrontEndOptions;
	private final LogProxy mLogger;
	private boolean mOnline;

	/**
	 * Create a new option map and set up the solver options.  If the logger
	 * given is a {@link DefaultLogger}, we also set up the option
	 * <code>:diagnostic-output-channel</code> to configure this logger.
	 * @param logger The logger to be used by SMTInterpol.
	 */
	public OptionMap(LogProxy logger) {
		mOptions = new LinkedHashMap<String, Option>();
		mSolverOptions = new SolverOptions(this, logger);
		mLogger = logger;
		if (logger instanceof DefaultLogger) {
			addOption(":diagnostic-output-channel", new ChannelOption("stderr",
					(DefaultLogger) logger, true, "Where to print "
						+ "diagnostic output to.  Use \"stdout\" for standard "
						+ "output and \"stderr\" for standard error."));
		}
		mOnline = false;
	}
	
	private OptionMap(LogProxy logger, LinkedHashMap<String, Option> options) {
		mOptions = options;
		mSolverOptions = new SolverOptions(this);
		mLogger = logger;
		mOnline = false;
	}
	
	/**
	 * Set the option map into online mode.  From now on, all options that are
	 * not online modifiable cannot be modified anymore.
	 */
	public void setOnline() {
		mOnline = true;
	}
	
	/**
	 * Get the logger used to construct this option map.
	 * @return The logger used to construct this option map.
	 */
	public final LogProxy getLogProxy() {
		return mLogger;
	}
	
	public final SolverOptions getSolverOptions() {
		return mSolverOptions;
	}
	
	public final FrontEndOptions createFrontEndOptions() {
		return mFrontEndOptions = new FrontEndOptions(this);
	}
	
	public final FrontEndOptions getFrontEndOptions() {
		return mFrontEndOptions;
	}

	public void addOption(String name, Option option) {
		mOptions.put(name, option);
	}
	
	/**
	 * Get the current value of an option.  If the option is unknown to this
	 * option map, a <code>UnsupportedOperationException</code> will be thrown.
	 * @param option To option whose value should be retrieved.
	 * @return The current value of this option.
	 */
	public Object get(String option) {
		Option o = mOptions.get(option);
		if (o == null)
			throw new UnsupportedOperationException();
		return o.get();
	}
	
	/**
	 * Set the value of an option.  The option map relies on the caller of this
	 * function to correctly 
	 * @param option
	 * @param value
	 */
	public void set(String option, Object value) {
		Option o = mOptions.get(option);
		if (o == null)
			throw new UnsupportedOperationException();
		if (mOnline && !o.isOnlineModifiable())
			throw new SMTLIBException("Option " + option
					+ " can only be changed before setting the logic");
		o.set(value);
	}
	
	/**
	 * Get all known option names.
	 * @return All known option names.
	 */
	public String[] getInfo() {
		return mOptions.keySet().toArray(new String[mOptions.size()]);
	}
	
	/**
	 * Get information about a specific option.  The information contains the
	 * description, the default value, and the online modifiable state of this
	 * option.  If the option is unknown, an 
	 * <code>UnsupportedOperationException</code> will be thrown.
	 * @param option The option to get information for.
	 * @return Information for this option.
	 */
	public Object[] getInfo(String option) {
		Option o = mOptions.get(option);
		if (o == null)
			throw new UnsupportedOperationException();
		if (o.isOnlineModifiable())
			return new Object[] {
				":description", o.getDescription(), ":default",
				o.defaultValue(), ":online-modifiable" };
		return new Object[] {
			":description", o.getDescription(), ":default",
				o.defaultValue() };
	}
	
	/**
	 * Reset every option to its default value and set the map back to offline
	 * state.
	 */
	public void reset() {
		mOnline = false;
		for (Option o : mOptions.values())
			o.reset();
	}

	public OptionMap copy(CopyMode mode) {
		LinkedHashMap<String, Option> options = new LinkedHashMap<String, Option>();
		for (Map.Entry<String, Option> me : mOptions.entrySet()) {
			Option cpy = me.getValue().copy();
			switch(mode) {
			case CURRENT_VALUE:
				break;
			case RESET_EXCEPT_CHANNELS:
				if (cpy instanceof VerbosityOption || cpy instanceof ChannelOption)
					break;
				// FALLTHROUGH
			default:
				cpy.reset();
			}
			options.put(me.getKey(), cpy);
		}
		return new OptionMap(mLogger, options);
	}
	
	Option getOption(String key) {
		return mOptions.get(key);
	}
}
