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
package de.uni_freiburg.informatik.ultimate.smtinterpol.samples.util;

import java.io.IOException;

import org.apache.log4j.Level;
import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.smtinterpol.LogProxy;

/**
 * Sample LogProxy implementation for the Log4j version 1.2 logging system.
 * This implementation might serve as a basic for implementing the LogProxy
 * interface interface for different logging systems.
 * @author Juergen Christ
 */
public class Log4jProxy implements LogProxy {

	/**
	 * A wrapper used to call <code>String.format</code> to produce the string
	 * representation of this object.
	 * @author Juergen Christ
	 */
	private static class StringFormatter {
		private final String mFormat;
		private final Object[] mArgs;
		public StringFormatter(String format, Object[] args) {
			mFormat = format;
			mArgs = args;
		}
		public String toString() {
			return String.format(mFormat, mArgs);
		}
	}
	
	private final Logger mLogger;
	
	public Log4jProxy(Logger logger) {
		mLogger = logger;
	}
	
	@Override
	public void setLoglevel(int level) {
		switch(level) {
		case LogProxy.LOGLEVEL_OFF:
			mLogger.setLevel(Level.OFF);
			break;
		case LogProxy.LOGLEVEL_FATAL:
			mLogger.setLevel(Level.FATAL);
			break;
		case LogProxy.LOGLEVEL_ERROR:
			mLogger.setLevel(Level.ERROR);
			break;
		case LogProxy.LOGLEVEL_WARN:
			mLogger.setLevel(Level.WARN);
			break;
		case LogProxy.LOGLEVEL_INFO:
			mLogger.setLevel(Level.INFO);
			break;
		case LogProxy.LOGLEVEL_DEBUG:
			mLogger.setLevel(Level.DEBUG);
			break;
		case LogProxy.LOGLEVEL_TRACE:
			mLogger.setLevel(Level.TRACE);
			break;
		default:
			throw new InternalError("Unknown loglevel: " + level);
		}
	}

	@Override
	public int getLoglevel() {
		Level lvl = mLogger.getLevel();
		if (lvl == Level.OFF)
			return LogProxy.LOGLEVEL_OFF;
		if (lvl == Level.FATAL)
			return LogProxy.LOGLEVEL_FATAL;
		if (lvl == Level.ERROR)
			return LogProxy.LOGLEVEL_ERROR;
		if (lvl == Level.WARN)
			return LogProxy.LOGLEVEL_WARN;
		if (lvl == Level.INFO)
			return LogProxy.LOGLEVEL_INFO;
		if (lvl == Level.DEBUG)
			return LogProxy.LOGLEVEL_DEBUG;
		if (lvl == Level.TRACE)
			return LogProxy.LOGLEVEL_TRACE;
		throw new InternalError("Unknown loglevel: " + lvl);
	}

	@Override
	public boolean isFatalEnabled() {
		return mLogger.isEnabledFor(Level.FATAL);
	}

	@Override
	public void fatal(String msg, Object... params) {
		mLogger.fatal(new StringFormatter(msg, params));
	}

	@Override
	public void fatal(Object msg) {
		mLogger.fatal(msg);
	}

	@Override
	public void outOfMemory(String msg) {
		/* Do not implement this.  Log4j produces a LogRecord that needs
		 * additional memory quite likely causing the next OutOfMemoryError to
		 * be thrown.
		 */
	}

	@Override
	public boolean isErrorEnabled() {
		return mLogger.isEnabledFor(Level.ERROR);
	}

	@Override
	public void error(String msg, Object... params) {
		mLogger.error(new StringFormatter(msg, params));
	}

	@Override
	public void error(Object msg) {
		mLogger.error(msg);
	}

	@Override
	public boolean isWarnEnabled() {
		return mLogger.isEnabledFor(Level.WARN);
	}

	@Override
	public void warn(String msg, Object... params) {
		mLogger.warn(new StringFormatter(msg, params));
	}

	@Override
	public void warn(Object msg) {
		mLogger.warn(msg);
	}

	@Override
	public boolean isInfoEnabled() {
		return mLogger.isInfoEnabled();
	}

	@Override
	public void info(String msg, Object... params) {
		mLogger.info(new StringFormatter(msg, params));
	}

	@Override
	public void info(Object msg) {
		mLogger.info(msg);
	}

	@Override
	public boolean isDebugEnabled() {
		return mLogger.isDebugEnabled();
	}

	@Override
	public void debug(String msg, Object... params) {
		mLogger.debug(new StringFormatter(msg, params));
	}

	@Override
	public void debug(Object msg) {
		mLogger.debug(msg);
	}

	@Override
	public boolean isTraceEnabled() {
		return mLogger.isTraceEnabled();
	}

	@Override
	public void trace(String msg, Object... params) {
		mLogger.trace(new StringFormatter(msg, params));
	}

	@Override
	public void trace(Object msg) {
		mLogger.trace(msg);
	}

	@Override
	public boolean canChangeDestination() {
		// I assume the loger is managed by some external log4j configurator.
		return false;
	}

	@Override
	public void changeDestination(String newDest) throws IOException {
		throw new InternalError("This should never be called!");
	}

	@Override
	public String getDestination() {
		return mLogger.getName(); // Essentially a dummy
	}

}
