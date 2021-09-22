# Webinterface SMTInterpol

This is a simple implemented Webinterface for SMTInterpol. ( SMTInterpol is an interpolating SMT-solver developed at the university of Freiburg. You can find more information on the following [website](http://ultimate.informatik.uni-freiburg.de/smtinterpol/) )

# Compilation

To compile SMTInterpol you need:
- Java
- Maven

SMTInterpol comes with a Maven build file(pom.xml) that compiles the sources into a target folder (will be created by the build). In the targed folder you will find a smtinterpol-web-1.0-SNAPSHOT folder where all the needed files to run the Interface are.

You can run the build with: mvn (clean) package

# Usage

To run the Webinterface you just have to open
  `target/smtinterpol-web-1.0-SNAPSHOT/index.html` 
in your browser.
The usage of the interface in the browser should be self explanatory.

# Reporting Bugs

Reporting Bugs
You can report bugs using the [bug-tracker](https://github.com/ultimate-pa/smtinterpol/issues) at github. Please provide all needed information. This includes:

- a description of the bug (e.g., crash, unsoundness, or feature-request),
- a way to reproduce the bug (e.g., an interaction log with the solver via the LoggingScript provided with the sources).
