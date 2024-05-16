Bugs Found by Proof Checker
===========================

2024-05-16: recheckTrigger()

In DataTypeTheory.recheckTrigger the code assumed that a 
trigger on an "(_ is cons1)" can only be for a cons1 constructor
call, even though the trigger code is also produced for different
constructors to propagate ((_ is cons1) (cons2 ...)) to false.

This triggers an assertion violation in this function, but when
running without assertions, this is ignored.  The recheck trigger
function propagates ((_ is cons1) (cons2 ...)) to true instead of
false.  This finally leads to an invalid proof which is only caught
by the proof checker (the proof simplifier would also have thrown
an assertion error if assertions were enabled).

To summarize, because we disabled assertions, a simple bug in the
recheck trigger code was escalating to a wrong solver result, which
was only finally caught by the proof checker.
