importScripts("classes.js");
var runWebInterface;

var proofMode = 0;
var script;

onmessage = ((ev) => {
    if (proofMode == 1) {
	script = ev.data;
	proofMode = 2;
    } else if (proofMode == 2) {
	runWebInterface.runProofChecker(script, ev.data);
	self.postMessage("@EXIT");
	self.close();
	script = "";
	proofMode = 0;
    } else if (ev.data == "proofcheck") {
	proofMode = 1;
    } else {
	runWebInterface.runSMTInterpol(ev.data);
	self.postMessage("@EXIT");
	self.close();
    }
});

main();
