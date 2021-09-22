importScripts("classes.js");
var runWebInterface;

onmessage = ((ev) => {
    runWebInterface.runSMTInterpol(ev.data);
    self.postMessage("@EXIT");
    self.close();
});

main();
