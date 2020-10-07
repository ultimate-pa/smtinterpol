importScripts("classes.js");
var runWebInterface;

self.addEventListener('message', (ev)=>{
    console.log('Web worker started with data: ', ev.data);

    let data = ev.data;
    switch(data){
        default:
            console.log("Hier wird aufgerufen");
            var output = runWebInterface.runSMTInterpol(data);
            console.log("Hier wurde aufgerufen");
            self.postMessage(output);
            break;
        case 'Stop SMTInterpol':
            runWebInterface.requestTermination();
            self.postMessage('Stop Web Worker');
            break;
    }
});

main();