importScripts("classes.js");
var runWebInterface;
var counter = 1;

self.addEventListener('message', (ev)=>{
    console.log('Web worker started.');

    let data = ev.data;
    switch(data){
        default:
            console.log("Versuch aufzurufen, counter: ", counter);
            // Zuweiss auf eine Variable kann man vielleicht nicht stoppen.
            var output = runWebInterface.runSMTInterpol(data);
            console.log("Aufruf erfolgreich, counter: ", counter);
            self.postMessage(output);
            counter += 1;
            self.close();
            break;
            /*
        case 'Stop SMTInterpol':
            console.log("Versuch thread zu stoppen");
            runWebInterface.requestTermination();
            console.log('Nach Webworker thread is stopped');
            break;
            */
    }
});

main();