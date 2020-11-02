importScripts("classes.js");
var runWebInterface;

self.addEventListener('message', (ev)=>{
    console.log('Web worker started.');

    let data = ev.data;
    switch(data){
        default:
            var output = runWebInterface.runSMTInterpol(data);
            self.postMessage(output);
            self.close();
            break;
    }
});

main();