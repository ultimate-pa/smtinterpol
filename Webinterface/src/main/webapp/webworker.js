importScripts("classes.js");
var runWebInterface;

self.addEventListener('message', (ev)=>{
    console.log('Web worker started.');

    let data = ev.data;
    switch(data){
        default:
        runWebInterface.runSMTInterpol(data);
	self.postMessage("@EXIT");
        self.close();
        break;
    }
});

main();
