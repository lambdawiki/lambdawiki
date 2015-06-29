var lc = require("./../lambda.js");
var rt = new lc();

var args = [].slice.call(process.argv,2);

if (args.length === 0) wrong();

var file_path = args.shift();

var opts = {};

while (args[0] && args[0][0] === "-"){
    var opt = args.shift();
    opts[opt.slice(/[^-]/.exec(opt).index).toLowerCase().replace("to-","")] = true;
};

if (Object.keys(opts).length === 0)
    opts.normalize = true;

if (opts.help) help();

try {
    rt.readSource(require("fs").readFileSync("./"+file_path,"utf8"));
} catch (e){
    console.log(e);
    process.exit();
};

if (args.length === 0)
    args.push("main");

args.map(compile);

if (opts["generate-javascript"]){
    console.log(rt.generateJavascriptLibrary(args));
};


function wrong(){
    console.log("You are doing it wrong!");
    console.log("");
    help();
};

function help(){
    console.log("Usage   : lambda file [opts] function1 function2 ...");
    console.log("Example : lambda file.lc --onlycode --compute --to-javascript --stats main");
    console.log("(This example reads the function `main` from `file.lc`, pretifies, normalizes and compiles it.)");
    console.log("");
    console.log("Opts can be:");
    console.log("--verbose             : outputs human-friendly comments.");
    console.log("--expand              : outputs expanded term (before normalization).");
    console.log("--normalize           : outputs computed term (after normalization).");
    console.log("--bruijn              : prints the compilation result as bruijn indices.");
    console.log("--stats               : prints some stats of the compilation.");
    console.log("--scheme              : prints compilation to Scheme.");
    console.log("--to-javascript       : prints compilation to JavaScript.");
    console.log("--to-python           : prints compilation to Python.");
    console.log("--to-haskell          : prints compilation to Haskell.");
    console.log("--no-names            : don't include variable names on the compilation result.");
    console.log("--generate-javascript : generate compiled JavaScript code with runtime.");
    console.log("--all                 : prints everything.");
    process.exit();
};

function compile(symbol){
    if (opts["verbose"]){
        console.log("## Lambda: loading "+symbol+". ##");
        console.log("");
    };

    if (opts.bruijn || opts.all){
        if (opts.expand){
            if (opts["verbose"]) console.log("## Expanded term (bruijn-indexed). ##");
            console.log(rt.toString(rt.defs[symbol]));
            if (opts["verbose"]) console.log();
        };
        if (opts["verbose"]) console.log("## Normalized term (bruijn-indexed). ##");
        console.log(rt.toString(rt.normal(rt.defs[symbol])));
        if (opts["verbose"]) console.log();
    };

    if (opts.expand){
        if (opts["verbose"]) console.log("## Expanded term:");
        console.log(rt.show(rt.defs[symbol]));
        if (opts["verbose"]) console.log();
    };
    if (opts.normalize || opts.all){
        if (opts["verbose"]) console.log("## Normalized term: ##");
        console.log(rt.show(rt.normal(rt.defs[symbol])).replace(/ +(?= )/g,''));
        if (opts["verbose"]) console.log();
    };

    ["Scheme","JavaScript","Python","Haskell"].map(function(language){
        if (opts[language.toLowerCase()] || opts.all){
            if (opts["verbose"]) console.log("## Compiled to " + language + ". ##");
            console.log(rt.compileTo(language,rt.normal(rt.defs[symbol]),opts["no-names"] ? undefined : symbol));
            //console.log(rt.compileTo(language,rt.defs[symbol],opts["no-names"] ? undefined : symbol));
            if (opts["verbose"]) console.log();
        };
    });

    if (opts.stats || opts.all){
        console.log("## Stats. ##");
        console.log("-> Node count      :",rt.left_.length);
        console.log("-> Beta-reductions :",rt.stats.beta_reductions);
        console.log("-> Reductions      :",rt.stats.reductions,"("+(rt.stats.reductions-rt.stats.unmemoized_reductions)+" memoized)");
        console.log("-> Calls to subs   :",rt.stats.subs_calls,"("+(rt.stats.subs_calls-rt.stats.unmemoized_subs_calls)+" memoized)");
        console.log("-> Max var         :",rt.stats.max_var);
    };

};
