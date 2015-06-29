// This is the parser/evaluator/compiler for the Lambda Calculus. It is written
// in JavaScript, but will slowly be rewritten on the Lambda Calculus itself.
var Lambda = (function(){
    var i32size = Math.pow(2,32);
    function Runtime(params){
        this.Lam      = this.prim(1000);
        var params    = params          || {};
        this.left_    = params.left_    || [];
        this.right_   = params.right_   || [];
        this.defs     = params.defs     || {};
        this.source   = params.source   || {};
        this.subsMemo = params.subsMemo || {};
        this.normMemo = params.normMemo || {};
        this.hash     = params.hahs     || {};
        this.stats    = {
            beta_reductions       : 0,
            reductions            : 0,
            unmemoized_reductions : 0,
            subs_calls            : 0,
            unmemoized_subs_calls : 0,
            max_var               : 0
        };
        if (!params.hash)
            for (var i=0; i<this.buckets; ++i) 
                this.hash[i] = [];
    };
    Runtime.prototype.symbolNames = function(){ 
        return Object.keys(this.defs);
    };
    Runtime.prototype.app = function(x,y){
        var hash         = x + "_" + y; // how to improve this?
        if (this.hash[hash]) return this.hash[hash];
        var pos          = this.left_.length;
        var ptr          = 0x80000000|pos
        this.left_[pos]  = x;
        this.right_[pos] = y;
        return this.hash[hash] = ptr;
    };
    Runtime.prototype.isApp = function(node){
        return !this.isLam(node) && !this.isNum(node) && (node >>> 20) === 0x800;
    };
    Runtime.prototype.left = function(node){ 
        return this.left_[(node & 0x000FFFFF)];
    };
    Runtime.prototype.right = function(node){ 
        return this.right_[(node & 0x000FFFFF)];
    };
    Runtime.prototype.isPrim = function(node){
        return (node >>> 20) === 0x400;
    };
    Runtime.prototype.prim = function(node){
        return node | 0x40000000;
    };
    Runtime.prototype.getPrim = function(n){
        return n & 0x000FFFFF;
    };
    Runtime.prototype.isLam = function(node){
        return (node >>> 20) === 0x800 ? this.left(node) === this.Lam : !this.isNum(node) && (node & 0x3FF00000);
    };
    Runtime.prototype.lam = function(node){
        return this.isNum(node) ? this.app(this.Lam,node) : node + 0x00100000;
    };
    Runtime.prototype.body = function(node){
        return (node >>> 20) === 0x800 ? this.right(node) : node - 0x00100000;
    };
    Runtime.prototype.isVar = function(node){
        return !this.isNum(node) && !(node >>> 20);
    };
    Runtime.prototype.num = function(x){
        return x > 0 ? (x + 1) * i32size : (x - 1) * i32size;
    };
    Runtime.prototype.isNum = function(node){
        return Math.abs(node) >= i32size;
    };
    Runtime.prototype.getNum = function(x){
        return x > 0 ? (x / i32size - 1) : (x / i32size + 1);
    };
    Runtime.prototype.id = function(node){
        return node & 0x7FFFFFFF;
    };
    Runtime.prototype.prims = (function(){
        var primNames = [
            "","float.to_church","float.to_string",
            "float.add","float.sub","float.mul","float.div","float.mod","float.pow","float.log",
            "float.greater_than","float.less_than","float.equal",
            "float.floor","float.ceil","float.round"];
        var prims = {};
        for (var i=0; i<primNames.length; ++i){
            prims[primNames[i]] = i;
            prims[i] = primNames[i];
        };
        return prims;
    })();
    var prims = Runtime.prototype.prims;
    var binOps = {};
    Runtime.prototype.binOps = binOps;
    binOps[prims["float.add"]] = function(a,b){ 
        return this.num(this.getNum(a) + this.getNum(b)) 
    };
    binOps[prims["float.sub"]] = function(a,b){ 
        return this.num(this.getNum(a) - this.getNum(b)) 
    };
    binOps[prims["float.mul"]] = function(a,b){ 
        return this.num(this.getNum(a) * this.getNum(b)) 
    };
    binOps[prims["float.div"]] = function(a,b){ 
        return this.num(this.getNum(a) / this.getNum(b)) 
    };
    binOps[prims["float.mod"]] = function(a,b){ 
        return this.num(((this.getNum(a) % this.getNum(b)) + this.getNum(b)) % this.getNum(b)) 
    };
    binOps[prims["float.pow"]] = function(a,b){ 
        return this.num(Math.pow(this.getNum(a),this.getNum(b))) 
    };
    binOps[prims["float.log"]] = function(a,b){ 
        return this.num(Math.log(this.getNum(b))/Math.log(this.getNum(a))) 
    };
    binOps[prims["float.greater_than"]] = function(a,b){ 
        return (this.getNum(a) > this.getNum(b) ? this.lam(this.lam(1)) : this.lam(this.lam(0))) 
    };
    binOps[prims["float.less_than"]] = function(a,b){ 
        return (this.getNum(a) < this.getNum(b) ? this.lam(this.lam(1)) : this.lam(this.lam(0))) 
    };
    binOps[prims["float.equal"]] = function(a,b){ 
        return (this.getNum(a) === this.getNum(b) ? this.lam(this.lam(1)) : this.lam(this.lam(0))) 
    };
    var ops = {};
    Runtime.prototype.ops = ops;
    ops[prims["float.to_church"]] = function (n){
        for (var result=0, i=0, l=this.getNum(n); i<l; ++i)
            result = this.app(1,result);
        return this.lam(this.lam(result));
    };
    ops[prims["float.floor"]] = function (r){
        return this.num(Math.floor(this.getNum(r)));
    };
    ops[prims["float.ceil"]] = function (r){
        return this.num(Math.ceil(this.getNum(r)));
    };
    ops[prims["float.round"]] = function (r){
        return this.num(Math.round(this.getNum(r)));
    };
    Runtime.prototype.normal = function(x){
        ++this.stats.reductions;
        var self = this;
        if (this.isApp(x)){
            var l  = this.normal(this.left(x));
            var r  = this.normal(this.right(x));
            var ll = this.left(l);
            var lr = this.right(l);
        };
        if (this.isLam(x))
            var body = this.normal(this.body(x));
        return this.normMemo[x] || (++this.stats.unmemoized_reductions, this.normMemo[x] = ((
            this.isVar(x) ? (this.stats.max_var < x ? (this.stats.max_var=x) : x)
            : this.isPrim(x) ? x
            : this.isNum(x) ? x
            //: this.isLam(x) && this.isApp(body) && this.right(body) === 0 && this.bindUses(x) === 1 ?
                //this.subs(0,-1,-1,this.left(body)) // eta-reduce
            : this.isLam(x) ? this.lam(body)
            : this.isLam(l) ? this.apply(l,r) // beta-reduce
            : this.isPrim(l) && this.isNum(r) && this.ops[this.getPrim(l)] ?
                this.ops[this.getPrim(l)].call(this,r)
            : this.isPrim(ll) && this.isNum(lr) && this.isNum(r) && this.binOps[this.getPrim(ll)] ? 
                ((this.binOps[this.getPrim(ll)]).call(this,lr,r))
            : this.app(l,r))));
    };
    Runtime.prototype.bindUses = function (t){
        var self = this;
        return (function R(d,x){
            return self.isApp(x) ? R(d,self.left(x))+R(d,self.right(x))
                 : self.isLam(x) ? R(d+1,self.body(x))
                 : self.isVar(x) ? (x===d ? 1 : 0)
                 : 0;
        })(-1,t);
    };
    Runtime.prototype.subs = function (t,d,w,x){
        ++this.stats.subs_calls;
        var hash = ""+t+"_"+d+"_"+w+"_"+x;
        if (this.subsMemo[hash]) return this.subsMemo[hash];
        ++this.stats.unmemoized_subs_calls;
        return this.subsMemo[hash] = 
              this.isApp(x) ? this.app(this.subs(t,d,w,this.left(x)),this.subs(t,d,w,this.right(x)))
            : this.isLam(x) ? this.lam(this.subs(t,d+1,w,this.body(x)))
            : this.isVar(x) ? (t && x===d ? this.subs(0,-1,d,t) : x>d ? x+w : x)
            : x;
    };
    Runtime.prototype.apply = function(f,x){
        ++this.stats.beta_reductions;
        return this.normal(this.subs(x,0,-1,this.body(f)));
    };
    Runtime.prototype.define = function(name,source){
        var ptr           = this.read(source);
        var old_ptr       = this.defs[name];
        var old_name      = this.defs[ptr];
        this.defs[name]   = ptr;
        this.source[name] = source;
        return ptr;
    };
    Runtime.prototype.toString = function(x){ 
        return this.isPrim(x) ? this.prims[this.getPrim(x)] :
            this.isNum(x) ? this.getNum(x) :
            this.isApp(x) ? "("+this.toString(this.left(x))+" "+this.toString(this.right(x))+")" :
            this.isLam(x) ? "(λ "+this.toString(this.body(x))+")" 
            : "v"+x;
    };
    Runtime.prototype.compilers = {
        lambda: {
            def  : function (name,a){ return a; },
            app  : function (a,b){ return "("+a+" "+b+")"; },
            lam  : function (var_,body){ return "(λ "+var_+" . "+body+")"; }
        },
        scheme : {
            def  : function (name,a){ return "(define " + name + " " + a + ")"; },
            app  : function (a,b){ return "("+a+" "+b+")"; },
            lam  : function (var_,body){ return "(lambda ("+var_+") "+body+")"; },
            prim : function(prim){ return prim.replace("float.","f_"); }
        },
        javascript : {
            def  : function (name,a){ return name + " = " + a; },
            app  : function (a,b){ return "("+a+"("+b+"))"; },
            lam  : function (var_,body){ return "(function ("+var_+") { return "+body+" })"; },
            prim : function(prim){ return prim.replace("float.","f_"); },
            //"float.add" : function (a,b){return "("+a+"+"+b+")";}
        },
        python : {
            def  : function (name,a){ return name + " = " + a; },
            app  : function (a,b){ return "("+a+"("+b+"))"; },
            lam  : function (var_,body){ return "(lambda "+var_+" : "+body+")"; },
            prim : function(prim){ return prim.replace("float.","f_"); }
        },
        haskell : {
            def  : function (name,a){ return name + " = " + a; },
            app  : function (a,b){ return "("+a+" # "+b+")"; },
            lam  : function (var_,body){ return "(Fun(\\"+var_+"->"+body+"))"; },
            prim : function(prim){ return prim.replace("float.","f_"); },
            num  : function(num){ return "(Num "+num+")"; }
        }
    };
    Runtime.prototype.compileWith = function(fns,symbol){ 
        fns.prim = fns.prim || function(a){return a};
        fns.num  = fns.num  || function(a){return a};
        var self = this;
        return (function(x){
            return (function R(x,d){
                //if (self.isApp(x) && self.isApp(self.left(x)) && self.isPrim(self.left(self.left(x)))){
                    //var prim = self.getPrim(self.left(self.left(x)));
                    //if (fns[prims[prim]])
                        //return fns[prims[prim]](R(self.right(self.left(x)),d),R(self.right(x),d));
                //};
                return (
                    self.isPrim(x) ? fns.prim(self.prims[self.getPrim(x)]) :
                    self.isNum(x)  ? fns.num(self.getNum(x)) :
                    self.isApp(x)  ? fns.app(R(self.left(x),d),R(self.right(x),d)) :
                    self.isLam(x)  ? fns.lam("v"+d,R(self.body(x),d+1)) : 
                    "v"+(d-x-1));
                })(x,0);
        })(symbol);
    };
    Runtime.prototype.compileTo = function(target,symbol,name){
        var compiler = this.compilers[target.toLowerCase()];
        var compiled = this.compileWith(compiler, symbol);
        return name ? compiler.def(name,compiled) : compiled;
    };
    Runtime.prototype.read = function(value){
        return this.jsonToValue(this.unflatten(this.unlets(this.unarrows(this.stringToJson(value))))); 
    };
    Runtime.prototype.show = function(value){
        if (typeof value === "string") value = this.defs[value];
        return this.jsonToString(this.arrows(this.lets(this.flatten(this.valueToJson(value)))));
    }; 
    Runtime.prototype.valueToJson = function(tree){
        var abc = "abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ";
        var self = this;
        return (function R(x,scope,root){
            // (a b -> (a (a (a b)))) to 3
            function churchNumber(x){
                return x === 0 ? 0 : self.isApp(x) && self.left(x) === 1 ? 1 + churchNumber(self.right(x)) : NaN;
            };
            // (a b -> (a 1 (a 2 (a 3 b)))) to [1 2 3]
            function churchList(x){
                var listified = (function R(x){
                    if (x === 0)
                        return [];
                    if (self.isApp(x) && self.isApp(self.left(x)) && self.left(self.left(x)) === 1){
                        var tail = R(self.right(x));
                        return tail !== null 
                            ? [self.right(self.left(x))].concat(tail) 
                            : null;
                    };
                    return null;
                })(x);
                // Uses the cons/nil binders inside list, so can't listify.
                if (listified && (self.bindUses(self.lam(self.lam(x))) !== listified.length || self.bindUses(self.lam(x)) !== 1))
                    return null;
                return listified;
            };
            // (a -> (((a 1) 2) 3)) to {1 2 3}
            function churchTuple(x){
                var tuplified = (function R(x){
                    if (self.isApp(self.left(x))){
                        var left = R(self.left(x));
                        return left !== null ? left.concat([self.right(x)]) : null;
                    };
                    if (self.left(x) === 0){
                        return [self.right(x)];
                    };
                    return null;
                })(x);
                // Uses the tuple binder inside tuple, so can't tuplify.
                if (tuplified && self.bindUses(self.lam(x)) !== 1)
                    return null;
                return tuplified;
            };
            var church;
            if (!root && self.defs[x])
                return self.defs[x];
            if (self.isNum(x))
                return String(self.getNum(x));
            if (self.isPrim(x))
                return self.prims[self.getPrim(x)];
            if (self.isLam(x) && self.isLam(self.body(x)) && !isNaN(church = churchNumber(self.body(self.body(x)))))
                return "c"+String(church);
            if (self.isLam(x) && self.isLam(self.body(x)) && ((church = churchList(self.body(self.body(x)))) !== null)){
                return ["LIST"].concat(church.map(function(x){ 
                    return R(x,[abc[scope.length],abc[scope.length+1]].concat(scope),0); 
                }));
            };
            if (self.isLam(x) && self.isApp(self.body(x)) && (church = churchTuple(self.body(x)))){
                return ["TUPLE"].concat(church.map(function(x){
                    return R(x,[abc[scope.length]].concat(scope),0);
                }));
            };
            if (self.isApp(x))
                return [R(self.left(x),scope,0),R(self.right(x),scope,0)];
            if (self.isLam(x)){
                var bind = abc[scope.length];
                return [["fn",[bind]],R(self.body(x),[bind].concat(scope),0)];
            };
            return scope[x] || "var_"+x+"";
        })(tree,[],1); 
    };
    Runtime.prototype.jsonToValue = function (tree){
        var self = this;
        return (function R(a,scope,depth){
            function churchNumber(x){
                return self.lam(self.lam((function R(x){
                    return x === 0 ? 0 : self.app(1,R(x-1));
                })(x)));
            };
            function churchList(x){
                return self.lam(self.lam((function R_(x,t){
                    return x === "LIST" || x.length === 1 ? t : R_(x[0],self.app(self.app(1,R(x[1],scope,depth+2)),t));
                })(x,0)));
            };
            function churchTuple(x){
                return self.lam((function R_(x){
                    return x === "TUPLE" || x.length === 1 ? 0 : self.app(R_(x[0]),R(x[1],scope,depth+1));
                })(x));
            };
            if (a[1] === "NIL")
                return churchList(a[0]);
            if (a[1] === "TUPLENIL")
                return churchTuple(a[0]);
            if (typeof a === "string"){
                return (
                    self.defs[a] && scope[a]===undefined ? self.defs[a] :
                    typeof scope[a] !== "undefined" ? depth-scope[a] :
                    a[0] === "c" && !isNaN(Number(a.slice(1))) ? churchNumber(Number(a.slice(1))) :
                    !isNaN(Number(a)) ? self.num(Number(a)) :
                    self.prims[a] ? self.prim(self.prims[a]) :
                    (function(){throw "Undefined symbol: "+a})());
            };
            if (a[0]&&a[0][0] === "fn") {
                depth = depth+1;
                scope = JSON.parse(JSON.stringify(scope));
                scope[a[0][1][0]] = depth;
                //return self.tag(a[0][1][0],self.lam(R(a[1], scope, depth)));
                return self.lam(R(a[1], scope, depth));
            };
            return self.app(R(a[0],scope,depth),R(a[1],scope,depth));
        })(tree,{},-1); 
    };
    Runtime.prototype.flatten = foldJson(function R(a){
        return Array.isArray(a[0]) && !(a[0][0]==="fn" && a[0].length===3) ? a[0].concat(a.slice(1)) : a;
    },function(x){return x});
    Runtime.prototype.unflatten = foldJson(function R(a){
        return typeof a === "object" && a.length > 2 ? R([[a[0],a[1]]].concat(a.slice(2))) : a;
    },function(x){return x});
    Runtime.prototype.arrows = foldJson(function R(a){
        return a[0] === "fn" ? a[1].concat(["->",a[2]]) : a;
    },function(x){return x});
    Runtime.prototype.unarrows = foldJson(function R(a){
        return a.indexOf("->") !== -1 
            ? ["fn",a.slice(0,a.indexOf("->"))].concat(a.slice(a.indexOf("->")+1))
            : a;
    },function(x){return x});
    Runtime.prototype.lets = foldJson(function R(a){
        return 0,
            //( a[0][0] === "fn" ? ["let",[a[0][1][0],a[1]],R(a[0][2].concat(a.slice(2)))]
            ( a[0] === "fn" && a[2][0] === "fn" ? ["fn",a[1].concat(a[2][1]),a[2][2]]
            //: a[0] === "let" && a[2][0] === "let" ? ["let",a[1]].concat(a[2].slice(1))
            : a);
    },function(x){return x});
    Runtime.prototype.unlets = foldJson(function R(a){
        return 0,
            //( a[0] === "let" && a.length <= 3  ? [["fn",[a[1][0]],a[2]],a[1][1]]
            ( a[0] === "fn" && a[1].length > 1 ? ["fn",[a[1][0]],R(["fn",a[1].slice(1),a[2]])]
            //: a[0] === "let" && a.length > 3   ? R(["let",a[1],R(["let"].concat(a.slice(2)))])
            : a); 
    },function(x){return x});
    Runtime.prototype.isAsciiCode = function isAsciiCode(a){
        return (Number(a)>=(65536) && Number(a)<=(65536+255));
    };
    Runtime.prototype.charFromAscii = function charFromAscii(a){
        return String.fromCharCode(a-65536);
    };
    Runtime.prototype.charToAscii = function charToAscii(a){
        return (a.charCodeAt(0)+65536).toString();
    };
    Runtime.prototype.isCharList = function isCharList(a){
        for (var i=0,l=a.length; i<l; ++i)
            if (a[i][0] !== "'")
                return false;
        return true;
    };
    Runtime.prototype.jsonToString = function(json){
        var self = this;
        return foldJson(function(a){ return function(d){
            function repeat(str,n){ return n===0 ? "" : str + repeat(str,n-1); };
            function removeQuote(c){ return c[1]; };
            for (var i=0,l=a.length; i<l; ++i) a[i] = a[i](d+1);
            var tail = a.slice(1);
            if (a[0] === "LIST") return self.isCharList(tail) ? '"'+tail.map(removeQuote).join("")+'"' : '['+tail.join(" ")+']';
            if (a[0] === "LIST") return '['+tail.join(" ")+']';
            if (a[0] === "TUPLE") return '{'+tail.join(" ")+'}';
            //var inline     = JSON.stringify(a).length < 60;
            var inline     = true;
            var sep        = inline ? " " : "\n" + repeat("    ",d);
            var doubleHead = a.length > 1 && (a[0] === "fn" || a[0] === "if" || a[0] === "case");
            return "("+(doubleHead ? a[0]+" "+a.slice(1).join(sep) : a.join(sep))+")";
        }},function(a){return function(d){
            return self.isAsciiCode(a) ? "'"+self.charFromAscii(Number(a)) : a;
        }})(json)(1);
    };
    Runtime.prototype.stringToJson = function(str){
        var i = 0, l = str.length;
        str = str.replace(/\\n/g,"\n");
        str = str.replace(/\\t/g,"\t");
        var self = this;
        return (function parse(){
            for (var c; !c || c === " "; c = str[i++]){};
            if (/[\(\[\{]/.test(c)){
                for (var result = (c[0]==="["?["LIST"]:c[0]==="{"?["TUPLE"]:[]); i<l && str[i]!=="]" && str[i]!==")" && str[i]!=="}";)
                    result.push(parse());
                if (result[0] === "LIST")
                    result.push("NIL");
                if (result[0] === "TUPLE")
                    result.push("TUPLENIL");
                return ++i, result;
            };
            if (str[i-1] === "'")
                return i+=1, self.charToAscii(str[i-1]);
            if (c === '"'){
                var str_literal = str.slice(i,str.indexOf('"',i+1)).split("").map(self.charToAscii);
                i += str_literal.length+1;
                return ["LIST"].concat(str_literal).concat(["NIL"]);
            };
            for (var word = ""; i<l && !/[ ,\)\]\}]/.test(c); c = str[i++])
                word += c;
            if (c === ")" || c === "]" || c === "}") --i;
            return word;
        })(); 
    };
    Runtime.prototype.writeJSON = function(){
        var serial = {};
        this.symbolNames().map(function(name){
            serial[name] = this.source[name];
            //serial[name] = this.show(this.defs[name]);
        }.bind(this));
        return JSON.stringify(serial,null,4);
    };
    Runtime.prototype.readJSON = function(json){
        json = typeof json === "string" ? JSON.parse(json) : json;
        for (var name in json)
            this.define(name,json[name]);
    };
    Runtime.prototype.readSource = function(text){
        var self = this;
        var changed = [];
        text.split("\n").map(function(line){
            if (line.indexOf("=") === -1) return;
            if (line.slice(0,3) === "---") return;
            line = line.replace(/\s{2,}/g, ' ');
            if (line[line.length-1] === " ") line = line.slice(0,-1);
            var name = line.split(" = ")[0].split(" ")[0];
            var vars = line.split(" = ")[0].split(" ").slice(1).join(" ");
            var body = line.split(" = ")[1];
            if (body.indexOf(" ")!==-1 && body[0]!=="(" && body[0]!=="[" && body[0]!=="{") body = "("+body+")";
            if (body.indexOf(" ")===-1 && vars.length===0) body = "((fn (a) a) "+body+")";
            var code = vars.length > 0 ? "(fn ("+vars+") "+body+")" : body;
            var old_ptr = self.defs[name];
            var ptr = self.define(name,code);
            if (ptr !== old_ptr)
                changed.push(name);
        });
        return changed;
    };
    function foldJson(node,leaf){
        return function(tree){
            return (function R(a){
                return typeof a !== "object" ? leaf(a) : node(a.map(R));
            })(tree,[]);
        };
    };
    Runtime.prototype.generateJavascriptLibrary = function(symbols){
        var self = this;
        var generateJs = function(contents,definitions){
            return ([
                '// ## LambdaWiki.org ##',
                '// ::',
                '// :: Hello! This source was generated by LambdaWiki.org, the encyclopedia of',
                '// :: code. It contains a collection of functions compiled from our database',
                '// :: to JavaScript. You can use those functions in any JavaScript project!',
                '// :: Please visit our site for more info: LambdaWiki.org',
                '',
                '// ## Using this file ##',
                '// ::',
                '// :: Every imported function lies inside an object called "lambda".',
                '// ::',
                '// :: To call a function, use function_name(arg0)(arg1)(etc...)',
                '// ::',
                '// :: To call with js arrays/lists, first convert them to lambda-encoded structures:',
                '// ::',
                '// ::     to_lambda_list(js_array)          // js array to lambda list',
                '// ::     from_lambda_list(lambda_list)     // lambda list to js array',
                '// ::     to_lambda_string(js_array)        // js string to lambda list',
                '// ::     from_lambda_string(lambda_string) // lambda list to js string',
                '// ::',
                '// :: Examples:',
                '// ::',
                '// ::     // Sum numbers from 0 to 4, returning 6 (0 + 1 + 2 + 3 == 6).',
                '// ::     sum_range(0)(4) ',
                '// ::',
                '// ::     // Converts a JS array to a lambda-list, reverses it and converts back.',
                '// ::     var js_array             = [1,2,3,4];',
                '// ::     var lambda_list          = to_lambda_list(array);',
                '// ::     var reversed_lambda_list = reverse(lambda_list);',
                '// ::     var reversed_js_array    = from_lambda_list(reversed_lambda_list);',
                '// ::     console.log(reversed_js_array); // [4,3,2,1]',
                '// ::',
                '// :: Pro-tip : use globalize() and you wont need the "" prefix anymore. ',
                '// :: Note    : the examples wont work if those functions werent included on this file.',
                '',
                '// ## Contents ##',
                '// ::',
                '// :: The following functions are included in this selection:',
                '// :: (For specific documentation, visit LambdaWiki.org/function_name)',
                '// ::',
                contents,
                '',
                'var lamlib = (function(){',
                '',
                '    // ## Part 1. Floating Point Primitives ##',
                '    // :: Those are used by the compiled functions for faster arithmetic.',
                '    ',
                '    var f_true         = (function(a){return (function(b){return a})});',
                '    var f_false        = (function(a){return (function(b){return b})});',
                '    var f_to_church    = (function(n){return (function(f){return (function(a){ for (var i=0; i<n; ++i) a  =  f(a); return a; }) }) });',
                '    var f_from_church  = (function(n){return ((n(function(a){return (a + 1)}))(0))});',
                '    var f_add          = (function(a){return (function(b){return (a + b)})});',
                '    var f_sub          = (function(a){return (function(b){return (a - b)})});',
                '    var f_mul          = (function(a){return (function(b){return (a * b)})});',
                '    var f_div          = (function(a){return (function(b){return (a / b)})});',
                '    var f_floor        = (function(a){return Math.floor(a)});',
                '    var f_ceil         = (function(a){return Math.ceil(a)});',
                '    var f_equal        = (function(a){return (function(b){return a === b ? f_true : f_false})});',
                '    var f_less_than    = (function(a){return (function(b){return a < b ? f_true : f_false})});',
                '    var f_greater_than = (function(a){return (function(b){return a > b ? f_true : f_false})});',
                '    var f_mod          = (function(a){return (function(b){return (((a % b) + b) % b)})});',
                '    var f_log          = (function(a){return (function(b){return Math.log(b) / Math.log(a)})});',
                '    var f_pow          = (function(a){return (function(b){return Math.pow(a,b)})});',
                '    ',
                '    // ## Part 2. Utils ##',
                '    // :: Those utils allows you to convert JavaScript native objects (arrays,',
                '    // :: strings, etc) from/to church-encoded structures (that is, structures using',
                '    // :: lambdas only), so you can use functions compiled from the lambda calculus ',
                '    // :: on your js data. See: <Alan please add link> for explanation and examples.',
                '    // :: Ex: from_lambda_list(reverse(to_lambda_list([1,2,3,4])));',
                '    ',
                '    var lamlib = {};',
                '    ',
                '    lamlib.to_lambda_list = function(js_array){',
                '        return function(cons){',
                '            return function(nil){',
                '                var list = nil;',
                '                for (var i=js_array.length-1; i>=0; --i)',
                '                    list = cons(js_array[i])(list);',
                '               return list;',
                '            };',
                '        };',
                '    };',
                '    lamlib.from_lambda_list = function (lambda_list){',
                '        var result = []; ',
                '        lambda_list(function(x){return (function(xs){ result.push(x); })})(function(){}); ',
                '        for (var i=0, l=result.length; i<l/2; ++i){',
                '            var tmp = result[l-i-1];',
                '            result[l-i-1] = result[i];',
                '            result[i] = tmp;',
                '        };',
                '        return result; ',
                '    };',
                '    lamlib.char_from_ascii = function(c){',
                '        return String.fromCharCode(c-65536);',
                '    };',
                '    lamlib.char_to_ascii = function(c){',
                '        return (c.charCodeAt(0)+65536);',
                '    };',
                '    lamlib.to_lambda_string = function(str){',
                '        return lamlib.to_lambda_list(str.split("").map(lamlib.char_to_ascii));',
                '    };',
                '    lamlib.from_lambda_string = function(str){',
                '        return lamlib.from_lambda_list(str).map(lamlib.char_from_ascii).join("");',
                '    };',
                '    lamlib.to_lambda_bool = function(bool){',
                '        return bool ? f_true : f_false;',
                '    };',
                '    lamlib.from_lambda_bool = function(lambda_bool){',
                '        return lambda_bool(true)(false);',
                '    };',
                '    lamlib.interfaced = function(fn){',
                '        // Enables a function compiled from lambda calculus to be called with native js objects.',
                '        // Ex: from_lambda_list(interfaced(reverse)([1,2,3,4]));',
                '        if (typeof fn === "number")',
                '            return fn;',
                '        return function (x){',
                '            var converted_x = ',
                '                typeof x === "string" ? lamlib.to_lambda_string(x) :',
                '                typeof x === "object" ? lamlib.to_lambda_list(x) :',
                '                x;',
                '            return interfaced(fn(converted_x));',
                '        };',
                '    };',
                '    lamlib.print = function(str){ ',
                '        console.log(from_lambda_string(str));',
                '    };',
                '    lamlib.globalize = function(){',
                '        var global_object = typeof global === "undefined" ? window : global;',
                '        for (var key in lamlib)',
                '            global_object[key] = lamlib[key];',
                '    };',
                '    ',
                '    ',
                '    // ## Part 3. Library ##',
                '    // :: A selected collection of functions compiled from the Lambda Calculus to JavaScript.',
                '    ',
                definitions,
                '    ',
                '    return lamlib;',
                '})();',
                'if (typeof module !== "undefined") module.exports = lamlib;'].join("\n")); 
        };
        var definitions = symbols.map(function(name){
            var compiled  = self.compileTo("javascript",self.normal(self.defs[name]));
            return '    lamlib["'+name.replace(/\./g,"_")+'"] = '+compiled+';';
        }).join("\n\n");
        var contents = symbols.sort().map(function(name){
            return "// ::     "+name.replace(/\./g,"_");
        }).join("\n");
        return generateJs(contents,definitions);
    };
    return Runtime;
})();
if (typeof module !== "undefined") module.exports = Lambda;
