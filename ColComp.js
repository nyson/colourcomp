"use strict";
// This object will hold all exports.
var Haste = {};

/* Thunk
   Creates a thunk representing the given closure.
   If the non-updatable flag is undefined, the thunk is updatable.
*/
function T(f, nu) {
    this.f = f;
    if(nu === undefined) {
        this.x = __updatable;
    }
}

/* Hint to optimizer that an imported symbol is strict. */
function __strict(x) {return x}

// A tailcall.
function F(f) {
    this.f = f;
}

// A partially applied function. Invariant: members are never thunks.
function PAP(f, args) {
    this.f = f;
    this.args = args;
    this.arity = f.length - args.length;
}

// Special object used for blackholing.
var __blackhole = {};

// Used to indicate that an object is updatable.
var __updatable = {};

/* Generic apply.
   Applies a function *or* a partial application object to a list of arguments.
   See https://ghc.haskell.org/trac/ghc/wiki/Commentary/Rts/HaskellExecution/FunctionCalls
   for more information.
*/
function A(f, args) {
    while(true) {
        f = E(f);
        if(f instanceof F) {
            f = E(B(f));
        }
        if(f instanceof PAP) {
            // f is a partial application
            if(args.length == f.arity) {
                // Saturated application
                return f.f.apply(null, f.args.concat(args));
            } else if(args.length < f.arity) {
                // Application is still unsaturated
                return new PAP(f.f, f.args.concat(args));
            } else {
                // Application is oversaturated; 
                var f2 = f.f.apply(null, f.args.concat(args.slice(0, f.arity)));
                args = args.slice(f.arity);
                f = B(f2);
            }
        } else if(f instanceof Function) {
            if(args.length == f.length) {
                return f.apply(null, args);
            } else if(args.length < f.length) {
                return new PAP(f, args);
            } else {
                var f2 = f.apply(null, args.slice(0, f.length));
                args = args.slice(f.length);
                f = B(f2);
            }
        } else {
            return f;
        }
    }
}

/* Eval
   Evaluate the given thunk t into head normal form.
   If the "thunk" we get isn't actually a thunk, just return it.
*/
function E(t) {
    if(t instanceof T) {
        if(t.f !== __blackhole) {
            var f = t.f;
            t.f = __blackhole;
            if(t.x === __updatable) {
                t.x = f();
            } else {
                return f();
            }
        }
        return t.x;
    } else {
        return t;
    }
}

/* Bounce
   Bounce on a trampoline for as long as we get a function back.
*/
function B(f) {
    while(f instanceof F) {
        var fun = f.f;
        f.f = __blackhole;
        f = fun();
    }
    return f;
}

// Export Haste, A, B and E. Haste because we need to preserve exports, A, B
// and E because they're handy for Haste.Foreign.
if(!window) {
    var window = {};
}
window['Haste'] = Haste;
window['A'] = A;
window['E'] = E;
window['B'] = B;


/* Throw an error.
   We need to be able to use throw as an exception so we wrap it in a function.
*/
function die(err) {
    throw E(err);
}

function quot(a, b) {
    return (a-a%b)/b;
}

function quotRemI(a, b) {
    return [0, (a-a%b)/b, a%b];
}

// 32 bit integer multiplication, with correct overflow behavior
// note that |0 or >>>0 needs to be applied to the result, for int and word
// respectively.
if(Math.imul) {
    var imul = Math.imul;
} else {
    var imul = function(a, b) {
        // ignore high a * high a as the result will always be truncated
        var lows = (a & 0xffff) * (b & 0xffff); // low a * low b
        var aB = (a & 0xffff) * (b & 0xffff0000); // low a * high b
        var bA = (a & 0xffff0000) * (b & 0xffff); // low b * high a
        return lows + aB + bA; // sum will not exceed 52 bits, so it's safe
    }
}

function addC(a, b) {
    var x = a+b;
    return [0, x & 0xffffffff, x > 0x7fffffff];
}

function subC(a, b) {
    var x = a-b;
    return [0, x & 0xffffffff, x < -2147483648];
}

function sinh (arg) {
    return (Math.exp(arg) - Math.exp(-arg)) / 2;
}

function tanh (arg) {
    return (Math.exp(arg) - Math.exp(-arg)) / (Math.exp(arg) + Math.exp(-arg));
}

function cosh (arg) {
    return (Math.exp(arg) + Math.exp(-arg)) / 2;
}

function isFloatFinite(x) {
    return isFinite(x);
}

function isDoubleFinite(x) {
    return isFinite(x);
}

function err(str) {
    die(toJSStr(str));
}

/* unpackCString#
   NOTE: update constructor tags if the code generator starts munging them.
*/
function unCStr(str) {return unAppCStr(str, [0]);}

function unFoldrCStr(str, f, z) {
    var acc = z;
    for(var i = str.length-1; i >= 0; --i) {
        acc = B(A(f, [str.charCodeAt(i), acc]));
    }
    return acc;
}

function unAppCStr(str, chrs) {
    var i = arguments[2] ? arguments[2] : 0;
    if(i >= str.length) {
        return E(chrs);
    } else {
        return [1,str.charCodeAt(i),new T(function() {
            return unAppCStr(str,chrs,i+1);
        })];
    }
}

function charCodeAt(str, i) {return str.charCodeAt(i);}

function fromJSStr(str) {
    return unCStr(E(str));
}

function toJSStr(hsstr) {
    var s = '';
    for(var str = E(hsstr); str[0] == 1; str = E(str[2])) {
        s += String.fromCharCode(E(str[1]));
    }
    return s;
}

// newMutVar
function nMV(val) {
    return ({x: val});
}

// readMutVar
function rMV(mv) {
    return mv.x;
}

// writeMutVar
function wMV(mv, val) {
    mv.x = val;
}

// atomicModifyMutVar
function mMV(mv, f) {
    var x = B(A(f, [mv.x]));
    mv.x = x[1];
    return x[2];
}

function localeEncoding() {
    var le = newByteArr(5);
    le['v']['i8'][0] = 'U'.charCodeAt(0);
    le['v']['i8'][1] = 'T'.charCodeAt(0);
    le['v']['i8'][2] = 'F'.charCodeAt(0);
    le['v']['i8'][3] = '-'.charCodeAt(0);
    le['v']['i8'][4] = '8'.charCodeAt(0);
    return le;
}

var isDoubleNaN = isNaN;
var isFloatNaN = isNaN;

function isDoubleInfinite(d) {
    return (d === Infinity);
}
var isFloatInfinite = isDoubleInfinite;

function isDoubleNegativeZero(x) {
    return (x===0 && (1/x)===-Infinity);
}
var isFloatNegativeZero = isDoubleNegativeZero;

function strEq(a, b) {
    return a == b;
}

function strOrd(a, b) {
    if(a < b) {
        return 0;
    } else if(a == b) {
        return 1;
    }
    return 2;
}

function jsCatch(act, handler) {
    try {
        return B(A(act,[0]));
    } catch(e) {
        return B(A(handler,[e, 0]));
    }
}

/* Haste represents constructors internally using 1 for the first constructor,
   2 for the second, etc.
   However, dataToTag should use 0, 1, 2, etc. Also, booleans might be unboxed.
 */
function dataToTag(x) {
    if(x instanceof Array) {
        return x[0];
    } else {
        return x;
    }
}

function __word_encodeDouble(d, e) {
    return d * Math.pow(2,e);
}

var __word_encodeFloat = __word_encodeDouble;
var jsRound = Math.round;
var jsTrunc = Math.trunc ? Math.trunc : function(x) {
    return x < 0 ? Math.ceil(x) : Math.floor(x);
};
function jsRoundW(n) {
    return Math.abs(jsTrunc(n));
}
var realWorld = undefined;
if(typeof _ == 'undefined') {
    var _ = undefined;
}

function popCnt(i) {
    i = i - ((i >> 1) & 0x55555555);
    i = (i & 0x33333333) + ((i >> 2) & 0x33333333);
    return (((i + (i >> 4)) & 0x0F0F0F0F) * 0x01010101) >> 24;
}

// Scratch space for byte arrays.
var rts_scratchBuf = new ArrayBuffer(8);
var rts_scratchW32 = new Uint32Array(rts_scratchBuf);
var rts_scratchFloat = new Float32Array(rts_scratchBuf);
var rts_scratchDouble = new Float64Array(rts_scratchBuf);

function decodeFloat(x) {
    rts_scratchFloat[0] = x;
    var sign = x < 0 ? -1 : 1;
    var exp = ((rts_scratchW32[0] >> 23) & 0xff) - 150;
    var man = rts_scratchW32[0] & 0x7fffff;
    if(exp === 0) {
        ++exp;
    } else {
        man |= (1 << 23);
    }
    return [0, sign*man, exp];
}

function decodeDouble(x) {
    rts_scratchDouble[0] = x;
    var sign = x < 0 ? -1 : 1;
    var manHigh = rts_scratchW32[1] & 0xfffff;
    var manLow = rts_scratchW32[0];
    var exp = ((rts_scratchW32[1] >> 20) & 0x7ff) - 1075;
    if(exp === 0) {
        ++exp;
    } else {
        manHigh |= (1 << 20);
    }
    return [0, sign, manHigh, manLow, exp];
}

function jsAlert(val) {
    if(typeof alert != 'undefined') {
        alert(val);
    } else {
        print(val);
    }
}

function jsLog(val) {
    console.log(val);
}

function jsPrompt(str) {
    var val;
    if(typeof prompt != 'undefined') {
        val = prompt(str);
    } else {
        print(str);
        val = readline();
    }
    return val == undefined ? '' : val.toString();
}

function jsEval(str) {
    var x = eval(str);
    return x == undefined ? '' : x.toString();
}

function isNull(obj) {
    return obj === null;
}

function jsRead(str) {
    return Number(str);
}

function jsShowI(val) {return val.toString();}
function jsShow(val) {
    var ret = val.toString();
    return val == Math.round(val) ? ret + '.0' : ret;
}

window['jsGetMouseCoords'] = function jsGetMouseCoords(e) {
    var posx = 0;
    var posy = 0;
    if (!e) var e = window.event;
    if (e.pageX || e.pageY) 	{
	posx = e.pageX;
	posy = e.pageY;
    }
    else if (e.clientX || e.clientY) 	{
	posx = e.clientX + document.body.scrollLeft
	    + document.documentElement.scrollLeft;
	posy = e.clientY + document.body.scrollTop
	    + document.documentElement.scrollTop;
    }
    return [posx - (e.currentTarget.offsetLeft || 0),
	    posy - (e.currentTarget.offsetTop || 0)];
}

function jsGet(elem, prop) {
    return elem[prop].toString();
}

function jsSet(elem, prop, val) {
    elem[prop] = val;
}

function jsGetAttr(elem, prop) {
    if(elem.hasAttribute(prop)) {
        return elem.getAttribute(prop).toString();
    } else {
        return "";
    }
}

function jsSetAttr(elem, prop, val) {
    elem.setAttribute(prop, val);
}

function jsGetStyle(elem, prop) {
    return elem.style[prop].toString();
}

function jsSetStyle(elem, prop, val) {
    elem.style[prop] = val;
}

function jsKillChild(child, parent) {
    parent.removeChild(child);
}

function jsClearChildren(elem) {
    while(elem.hasChildNodes()){
        elem.removeChild(elem.lastChild);
    }
}

function jsFind(elem) {
    var e = document.getElementById(elem)
    if(e) {
        return [1,e];
    }
    return [0];
}

function jsElemsByClassName(cls) {
    var es = document.getElementsByClassName(cls);
    var els = [0];

    for (var i = es.length-1; i >= 0; --i) {
        els = [1, es[i], els];
    }
    return els;
}

function jsQuerySelectorAll(elem, query) {
    var els = [0], nl;

    if (!elem || typeof elem.querySelectorAll !== 'function') {
        return els;
    }

    nl = elem.querySelectorAll(query);

    for (var i = nl.length-1; i >= 0; --i) {
        els = [1, nl[i], els];
    }

    return els;
}

function jsCreateElem(tag) {
    return document.createElement(tag);
}

function jsCreateTextNode(str) {
    return document.createTextNode(str);
}

function jsGetChildBefore(elem) {
    elem = elem.previousSibling;
    while(elem) {
        if(typeof elem.tagName != 'undefined') {
            return [1,elem];
        }
        elem = elem.previousSibling;
    }
    return [0];
}

function jsGetLastChild(elem) {
    var len = elem.childNodes.length;
    for(var i = len-1; i >= 0; --i) {
        if(typeof elem.childNodes[i].tagName != 'undefined') {
            return [1,elem.childNodes[i]];
        }
    }
    return [0];
}


function jsGetFirstChild(elem) {
    var len = elem.childNodes.length;
    for(var i = 0; i < len; i++) {
        if(typeof elem.childNodes[i].tagName != 'undefined') {
            return [1,elem.childNodes[i]];
        }
    }
    return [0];
}


function jsGetChildren(elem) {
    var children = [0];
    var len = elem.childNodes.length;
    for(var i = len-1; i >= 0; --i) {
        if(typeof elem.childNodes[i].tagName != 'undefined') {
            children = [1, elem.childNodes[i], children];
        }
    }
    return children;
}

function jsSetChildren(elem, children) {
    children = E(children);
    jsClearChildren(elem, 0);
    while(children[0] === 1) {
        elem.appendChild(E(children[1]));
        children = E(children[2]);
    }
}

function jsAppendChild(child, container) {
    container.appendChild(child);
}

function jsAddChildBefore(child, container, after) {
    container.insertBefore(child, after);
}

var jsRand = Math.random;

// Concatenate a Haskell list of JS strings
function jsCat(strs, sep) {
    var arr = [];
    strs = E(strs);
    while(strs[0]) {
        strs = E(strs);
        arr.push(E(strs[1]));
        strs = E(strs[2]);
    }
    return arr.join(sep);
}

// JSON stringify a string
function jsStringify(str) {
    return JSON.stringify(str);
}

// Parse a JSON message into a Haste.JSON.JSON value.
// As this pokes around inside Haskell values, it'll need to be updated if:
// * Haste.JSON.JSON changes;
// * E() starts to choke on non-thunks;
// * data constructor code generation changes; or
// * Just and Nothing change tags.
function jsParseJSON(str) {
    try {
        var js = JSON.parse(str);
        var hs = toHS(js);
    } catch(_) {
        return [0];
    }
    return [1,hs];
}

function toHS(obj) {
    switch(typeof obj) {
    case 'number':
        return [0, jsRead(obj)];
    case 'string':
        return [1, obj];
    case 'boolean':
        return [2, obj]; // Booleans are special wrt constructor tags!
    case 'object':
        if(obj instanceof Array) {
            return [3, arr2lst_json(obj, 0)];
        } else if (obj == null) {
            return [5];
        } else {
            // Object type but not array - it's a dictionary.
            // The RFC doesn't say anything about the ordering of keys, but
            // considering that lots of people rely on keys being "in order" as
            // defined by "the same way someone put them in at the other end,"
            // it's probably a good idea to put some cycles into meeting their
            // misguided expectations.
            var ks = [];
            for(var k in obj) {
                ks.unshift(k);
            }
            var xs = [0];
            for(var i = 0; i < ks.length; i++) {
                xs = [1, [0, ks[i], toHS(obj[ks[i]])], xs];
            }
            return [4, xs];
        }
    }
}

function arr2lst_json(arr, elem) {
    if(elem >= arr.length) {
        return [0];
    }
    return [1, toHS(arr[elem]), new T(function() {return arr2lst_json(arr,elem+1);}),true]
}

function ajaxReq(method, url, async, postdata, cb) {
    var xhr = new XMLHttpRequest();
    xhr.open(method, url, async);

    if(method == "POST") {
        xhr.setRequestHeader("Content-type",
                             "application/x-www-form-urlencoded");
    }
    xhr.onreadystatechange = function() {
        if(xhr.readyState == 4) {
            if(xhr.status == 200) {
                B(A(cb,[[1,xhr.responseText],0]));
            } else {
                B(A(cb,[[0],0])); // Nothing
            }
        }
    }
    xhr.send(postdata);
}

/* gettimeofday(2) */
function gettimeofday(tv, _tz) {
    var t = new Date().getTime();
    writeOffAddr("i32", 4, tv, 0, (t/1000)|0);
    writeOffAddr("i32", 4, tv, 1, ((t%1000)*1000)|0);
    return 0;
}

/* Utility functions for working with JSStrings. */

var _jss_singleton = String.fromCharCode;

function _jss_cons(c,s) {return String.fromCharCode(c)+s;}
function _jss_snoc(s,c) {return s+String.fromCharCode(c);}
function _jss_append(a,b) {return a+b;}
function _jss_len(s) {return s.length;}
function _jss_index(s,i) {return s.charCodeAt(i);}
function _jss_drop(s,i) {return s.substr(i);}
function _jss_substr(s,a,b) {return s.substr(a,b);}
function _jss_take(n,s) {return s.substr(0,n);}
// TODO: incorrect for some unusual characters.
function _jss_rev(s) {return s.split("").reverse().join("");}

function _jss_map(f,s) {
    f = E(f);
    var s2 = '';
    for(var i in s) {
        s2 += String.fromCharCode(E(f(s.charCodeAt(i))));
    }
    return s2;
}

function _jss_foldl(f,x,s) {
    f = E(f);
    for(var i in s) {
        x = A(f,[x,s.charCodeAt(i)]);
    }
    return x;
}

function _jss_re_match(s,re) {return s.search(re)>=0;}
function _jss_re_compile(re,fs) {return new RegExp(re,fs);}
function _jss_re_replace(s,re,rep) {return s.replace(re,rep);}

function _jss_re_find(re,s) {
    var a = s.match(re);
    return a ? mklst(a) : [0];
}

function mklst(arr) {
    var l = [0], len = arr.length-1;
    for(var i = 0; i <= len; ++i) {
        l = [1,arr[len-i],l];
    }
    return l;
}

// Create a little endian ArrayBuffer representation of something.
function toABHost(v, n, x) {
    var a = new ArrayBuffer(n);
    new window[v](a)[0] = x;
    return a;
}

function toABSwap(v, n, x) {
    var a = new ArrayBuffer(n);
    new window[v](a)[0] = x;
    var bs = new Uint8Array(a);
    for(var i = 0, j = n-1; i < j; ++i, --j) {
        var tmp = bs[i];
        bs[i] = bs[j];
        bs[j] = tmp;
    }
    return a;
}

window['toABle'] = toABHost;
window['toABbe'] = toABSwap;

// Swap byte order if host is not little endian.
var buffer = new ArrayBuffer(2);
new DataView(buffer).setInt16(0, 256, true);
if(new Int16Array(buffer)[0] !== 256) {
    window['toABle'] = toABSwap;
    window['toABbe'] = toABHost;
}

// MVar implementation.
// Since Haste isn't concurrent, takeMVar and putMVar don't block on empty
// and full MVars respectively, but terminate the program since they would
// otherwise be blocking forever.

function newMVar() {
    return ({empty: true});
}

function tryTakeMVar(mv) {
    if(mv.empty) {
        return [0, 0, undefined];
    } else {
        var val = mv.x;
        mv.empty = true;
        mv.x = null;
        return [0, 1, val];
    }
}

function takeMVar(mv) {
    if(mv.empty) {
        // TODO: real BlockedOnDeadMVar exception, perhaps?
        err("Attempted to take empty MVar!");
    }
    var val = mv.x;
    mv.empty = true;
    mv.x = null;
    return val;
}

function putMVar(mv, val) {
    if(!mv.empty) {
        // TODO: real BlockedOnDeadMVar exception, perhaps?
        err("Attempted to put full MVar!");
    }
    mv.empty = false;
    mv.x = val;
}

function tryPutMVar(mv, val) {
    if(!mv.empty) {
        return 0;
    } else {
        mv.empty = false;
        mv.x = val;
        return 1;
    }
}

function sameMVar(a, b) {
    return (a == b);
}

function isEmptyMVar(mv) {
    return mv.empty ? 1 : 0;
}

// Implementation of stable names.
// Unlike native GHC, the garbage collector isn't going to move data around
// in a way that we can detect, so each object could serve as its own stable
// name if it weren't for the fact we can't turn a JS reference into an
// integer.
// So instead, each object has a unique integer attached to it, which serves
// as its stable name.

var __next_stable_name = 1;
var __stable_table;

function makeStableName(x) {
    if(x instanceof Object) {
        if(!x.stableName) {
            x.stableName = __next_stable_name;
            __next_stable_name += 1;
        }
        return {type: 'obj', name: x.stableName};
    } else {
        return {type: 'prim', name: Number(x)};
    }
}

function eqStableName(x, y) {
    return (x.type == y.type && x.name == y.name) ? 1 : 0;
}

var Integer = function(bits, sign) {
  this.bits_ = [];
  this.sign_ = sign;

  var top = true;
  for (var i = bits.length - 1; i >= 0; i--) {
    var val = bits[i] | 0;
    if (!top || val != sign) {
      this.bits_[i] = val;
      top = false;
    }
  }
};

Integer.IntCache_ = {};

var I_fromInt = function(value) {
  if (-128 <= value && value < 128) {
    var cachedObj = Integer.IntCache_[value];
    if (cachedObj) {
      return cachedObj;
    }
  }

  var obj = new Integer([value | 0], value < 0 ? -1 : 0);
  if (-128 <= value && value < 128) {
    Integer.IntCache_[value] = obj;
  }
  return obj;
};

var I_fromNumber = function(value) {
  if (isNaN(value) || !isFinite(value)) {
    return Integer.ZERO;
  } else if (value < 0) {
    return I_negate(I_fromNumber(-value));
  } else {
    var bits = [];
    var pow = 1;
    for (var i = 0; value >= pow; i++) {
      bits[i] = (value / pow) | 0;
      pow *= Integer.TWO_PWR_32_DBL_;
    }
    return new Integer(bits, 0);
  }
};

var I_fromBits = function(bits) {
  var high = bits[bits.length - 1];
  return new Integer(bits, high & (1 << 31) ? -1 : 0);
};

var I_fromString = function(str, opt_radix) {
  if (str.length == 0) {
    throw Error('number format error: empty string');
  }

  var radix = opt_radix || 10;
  if (radix < 2 || 36 < radix) {
    throw Error('radix out of range: ' + radix);
  }

  if (str.charAt(0) == '-') {
    return I_negate(I_fromString(str.substring(1), radix));
  } else if (str.indexOf('-') >= 0) {
    throw Error('number format error: interior "-" character');
  }

  var radixToPower = I_fromNumber(Math.pow(radix, 8));

  var result = Integer.ZERO;
  for (var i = 0; i < str.length; i += 8) {
    var size = Math.min(8, str.length - i);
    var value = parseInt(str.substring(i, i + size), radix);
    if (size < 8) {
      var power = I_fromNumber(Math.pow(radix, size));
      result = I_add(I_mul(result, power), I_fromNumber(value));
    } else {
      result = I_mul(result, radixToPower);
      result = I_add(result, I_fromNumber(value));
    }
  }
  return result;
};


Integer.TWO_PWR_32_DBL_ = (1 << 16) * (1 << 16);
Integer.ZERO = I_fromInt(0);
Integer.ONE = I_fromInt(1);
Integer.TWO_PWR_24_ = I_fromInt(1 << 24);

var I_toInt = function(self) {
  return self.bits_.length > 0 ? self.bits_[0] : self.sign_;
};

var I_toWord = function(self) {
  return I_toInt(self) >>> 0;
};

var I_toNumber = function(self) {
  if (isNegative(self)) {
    return -I_toNumber(I_negate(self));
  } else {
    var val = 0;
    var pow = 1;
    for (var i = 0; i < self.bits_.length; i++) {
      val += I_getBitsUnsigned(self, i) * pow;
      pow *= Integer.TWO_PWR_32_DBL_;
    }
    return val;
  }
};

var I_getBits = function(self, index) {
  if (index < 0) {
    return 0;
  } else if (index < self.bits_.length) {
    return self.bits_[index];
  } else {
    return self.sign_;
  }
};

var I_getBitsUnsigned = function(self, index) {
  var val = I_getBits(self, index);
  return val >= 0 ? val : Integer.TWO_PWR_32_DBL_ + val;
};

var getSign = function(self) {
  return self.sign_;
};

var isZero = function(self) {
  if (self.sign_ != 0) {
    return false;
  }
  for (var i = 0; i < self.bits_.length; i++) {
    if (self.bits_[i] != 0) {
      return false;
    }
  }
  return true;
};

var isNegative = function(self) {
  return self.sign_ == -1;
};

var isOdd = function(self) {
  return (self.bits_.length == 0) && (self.sign_ == -1) ||
         (self.bits_.length > 0) && ((self.bits_[0] & 1) != 0);
};

var I_equals = function(self, other) {
  if (self.sign_ != other.sign_) {
    return false;
  }
  var len = Math.max(self.bits_.length, other.bits_.length);
  for (var i = 0; i < len; i++) {
    if (I_getBits(self, i) != I_getBits(other, i)) {
      return false;
    }
  }
  return true;
};

var I_notEquals = function(self, other) {
  return !I_equals(self, other);
};

var I_greaterThan = function(self, other) {
  return I_compare(self, other) > 0;
};

var I_greaterThanOrEqual = function(self, other) {
  return I_compare(self, other) >= 0;
};

var I_lessThan = function(self, other) {
  return I_compare(self, other) < 0;
};

var I_lessThanOrEqual = function(self, other) {
  return I_compare(self, other) <= 0;
};

var I_compare = function(self, other) {
  var diff = I_sub(self, other);
  if (isNegative(diff)) {
    return -1;
  } else if (isZero(diff)) {
    return 0;
  } else {
    return +1;
  }
};

var I_compareInt = function(self, other) {
  return I_compare(self, I_fromInt(other));
}

var shorten = function(self, numBits) {
  var arr_index = (numBits - 1) >> 5;
  var bit_index = (numBits - 1) % 32;
  var bits = [];
  for (var i = 0; i < arr_index; i++) {
    bits[i] = I_getBits(self, i);
  }
  var sigBits = bit_index == 31 ? 0xFFFFFFFF : (1 << (bit_index + 1)) - 1;
  var val = I_getBits(self, arr_index) & sigBits;
  if (val & (1 << bit_index)) {
    val |= 0xFFFFFFFF - sigBits;
    bits[arr_index] = val;
    return new Integer(bits, -1);
  } else {
    bits[arr_index] = val;
    return new Integer(bits, 0);
  }
};

var I_negate = function(self) {
  return I_add(not(self), Integer.ONE);
};

var I_add = function(self, other) {
  var len = Math.max(self.bits_.length, other.bits_.length);
  var arr = [];
  var carry = 0;

  for (var i = 0; i <= len; i++) {
    var a1 = I_getBits(self, i) >>> 16;
    var a0 = I_getBits(self, i) & 0xFFFF;

    var b1 = I_getBits(other, i) >>> 16;
    var b0 = I_getBits(other, i) & 0xFFFF;

    var c0 = carry + a0 + b0;
    var c1 = (c0 >>> 16) + a1 + b1;
    carry = c1 >>> 16;
    c0 &= 0xFFFF;
    c1 &= 0xFFFF;
    arr[i] = (c1 << 16) | c0;
  }
  return I_fromBits(arr);
};

var I_sub = function(self, other) {
  return I_add(self, I_negate(other));
};

var I_mul = function(self, other) {
  if (isZero(self)) {
    return Integer.ZERO;
  } else if (isZero(other)) {
    return Integer.ZERO;
  }

  if (isNegative(self)) {
    if (isNegative(other)) {
      return I_mul(I_negate(self), I_negate(other));
    } else {
      return I_negate(I_mul(I_negate(self), other));
    }
  } else if (isNegative(other)) {
    return I_negate(I_mul(self, I_negate(other)));
  }

  if (I_lessThan(self, Integer.TWO_PWR_24_) &&
      I_lessThan(other, Integer.TWO_PWR_24_)) {
    return I_fromNumber(I_toNumber(self) * I_toNumber(other));
  }

  var len = self.bits_.length + other.bits_.length;
  var arr = [];
  for (var i = 0; i < 2 * len; i++) {
    arr[i] = 0;
  }
  for (var i = 0; i < self.bits_.length; i++) {
    for (var j = 0; j < other.bits_.length; j++) {
      var a1 = I_getBits(self, i) >>> 16;
      var a0 = I_getBits(self, i) & 0xFFFF;

      var b1 = I_getBits(other, j) >>> 16;
      var b0 = I_getBits(other, j) & 0xFFFF;

      arr[2 * i + 2 * j] += a0 * b0;
      Integer.carry16_(arr, 2 * i + 2 * j);
      arr[2 * i + 2 * j + 1] += a1 * b0;
      Integer.carry16_(arr, 2 * i + 2 * j + 1);
      arr[2 * i + 2 * j + 1] += a0 * b1;
      Integer.carry16_(arr, 2 * i + 2 * j + 1);
      arr[2 * i + 2 * j + 2] += a1 * b1;
      Integer.carry16_(arr, 2 * i + 2 * j + 2);
    }
  }

  for (var i = 0; i < len; i++) {
    arr[i] = (arr[2 * i + 1] << 16) | arr[2 * i];
  }
  for (var i = len; i < 2 * len; i++) {
    arr[i] = 0;
  }
  return new Integer(arr, 0);
};

Integer.carry16_ = function(bits, index) {
  while ((bits[index] & 0xFFFF) != bits[index]) {
    bits[index + 1] += bits[index] >>> 16;
    bits[index] &= 0xFFFF;
  }
};

var I_mod = function(self, other) {
  return I_rem(I_add(other, I_rem(self, other)), other);
}

var I_div = function(self, other) {
  if(I_greaterThan(self, Integer.ZERO) != I_greaterThan(other, Integer.ZERO)) {
    if(I_rem(self, other) != Integer.ZERO) {
      return I_sub(I_quot(self, other), Integer.ONE);
    }
  }
  return I_quot(self, other);
}

var I_quotRem = function(self, other) {
  return [0, I_quot(self, other), I_rem(self, other)];
}

var I_divMod = function(self, other) {
  return [0, I_div(self, other), I_mod(self, other)];
}

var I_quot = function(self, other) {
  if (isZero(other)) {
    throw Error('division by zero');
  } else if (isZero(self)) {
    return Integer.ZERO;
  }

  if (isNegative(self)) {
    if (isNegative(other)) {
      return I_quot(I_negate(self), I_negate(other));
    } else {
      return I_negate(I_quot(I_negate(self), other));
    }
  } else if (isNegative(other)) {
    return I_negate(I_quot(self, I_negate(other)));
  }

  var res = Integer.ZERO;
  var rem = self;
  while (I_greaterThanOrEqual(rem, other)) {
    var approx = Math.max(1, Math.floor(I_toNumber(rem) / I_toNumber(other)));
    var log2 = Math.ceil(Math.log(approx) / Math.LN2);
    var delta = (log2 <= 48) ? 1 : Math.pow(2, log2 - 48);
    var approxRes = I_fromNumber(approx);
    var approxRem = I_mul(approxRes, other);
    while (isNegative(approxRem) || I_greaterThan(approxRem, rem)) {
      approx -= delta;
      approxRes = I_fromNumber(approx);
      approxRem = I_mul(approxRes, other);
    }

    if (isZero(approxRes)) {
      approxRes = Integer.ONE;
    }

    res = I_add(res, approxRes);
    rem = I_sub(rem, approxRem);
  }
  return res;
};

var I_rem = function(self, other) {
  return I_sub(self, I_mul(I_quot(self, other), other));
};

var not = function(self) {
  var len = self.bits_.length;
  var arr = [];
  for (var i = 0; i < len; i++) {
    arr[i] = ~self.bits_[i];
  }
  return new Integer(arr, ~self.sign_);
};

var I_and = function(self, other) {
  var len = Math.max(self.bits_.length, other.bits_.length);
  var arr = [];
  for (var i = 0; i < len; i++) {
    arr[i] = I_getBits(self, i) & I_getBits(other, i);
  }
  return new Integer(arr, self.sign_ & other.sign_);
};

var I_or = function(self, other) {
  var len = Math.max(self.bits_.length, other.bits_.length);
  var arr = [];
  for (var i = 0; i < len; i++) {
    arr[i] = I_getBits(self, i) | I_getBits(other, i);
  }
  return new Integer(arr, self.sign_ | other.sign_);
};

var I_xor = function(self, other) {
  var len = Math.max(self.bits_.length, other.bits_.length);
  var arr = [];
  for (var i = 0; i < len; i++) {
    arr[i] = I_getBits(self, i) ^ I_getBits(other, i);
  }
  return new Integer(arr, self.sign_ ^ other.sign_);
};

var I_shiftLeft = function(self, numBits) {
  var arr_delta = numBits >> 5;
  var bit_delta = numBits % 32;
  var len = self.bits_.length + arr_delta + (bit_delta > 0 ? 1 : 0);
  var arr = [];
  for (var i = 0; i < len; i++) {
    if (bit_delta > 0) {
      arr[i] = (I_getBits(self, i - arr_delta) << bit_delta) |
               (I_getBits(self, i - arr_delta - 1) >>> (32 - bit_delta));
    } else {
      arr[i] = I_getBits(self, i - arr_delta);
    }
  }
  return new Integer(arr, self.sign_);
};

var I_shiftRight = function(self, numBits) {
  var arr_delta = numBits >> 5;
  var bit_delta = numBits % 32;
  var len = self.bits_.length - arr_delta;
  var arr = [];
  for (var i = 0; i < len; i++) {
    if (bit_delta > 0) {
      arr[i] = (I_getBits(self, i + arr_delta) >>> bit_delta) |
               (I_getBits(self, i + arr_delta + 1) << (32 - bit_delta));
    } else {
      arr[i] = I_getBits(self, i + arr_delta);
    }
  }
  return new Integer(arr, self.sign_);
};

var I_signum = function(self) {
  var cmp = I_compare(self, Integer.ZERO);
  if(cmp > 0) {
    return Integer.ONE
  }
  if(cmp < 0) {
    return I_sub(Integer.ZERO, Integer.ONE);
  }
  return Integer.ZERO;
};

var I_abs = function(self) {
  if(I_compare(self, Integer.ZERO) < 0) {
    return I_sub(Integer.ZERO, self);
  }
  return self;
};

var I_decodeDouble = function(x) {
  var dec = decodeDouble(x);
  var mantissa = I_fromBits([dec[3], dec[2]]);
  if(dec[1] < 0) {
    mantissa = I_negate(mantissa);
  }
  return [0, dec[4], mantissa];
}

var I_toString = function(self) {
  var radix = 10;

  if (isZero(self)) {
    return '0';
  } else if (isNegative(self)) {
    return '-' + I_toString(I_negate(self));
  }

  var radixToPower = I_fromNumber(Math.pow(radix, 6));

  var rem = self;
  var result = '';
  while (true) {
    var remDiv = I_div(rem, radixToPower);
    var intval = I_toInt(I_sub(rem, I_mul(remDiv, radixToPower)));
    var digits = intval.toString();

    rem = remDiv;
    if (isZero(rem)) {
      return digits + result;
    } else {
      while (digits.length < 6) {
        digits = '0' + digits;
      }
      result = '' + digits + result;
    }
  }
};

var I_fromRat = function(a, b) {
    return I_toNumber(a) / I_toNumber(b);
}

function I_fromInt64(x) {
    return I_fromBits([x.getLowBits(), x.getHighBits()]);
}

function I_toInt64(x) {
    return Long.fromBits(I_getBits(x, 0), I_getBits(x, 1));
}

function I_fromWord64(x) {
    return x;
}

function I_toWord64(x) {
    return I_rem(I_add(__w64_max, x), __w64_max);
}

// Copyright 2009 The Closure Library Authors. All Rights Reserved.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//      http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS-IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

var Long = function(low, high) {
  this.low_ = low | 0;
  this.high_ = high | 0;
};

Long.IntCache_ = {};

Long.fromInt = function(value) {
  if (-128 <= value && value < 128) {
    var cachedObj = Long.IntCache_[value];
    if (cachedObj) {
      return cachedObj;
    }
  }

  var obj = new Long(value | 0, value < 0 ? -1 : 0);
  if (-128 <= value && value < 128) {
    Long.IntCache_[value] = obj;
  }
  return obj;
};

Long.fromNumber = function(value) {
  if (isNaN(value) || !isFinite(value)) {
    return Long.ZERO;
  } else if (value <= -Long.TWO_PWR_63_DBL_) {
    return Long.MIN_VALUE;
  } else if (value + 1 >= Long.TWO_PWR_63_DBL_) {
    return Long.MAX_VALUE;
  } else if (value < 0) {
    return Long.fromNumber(-value).negate();
  } else {
    return new Long(
        (value % Long.TWO_PWR_32_DBL_) | 0,
        (value / Long.TWO_PWR_32_DBL_) | 0);
  }
};

Long.fromBits = function(lowBits, highBits) {
  return new Long(lowBits, highBits);
};

Long.TWO_PWR_16_DBL_ = 1 << 16;
Long.TWO_PWR_24_DBL_ = 1 << 24;
Long.TWO_PWR_32_DBL_ =
    Long.TWO_PWR_16_DBL_ * Long.TWO_PWR_16_DBL_;
Long.TWO_PWR_31_DBL_ =
    Long.TWO_PWR_32_DBL_ / 2;
Long.TWO_PWR_48_DBL_ =
    Long.TWO_PWR_32_DBL_ * Long.TWO_PWR_16_DBL_;
Long.TWO_PWR_64_DBL_ =
    Long.TWO_PWR_32_DBL_ * Long.TWO_PWR_32_DBL_;
Long.TWO_PWR_63_DBL_ =
    Long.TWO_PWR_64_DBL_ / 2;
Long.ZERO = Long.fromInt(0);
Long.ONE = Long.fromInt(1);
Long.NEG_ONE = Long.fromInt(-1);
Long.MAX_VALUE =
    Long.fromBits(0xFFFFFFFF | 0, 0x7FFFFFFF | 0);
Long.MIN_VALUE = Long.fromBits(0, 0x80000000 | 0);
Long.TWO_PWR_24_ = Long.fromInt(1 << 24);

Long.prototype.toInt = function() {
  return this.low_;
};

Long.prototype.toNumber = function() {
  return this.high_ * Long.TWO_PWR_32_DBL_ +
         this.getLowBitsUnsigned();
};

Long.prototype.getHighBits = function() {
  return this.high_;
};

Long.prototype.getLowBits = function() {
  return this.low_;
};

Long.prototype.getLowBitsUnsigned = function() {
  return (this.low_ >= 0) ?
      this.low_ : Long.TWO_PWR_32_DBL_ + this.low_;
};

Long.prototype.isZero = function() {
  return this.high_ == 0 && this.low_ == 0;
};

Long.prototype.isNegative = function() {
  return this.high_ < 0;
};

Long.prototype.isOdd = function() {
  return (this.low_ & 1) == 1;
};

Long.prototype.equals = function(other) {
  return (this.high_ == other.high_) && (this.low_ == other.low_);
};

Long.prototype.notEquals = function(other) {
  return (this.high_ != other.high_) || (this.low_ != other.low_);
};

Long.prototype.lessThan = function(other) {
  return this.compare(other) < 0;
};

Long.prototype.lessThanOrEqual = function(other) {
  return this.compare(other) <= 0;
};

Long.prototype.greaterThan = function(other) {
  return this.compare(other) > 0;
};

Long.prototype.greaterThanOrEqual = function(other) {
  return this.compare(other) >= 0;
};

Long.prototype.compare = function(other) {
  if (this.equals(other)) {
    return 0;
  }

  var thisNeg = this.isNegative();
  var otherNeg = other.isNegative();
  if (thisNeg && !otherNeg) {
    return -1;
  }
  if (!thisNeg && otherNeg) {
    return 1;
  }

  if (this.subtract(other).isNegative()) {
    return -1;
  } else {
    return 1;
  }
};

Long.prototype.negate = function() {
  if (this.equals(Long.MIN_VALUE)) {
    return Long.MIN_VALUE;
  } else {
    return this.not().add(Long.ONE);
  }
};

Long.prototype.add = function(other) {
  var a48 = this.high_ >>> 16;
  var a32 = this.high_ & 0xFFFF;
  var a16 = this.low_ >>> 16;
  var a00 = this.low_ & 0xFFFF;

  var b48 = other.high_ >>> 16;
  var b32 = other.high_ & 0xFFFF;
  var b16 = other.low_ >>> 16;
  var b00 = other.low_ & 0xFFFF;

  var c48 = 0, c32 = 0, c16 = 0, c00 = 0;
  c00 += a00 + b00;
  c16 += c00 >>> 16;
  c00 &= 0xFFFF;
  c16 += a16 + b16;
  c32 += c16 >>> 16;
  c16 &= 0xFFFF;
  c32 += a32 + b32;
  c48 += c32 >>> 16;
  c32 &= 0xFFFF;
  c48 += a48 + b48;
  c48 &= 0xFFFF;
  return Long.fromBits((c16 << 16) | c00, (c48 << 16) | c32);
};

Long.prototype.subtract = function(other) {
  return this.add(other.negate());
};

Long.prototype.multiply = function(other) {
  if (this.isZero()) {
    return Long.ZERO;
  } else if (other.isZero()) {
    return Long.ZERO;
  }

  if (this.equals(Long.MIN_VALUE)) {
    return other.isOdd() ? Long.MIN_VALUE : Long.ZERO;
  } else if (other.equals(Long.MIN_VALUE)) {
    return this.isOdd() ? Long.MIN_VALUE : Long.ZERO;
  }

  if (this.isNegative()) {
    if (other.isNegative()) {
      return this.negate().multiply(other.negate());
    } else {
      return this.negate().multiply(other).negate();
    }
  } else if (other.isNegative()) {
    return this.multiply(other.negate()).negate();
  }

  if (this.lessThan(Long.TWO_PWR_24_) &&
      other.lessThan(Long.TWO_PWR_24_)) {
    return Long.fromNumber(this.toNumber() * other.toNumber());
  }

  var a48 = this.high_ >>> 16;
  var a32 = this.high_ & 0xFFFF;
  var a16 = this.low_ >>> 16;
  var a00 = this.low_ & 0xFFFF;

  var b48 = other.high_ >>> 16;
  var b32 = other.high_ & 0xFFFF;
  var b16 = other.low_ >>> 16;
  var b00 = other.low_ & 0xFFFF;

  var c48 = 0, c32 = 0, c16 = 0, c00 = 0;
  c00 += a00 * b00;
  c16 += c00 >>> 16;
  c00 &= 0xFFFF;
  c16 += a16 * b00;
  c32 += c16 >>> 16;
  c16 &= 0xFFFF;
  c16 += a00 * b16;
  c32 += c16 >>> 16;
  c16 &= 0xFFFF;
  c32 += a32 * b00;
  c48 += c32 >>> 16;
  c32 &= 0xFFFF;
  c32 += a16 * b16;
  c48 += c32 >>> 16;
  c32 &= 0xFFFF;
  c32 += a00 * b32;
  c48 += c32 >>> 16;
  c32 &= 0xFFFF;
  c48 += a48 * b00 + a32 * b16 + a16 * b32 + a00 * b48;
  c48 &= 0xFFFF;
  return Long.fromBits((c16 << 16) | c00, (c48 << 16) | c32);
};

Long.prototype.div = function(other) {
  if (other.isZero()) {
    throw Error('division by zero');
  } else if (this.isZero()) {
    return Long.ZERO;
  }

  if (this.equals(Long.MIN_VALUE)) {
    if (other.equals(Long.ONE) ||
        other.equals(Long.NEG_ONE)) {
      return Long.MIN_VALUE;
    } else if (other.equals(Long.MIN_VALUE)) {
      return Long.ONE;
    } else {
      var halfThis = this.shiftRight(1);
      var approx = halfThis.div(other).shiftLeft(1);
      if (approx.equals(Long.ZERO)) {
        return other.isNegative() ? Long.ONE : Long.NEG_ONE;
      } else {
        var rem = this.subtract(other.multiply(approx));
        var result = approx.add(rem.div(other));
        return result;
      }
    }
  } else if (other.equals(Long.MIN_VALUE)) {
    return Long.ZERO;
  }

  if (this.isNegative()) {
    if (other.isNegative()) {
      return this.negate().div(other.negate());
    } else {
      return this.negate().div(other).negate();
    }
  } else if (other.isNegative()) {
    return this.div(other.negate()).negate();
  }

  var res = Long.ZERO;
  var rem = this;
  while (rem.greaterThanOrEqual(other)) {
    var approx = Math.max(1, Math.floor(rem.toNumber() / other.toNumber()));

    var log2 = Math.ceil(Math.log(approx) / Math.LN2);
    var delta = (log2 <= 48) ? 1 : Math.pow(2, log2 - 48);

    var approxRes = Long.fromNumber(approx);
    var approxRem = approxRes.multiply(other);
    while (approxRem.isNegative() || approxRem.greaterThan(rem)) {
      approx -= delta;
      approxRes = Long.fromNumber(approx);
      approxRem = approxRes.multiply(other);
    }

    if (approxRes.isZero()) {
      approxRes = Long.ONE;
    }

    res = res.add(approxRes);
    rem = rem.subtract(approxRem);
  }
  return res;
};

Long.prototype.modulo = function(other) {
  return this.subtract(this.div(other).multiply(other));
};

Long.prototype.not = function() {
  return Long.fromBits(~this.low_, ~this.high_);
};

Long.prototype.and = function(other) {
  return Long.fromBits(this.low_ & other.low_,
                                 this.high_ & other.high_);
};

Long.prototype.or = function(other) {
  return Long.fromBits(this.low_ | other.low_,
                                 this.high_ | other.high_);
};

Long.prototype.xor = function(other) {
  return Long.fromBits(this.low_ ^ other.low_,
                                 this.high_ ^ other.high_);
};

Long.prototype.shiftLeft = function(numBits) {
  numBits &= 63;
  if (numBits == 0) {
    return this;
  } else {
    var low = this.low_;
    if (numBits < 32) {
      var high = this.high_;
      return Long.fromBits(
          low << numBits,
          (high << numBits) | (low >>> (32 - numBits)));
    } else {
      return Long.fromBits(0, low << (numBits - 32));
    }
  }
};

Long.prototype.shiftRight = function(numBits) {
  numBits &= 63;
  if (numBits == 0) {
    return this;
  } else {
    var high = this.high_;
    if (numBits < 32) {
      var low = this.low_;
      return Long.fromBits(
          (low >>> numBits) | (high << (32 - numBits)),
          high >> numBits);
    } else {
      return Long.fromBits(
          high >> (numBits - 32),
          high >= 0 ? 0 : -1);
    }
  }
};

Long.prototype.shiftRightUnsigned = function(numBits) {
  numBits &= 63;
  if (numBits == 0) {
    return this;
  } else {
    var high = this.high_;
    if (numBits < 32) {
      var low = this.low_;
      return Long.fromBits(
          (low >>> numBits) | (high << (32 - numBits)),
          high >>> numBits);
    } else if (numBits == 32) {
      return Long.fromBits(high, 0);
    } else {
      return Long.fromBits(high >>> (numBits - 32), 0);
    }
  }
};



// Int64
function hs_eqInt64(x, y) {return x.equals(y);}
function hs_neInt64(x, y) {return !x.equals(y);}
function hs_ltInt64(x, y) {return x.compare(y) < 0;}
function hs_leInt64(x, y) {return x.compare(y) <= 0;}
function hs_gtInt64(x, y) {return x.compare(y) > 0;}
function hs_geInt64(x, y) {return x.compare(y) >= 0;}
function hs_quotInt64(x, y) {return x.div(y);}
function hs_remInt64(x, y) {return x.modulo(y);}
function hs_plusInt64(x, y) {return x.add(y);}
function hs_minusInt64(x, y) {return x.subtract(y);}
function hs_timesInt64(x, y) {return x.multiply(y);}
function hs_negateInt64(x) {return x.negate();}
function hs_uncheckedIShiftL64(x, bits) {return x.shiftLeft(bits);}
function hs_uncheckedIShiftRA64(x, bits) {return x.shiftRight(bits);}
function hs_uncheckedIShiftRL64(x, bits) {return x.shiftRightUnsigned(bits);}
function hs_intToInt64(x) {return new Long(x, 0);}
function hs_int64ToInt(x) {return x.toInt();}



// Word64
function hs_wordToWord64(x) {
    return I_fromInt(x);
}
function hs_word64ToWord(x) {
    return I_toInt(x);
}
function hs_mkWord64(low, high) {
    return I_fromBits([low, high]);
}

var hs_and64 = I_and;
var hs_or64 = I_or;
var hs_xor64 = I_xor;
var __i64_all_ones = I_fromBits([0xffffffff, 0xffffffff]);
function hs_not64(x) {
    return I_xor(x, __i64_all_ones);
}
var hs_eqWord64 = I_equals;
var hs_neWord64 = I_notEquals;
var hs_ltWord64 = I_lessThan;
var hs_leWord64 = I_lessThanOrEqual;
var hs_gtWord64 = I_greaterThan;
var hs_geWord64 = I_greaterThanOrEqual;
var hs_quotWord64 = I_quot;
var hs_remWord64 = I_rem;
var __w64_max = I_fromBits([0,0,1]);
function hs_uncheckedShiftL64(x, bits) {
    return I_rem(I_shiftLeft(x, bits), __w64_max);
}
var hs_uncheckedShiftRL64 = I_shiftRight;
function hs_int64ToWord64(x) {
    var tmp = I_add(__w64_max, I_fromBits([x.getLowBits(), x.getHighBits()]));
    return I_rem(tmp, __w64_max);
}
function hs_word64ToInt64(x) {
    return Long.fromBits(I_getBits(x, 0), I_getBits(x, 1));
}

// Joseph Myers' MD5 implementation; used under the BSD license.

function md5cycle(x, k) {
    var a = x[0], b = x[1], c = x[2], d = x[3];

    a = ff(a, b, c, d, k[0], 7, -680876936);
    d = ff(d, a, b, c, k[1], 12, -389564586);
    c = ff(c, d, a, b, k[2], 17,  606105819);
    b = ff(b, c, d, a, k[3], 22, -1044525330);
    a = ff(a, b, c, d, k[4], 7, -176418897);
    d = ff(d, a, b, c, k[5], 12,  1200080426);
    c = ff(c, d, a, b, k[6], 17, -1473231341);
    b = ff(b, c, d, a, k[7], 22, -45705983);
    a = ff(a, b, c, d, k[8], 7,  1770035416);
    d = ff(d, a, b, c, k[9], 12, -1958414417);
    c = ff(c, d, a, b, k[10], 17, -42063);
    b = ff(b, c, d, a, k[11], 22, -1990404162);
    a = ff(a, b, c, d, k[12], 7,  1804603682);
    d = ff(d, a, b, c, k[13], 12, -40341101);
    c = ff(c, d, a, b, k[14], 17, -1502002290);
    b = ff(b, c, d, a, k[15], 22,  1236535329);

    a = gg(a, b, c, d, k[1], 5, -165796510);
    d = gg(d, a, b, c, k[6], 9, -1069501632);
    c = gg(c, d, a, b, k[11], 14,  643717713);
    b = gg(b, c, d, a, k[0], 20, -373897302);
    a = gg(a, b, c, d, k[5], 5, -701558691);
    d = gg(d, a, b, c, k[10], 9,  38016083);
    c = gg(c, d, a, b, k[15], 14, -660478335);
    b = gg(b, c, d, a, k[4], 20, -405537848);
    a = gg(a, b, c, d, k[9], 5,  568446438);
    d = gg(d, a, b, c, k[14], 9, -1019803690);
    c = gg(c, d, a, b, k[3], 14, -187363961);
    b = gg(b, c, d, a, k[8], 20,  1163531501);
    a = gg(a, b, c, d, k[13], 5, -1444681467);
    d = gg(d, a, b, c, k[2], 9, -51403784);
    c = gg(c, d, a, b, k[7], 14,  1735328473);
    b = gg(b, c, d, a, k[12], 20, -1926607734);

    a = hh(a, b, c, d, k[5], 4, -378558);
    d = hh(d, a, b, c, k[8], 11, -2022574463);
    c = hh(c, d, a, b, k[11], 16,  1839030562);
    b = hh(b, c, d, a, k[14], 23, -35309556);
    a = hh(a, b, c, d, k[1], 4, -1530992060);
    d = hh(d, a, b, c, k[4], 11,  1272893353);
    c = hh(c, d, a, b, k[7], 16, -155497632);
    b = hh(b, c, d, a, k[10], 23, -1094730640);
    a = hh(a, b, c, d, k[13], 4,  681279174);
    d = hh(d, a, b, c, k[0], 11, -358537222);
    c = hh(c, d, a, b, k[3], 16, -722521979);
    b = hh(b, c, d, a, k[6], 23,  76029189);
    a = hh(a, b, c, d, k[9], 4, -640364487);
    d = hh(d, a, b, c, k[12], 11, -421815835);
    c = hh(c, d, a, b, k[15], 16,  530742520);
    b = hh(b, c, d, a, k[2], 23, -995338651);

    a = ii(a, b, c, d, k[0], 6, -198630844);
    d = ii(d, a, b, c, k[7], 10,  1126891415);
    c = ii(c, d, a, b, k[14], 15, -1416354905);
    b = ii(b, c, d, a, k[5], 21, -57434055);
    a = ii(a, b, c, d, k[12], 6,  1700485571);
    d = ii(d, a, b, c, k[3], 10, -1894986606);
    c = ii(c, d, a, b, k[10], 15, -1051523);
    b = ii(b, c, d, a, k[1], 21, -2054922799);
    a = ii(a, b, c, d, k[8], 6,  1873313359);
    d = ii(d, a, b, c, k[15], 10, -30611744);
    c = ii(c, d, a, b, k[6], 15, -1560198380);
    b = ii(b, c, d, a, k[13], 21,  1309151649);
    a = ii(a, b, c, d, k[4], 6, -145523070);
    d = ii(d, a, b, c, k[11], 10, -1120210379);
    c = ii(c, d, a, b, k[2], 15,  718787259);
    b = ii(b, c, d, a, k[9], 21, -343485551);

    x[0] = add32(a, x[0]);
    x[1] = add32(b, x[1]);
    x[2] = add32(c, x[2]);
    x[3] = add32(d, x[3]);

}

function cmn(q, a, b, x, s, t) {
    a = add32(add32(a, q), add32(x, t));
    return add32((a << s) | (a >>> (32 - s)), b);
}

function ff(a, b, c, d, x, s, t) {
    return cmn((b & c) | ((~b) & d), a, b, x, s, t);
}

function gg(a, b, c, d, x, s, t) {
    return cmn((b & d) | (c & (~d)), a, b, x, s, t);
}

function hh(a, b, c, d, x, s, t) {
    return cmn(b ^ c ^ d, a, b, x, s, t);
}

function ii(a, b, c, d, x, s, t) {
    return cmn(c ^ (b | (~d)), a, b, x, s, t);
}

function md51(s) {
    var n = s.length,
        state = [1732584193, -271733879, -1732584194, 271733878], i;
    for (i=64; i<=s.length; i+=64) {
        md5cycle(state, md5blk(s.substring(i-64, i)));
    }
    s = s.substring(i-64);
    var tail = [0,0,0,0, 0,0,0,0, 0,0,0,0, 0,0,0,0];
    for (i=0; i<s.length; i++)
        tail[i>>2] |= s.charCodeAt(i) << ((i%4) << 3);
    tail[i>>2] |= 0x80 << ((i%4) << 3);
    if (i > 55) {
        md5cycle(state, tail);
        for (i=0; i<16; i++) tail[i] = 0;
    }
    tail[14] = n*8;
    md5cycle(state, tail);
    return state;
}
window['md51'] = md51;

function md5blk(s) {
    var md5blks = [], i;
    for (i=0; i<64; i+=4) {
        md5blks[i>>2] = s.charCodeAt(i)
            + (s.charCodeAt(i+1) << 8)
            + (s.charCodeAt(i+2) << 16)
            + (s.charCodeAt(i+3) << 24);
    }
    return md5blks;
}

var hex_chr = '0123456789abcdef'.split('');

function rhex(n)
{
    var s='', j=0;
    for(; j<4; j++)
        s += hex_chr[(n >> (j * 8 + 4)) & 0x0F]
        + hex_chr[(n >> (j * 8)) & 0x0F];
    return s;
}

function hex(x) {
    for (var i=0; i<x.length; i++)
        x[i] = rhex(x[i]);
    return x.join('');
}

function md5(s) {
    return hex(md51(s));
}

function add32(a, b) {
    return (a + b) & 0xFFFFFFFF;
}

// Functions for dealing with arrays.

function newArr(n, x) {
    var arr = [];
    for(; n >= 0; --n) {
        arr.push(x);
    }
    return arr;
}

// Create all views at once; perhaps it's wasteful, but it's better than having
// to check for the right view at each read or write.
function newByteArr(n) {
    // Pad the thing to multiples of 8.
    var padding = 8 - n % 8;
    if(padding < 8) {
        n += padding;
    }
    var arr = {};
    var buffer = new ArrayBuffer(n);
    var views = {};
    views['i8']  = new Int8Array(buffer);
    views['i16'] = new Int16Array(buffer);
    views['i32'] = new Int32Array(buffer);
    views['w8']  = new Uint8Array(buffer);
    views['w16'] = new Uint16Array(buffer);
    views['w32'] = new Uint32Array(buffer);
    views['f32'] = new Float32Array(buffer);
    views['f64'] = new Float64Array(buffer);
    arr['b'] = buffer;
    arr['v'] = views;
    // ByteArray and Addr are the same thing, so keep an offset if we get
    // casted.
    arr['off'] = 0;
    return arr;
}

// An attempt at emulating pointers enough for ByteString and Text to be
// usable without patching the hell out of them.
// The general idea is that Addr# is a byte array with an associated offset.

function plusAddr(addr, off) {
    var newaddr = {};
    newaddr['off'] = addr['off'] + off;
    newaddr['b']   = addr['b'];
    newaddr['v']   = addr['v'];
    return newaddr;
}

function writeOffAddr(type, elemsize, addr, off, x) {
    addr['v'][type][addr.off/elemsize + off] = x;
}

function readOffAddr(type, elemsize, addr, off) {
    return addr['v'][type][addr.off/elemsize + off];
}

// Two addresses are equal if they point to the same buffer and have the same
// offset. For other comparisons, just use the offsets - nobody in their right
// mind would check if one pointer is less than another, completely unrelated,
// pointer and then act on that information anyway.
function addrEq(a, b) {
    if(a == b) {
        return true;
    }
    return a && b && a['b'] == b['b'] && a['off'] == b['off'];
}

function addrLT(a, b) {
    if(a) {
        return b && a['off'] < b['off'];
    } else {
        return (b != 0); 
    }
}

function addrGT(a, b) {
    if(b) {
        return a && a['off'] > b['off'];
    } else {
        return (a != 0);
    }
}

function withChar(f, charCode) {
    return f(String.fromCharCode(charCode)).charCodeAt(0);
}

function u_towlower(charCode) {
    return withChar(function(c) {return c.toLowerCase()}, charCode);
}

function u_towupper(charCode) {
    return withChar(function(c) {return c.toUpperCase()}, charCode);
}

var u_towtitle = u_towupper;

function u_iswupper(charCode) {
    var c = String.fromCharCode(charCode);
    return c == c.toUpperCase() && c != c.toLowerCase();
}

function u_iswlower(charCode) {
    var c = String.fromCharCode(charCode);
    return  c == c.toLowerCase() && c != c.toUpperCase();
}

function u_iswdigit(charCode) {
    return charCode >= 48 && charCode <= 57;
}

function u_iswcntrl(charCode) {
    return charCode <= 0x1f || charCode == 0x7f;
}

function u_iswspace(charCode) {
    var c = String.fromCharCode(charCode);
    return c.replace(/\s/g,'') != c;
}

function u_iswalpha(charCode) {
    var c = String.fromCharCode(charCode);
    return c.replace(__hs_alphare, '') != c;
}

function u_iswalnum(charCode) {
    return u_iswdigit(charCode) || u_iswalpha(charCode);
}

function u_iswprint(charCode) {
    return !u_iswcntrl(charCode);
}

function u_gencat(c) {
    throw 'u_gencat is only supported with --full-unicode.';
}

// Regex that matches any alphabetic character in any language. Horrible thing.
var __hs_alphare = /[\u0041-\u005A\u0061-\u007A\u00AA\u00B5\u00BA\u00C0-\u00D6\u00D8-\u00F6\u00F8-\u02C1\u02C6-\u02D1\u02E0-\u02E4\u02EC\u02EE\u0370-\u0374\u0376\u0377\u037A-\u037D\u0386\u0388-\u038A\u038C\u038E-\u03A1\u03A3-\u03F5\u03F7-\u0481\u048A-\u0527\u0531-\u0556\u0559\u0561-\u0587\u05D0-\u05EA\u05F0-\u05F2\u0620-\u064A\u066E\u066F\u0671-\u06D3\u06D5\u06E5\u06E6\u06EE\u06EF\u06FA-\u06FC\u06FF\u0710\u0712-\u072F\u074D-\u07A5\u07B1\u07CA-\u07EA\u07F4\u07F5\u07FA\u0800-\u0815\u081A\u0824\u0828\u0840-\u0858\u08A0\u08A2-\u08AC\u0904-\u0939\u093D\u0950\u0958-\u0961\u0971-\u0977\u0979-\u097F\u0985-\u098C\u098F\u0990\u0993-\u09A8\u09AA-\u09B0\u09B2\u09B6-\u09B9\u09BD\u09CE\u09DC\u09DD\u09DF-\u09E1\u09F0\u09F1\u0A05-\u0A0A\u0A0F\u0A10\u0A13-\u0A28\u0A2A-\u0A30\u0A32\u0A33\u0A35\u0A36\u0A38\u0A39\u0A59-\u0A5C\u0A5E\u0A72-\u0A74\u0A85-\u0A8D\u0A8F-\u0A91\u0A93-\u0AA8\u0AAA-\u0AB0\u0AB2\u0AB3\u0AB5-\u0AB9\u0ABD\u0AD0\u0AE0\u0AE1\u0B05-\u0B0C\u0B0F\u0B10\u0B13-\u0B28\u0B2A-\u0B30\u0B32\u0B33\u0B35-\u0B39\u0B3D\u0B5C\u0B5D\u0B5F-\u0B61\u0B71\u0B83\u0B85-\u0B8A\u0B8E-\u0B90\u0B92-\u0B95\u0B99\u0B9A\u0B9C\u0B9E\u0B9F\u0BA3\u0BA4\u0BA8-\u0BAA\u0BAE-\u0BB9\u0BD0\u0C05-\u0C0C\u0C0E-\u0C10\u0C12-\u0C28\u0C2A-\u0C33\u0C35-\u0C39\u0C3D\u0C58\u0C59\u0C60\u0C61\u0C85-\u0C8C\u0C8E-\u0C90\u0C92-\u0CA8\u0CAA-\u0CB3\u0CB5-\u0CB9\u0CBD\u0CDE\u0CE0\u0CE1\u0CF1\u0CF2\u0D05-\u0D0C\u0D0E-\u0D10\u0D12-\u0D3A\u0D3D\u0D4E\u0D60\u0D61\u0D7A-\u0D7F\u0D85-\u0D96\u0D9A-\u0DB1\u0DB3-\u0DBB\u0DBD\u0DC0-\u0DC6\u0E01-\u0E30\u0E32\u0E33\u0E40-\u0E46\u0E81\u0E82\u0E84\u0E87\u0E88\u0E8A\u0E8D\u0E94-\u0E97\u0E99-\u0E9F\u0EA1-\u0EA3\u0EA5\u0EA7\u0EAA\u0EAB\u0EAD-\u0EB0\u0EB2\u0EB3\u0EBD\u0EC0-\u0EC4\u0EC6\u0EDC-\u0EDF\u0F00\u0F40-\u0F47\u0F49-\u0F6C\u0F88-\u0F8C\u1000-\u102A\u103F\u1050-\u1055\u105A-\u105D\u1061\u1065\u1066\u106E-\u1070\u1075-\u1081\u108E\u10A0-\u10C5\u10C7\u10CD\u10D0-\u10FA\u10FC-\u1248\u124A-\u124D\u1250-\u1256\u1258\u125A-\u125D\u1260-\u1288\u128A-\u128D\u1290-\u12B0\u12B2-\u12B5\u12B8-\u12BE\u12C0\u12C2-\u12C5\u12C8-\u12D6\u12D8-\u1310\u1312-\u1315\u1318-\u135A\u1380-\u138F\u13A0-\u13F4\u1401-\u166C\u166F-\u167F\u1681-\u169A\u16A0-\u16EA\u1700-\u170C\u170E-\u1711\u1720-\u1731\u1740-\u1751\u1760-\u176C\u176E-\u1770\u1780-\u17B3\u17D7\u17DC\u1820-\u1877\u1880-\u18A8\u18AA\u18B0-\u18F5\u1900-\u191C\u1950-\u196D\u1970-\u1974\u1980-\u19AB\u19C1-\u19C7\u1A00-\u1A16\u1A20-\u1A54\u1AA7\u1B05-\u1B33\u1B45-\u1B4B\u1B83-\u1BA0\u1BAE\u1BAF\u1BBA-\u1BE5\u1C00-\u1C23\u1C4D-\u1C4F\u1C5A-\u1C7D\u1CE9-\u1CEC\u1CEE-\u1CF1\u1CF5\u1CF6\u1D00-\u1DBF\u1E00-\u1F15\u1F18-\u1F1D\u1F20-\u1F45\u1F48-\u1F4D\u1F50-\u1F57\u1F59\u1F5B\u1F5D\u1F5F-\u1F7D\u1F80-\u1FB4\u1FB6-\u1FBC\u1FBE\u1FC2-\u1FC4\u1FC6-\u1FCC\u1FD0-\u1FD3\u1FD6-\u1FDB\u1FE0-\u1FEC\u1FF2-\u1FF4\u1FF6-\u1FFC\u2071\u207F\u2090-\u209C\u2102\u2107\u210A-\u2113\u2115\u2119-\u211D\u2124\u2126\u2128\u212A-\u212D\u212F-\u2139\u213C-\u213F\u2145-\u2149\u214E\u2183\u2184\u2C00-\u2C2E\u2C30-\u2C5E\u2C60-\u2CE4\u2CEB-\u2CEE\u2CF2\u2CF3\u2D00-\u2D25\u2D27\u2D2D\u2D30-\u2D67\u2D6F\u2D80-\u2D96\u2DA0-\u2DA6\u2DA8-\u2DAE\u2DB0-\u2DB6\u2DB8-\u2DBE\u2DC0-\u2DC6\u2DC8-\u2DCE\u2DD0-\u2DD6\u2DD8-\u2DDE\u2E2F\u3005\u3006\u3031-\u3035\u303B\u303C\u3041-\u3096\u309D-\u309F\u30A1-\u30FA\u30FC-\u30FF\u3105-\u312D\u3131-\u318E\u31A0-\u31BA\u31F0-\u31FF\u3400-\u4DB5\u4E00-\u9FCC\uA000-\uA48C\uA4D0-\uA4FD\uA500-\uA60C\uA610-\uA61F\uA62A\uA62B\uA640-\uA66E\uA67F-\uA697\uA6A0-\uA6E5\uA717-\uA71F\uA722-\uA788\uA78B-\uA78E\uA790-\uA793\uA7A0-\uA7AA\uA7F8-\uA801\uA803-\uA805\uA807-\uA80A\uA80C-\uA822\uA840-\uA873\uA882-\uA8B3\uA8F2-\uA8F7\uA8FB\uA90A-\uA925\uA930-\uA946\uA960-\uA97C\uA984-\uA9B2\uA9CF\uAA00-\uAA28\uAA40-\uAA42\uAA44-\uAA4B\uAA60-\uAA76\uAA7A\uAA80-\uAAAF\uAAB1\uAAB5\uAAB6\uAAB9-\uAABD\uAAC0\uAAC2\uAADB-\uAADD\uAAE0-\uAAEA\uAAF2-\uAAF4\uAB01-\uAB06\uAB09-\uAB0E\uAB11-\uAB16\uAB20-\uAB26\uAB28-\uAB2E\uABC0-\uABE2\uAC00-\uD7A3\uD7B0-\uD7C6\uD7CB-\uD7FB\uF900-\uFA6D\uFA70-\uFAD9\uFB00-\uFB06\uFB13-\uFB17\uFB1D\uFB1F-\uFB28\uFB2A-\uFB36\uFB38-\uFB3C\uFB3E\uFB40\uFB41\uFB43\uFB44\uFB46-\uFBB1\uFBD3-\uFD3D\uFD50-\uFD8F\uFD92-\uFDC7\uFDF0-\uFDFB\uFE70-\uFE74\uFE76-\uFEFC\uFF21-\uFF3A\uFF41-\uFF5A\uFF66-\uFFBE\uFFC2-\uFFC7\uFFCA-\uFFCF\uFFD2-\uFFD7\uFFDA-\uFFDC]/g;

// 2D Canvas drawing primitives.
function jsHasCtx2D(elem) {return !!elem.getContext;}
function jsGetCtx2D(elem) {return elem.getContext('2d');}
function jsBeginPath(ctx) {ctx.beginPath();}
function jsMoveTo(ctx, x, y) {ctx.moveTo(x, y);}
function jsLineTo(ctx, x, y) {ctx.lineTo(x, y);}
function jsStroke(ctx) {ctx.stroke();}
function jsFill(ctx) {ctx.fill();}
function jsRotate(ctx, radians) {ctx.rotate(radians);}
function jsTranslate(ctx, x, y) {ctx.translate(x, y);}
function jsScale(ctx, x, y) {ctx.scale(x, y);}
function jsPushState(ctx) {ctx.save();}
function jsPopState(ctx) {ctx.restore();}
function jsResetCanvas(el) {el.width = el.width;}
function jsDrawImage(ctx, img, x, y) {ctx.drawImage(img, x, y);}
function jsDrawImageClipped(ctx, img, x, y, cx, cy, cw, ch) {
    ctx.drawImage(img, cx, cy, cw, ch, x, y, cw, ch);
}
function jsDrawText(ctx, str, x, y) {ctx.fillText(str, x, y);}
function jsClip(ctx) {ctx.clip();}
function jsArc(ctx, x, y, radius, fromAngle, toAngle) {
    ctx.arc(x, y, radius, fromAngle, toAngle);
}
function jsCanvasToDataURL(el) {return el.toDataURL('image/png');}

// Simulate handles.
// When implementing new handles, remember that passed strings may be thunks,
// and so need to be evaluated before use.

function jsNewHandle(init, read, write, flush, close, seek, tell) {
    var h = {
        read: read || function() {},
        write: write || function() {},
        seek: seek || function() {},
        tell: tell || function() {},
        close: close || function() {},
        flush: flush || function() {}
    };
    init.call(h);
    return h;
}

function jsReadHandle(h, len) {return h.read(len);}
function jsWriteHandle(h, str) {return h.write(str);}
function jsFlushHandle(h) {return h.flush();}
function jsCloseHandle(h) {return h.close();}

function jsMkConWriter(op) {
    return function(str) {
        str = E(str);
        var lines = (this.buf + str).split('\n');
        for(var i = 0; i < lines.length-1; ++i) {
            op.call(console, lines[i]);
        }
        this.buf = lines[lines.length-1];
    }
}

function jsMkStdout() {
    return jsNewHandle(
        function() {this.buf = '';},
        function(_) {return '';},
        jsMkConWriter(console.log),
        function() {console.log(this.buf); this.buf = '';}
    );
}

function jsMkStderr() {
    return jsNewHandle(
        function() {this.buf = '';},
        function(_) {return '';},
        jsMkConWriter(console.warn),
        function() {console.warn(this.buf); this.buf = '';}
    );
}

function jsMkStdin() {
    return jsNewHandle(
        function() {this.buf = '';},
        function(len) {
            while(this.buf.length < len) {
                this.buf += prompt('[stdin]') + '\n';
            }
            var ret = this.buf.substr(0, len);
            this.buf = this.buf.substr(len);
            return ret;
        }
    );
}

// "Weak Pointers". Mostly useless implementation since
// JS does its own GC.

function mkWeak(key, val, fin) {
    fin = !fin? function() {}: fin;
    return {key: key, val: val, fin: fin};
}

function derefWeak(w) {
    return [0, 1, E(w).val];
}

function finalizeWeak(w) {
    return [0, B(A(E(w).fin, [0]))];
}

var __apply = function(f,as) {
    var arr = [];
    for(; as[0] === 1; as = as[2]) {
        arr.push(as[1]);
    }
    arr.reverse();
    return f.apply(null, arr);
}
var __app0 = function(f) {return f();}
var __app1 = function(f,a) {return f(a);}
var __app2 = function(f,a,b) {return f(a,b);}
var __app3 = function(f,a,b,c) {return f(a,b,c);}
var __app4 = function(f,a,b,c,d) {return f(a,b,c,d);}
var __app5 = function(f,a,b,c,d,e) {return f(a,b,c,d,e);}
var __jsNull = function() {return null;}
var __jsTrue = function() {return true;}
var __jsFalse = function() {return false;}
var __eq = function(a,b) {return a===b;}
var __createJSFunc = function(f){
    return (function(){
        var as = Array.prototype.slice.call(arguments);
        as.push(0);
        return E(B(A(f,as)));
    });
}


function __arr2lst(elem,arr) {
    if(elem >= arr.length) {
        return [0];
    }
    return [1, arr[elem],new T(function(){return __arr2lst(elem+1,arr);})]
}

function __lst2arr(xs) {
    var arr = [];
    xs = E(xs);
    for(;xs[0] === 1; xs = E(xs[2])) {
        arr.push(E(xs[1]));
    }
    return arr;
}

var __new = function() {return ({});}
var __set = function(o,k,v) {o[k]=v;}
var __get = function(o,k) {return o[k];}
var __has = function(o,k) {return o[k]!==undefined;}

var _0=function(_1,_2){_1=E(_1);_2=E(_2);return _1!=_2;},_3=function(_4,_5){_4=E(_4);_5=E(_5);return _4==_5;},_6=[0,_3,_0],_7="keyup",_8=[0],_9=function(_a,_){_a=E(_a);if(!_a[0]){return _8;}else{var _b=B(_9(_a[2],_));return [1,_a[1],_b];}},_c=function(_d,_){var _e=__arr2lst(0,_d);return new F(function(){return _9(_e,_);});},_f=function(_g,_){_g=E(_g);return new F(function(){return _c(_g,_);});},_h=function(_i,_){return _i;},_j=[0,_h,_f],_k=function(_l,_){return [1,_l];},_m=function(_n){return E(_n);},_o=[0,_m,_k],_p=function(_q){_q=E(_q);return E(_q[1]);},_r=function(_s){var _t=B(A(_s,[_]));return E(_t);},_u=function(_v,_w,_x,_y){var _z=new T(function(){var _A=new T(function(){var _B=function(_){return new F(function(){return A(_p,[_v,_y,0]);});};return B(_r(_B));});return B(A(_x,[_A]));});return new F(function(){return A(_w,[_z]);});},_C=function(_D,_E,_F){var _G=function(_H){return new F(function(){return _u(_D,_E,_F,_H);});},_I=_G,_J=function(_){return new F(function(){return __createJSFunc(_I);});};return new F(function(){return _r(_J);});},_K=function(_L,_){_L=E(_L);if(!_L[0]){return _8;}else{var _M=_L[1];_M=E(_M);var _N=jsFind(toJSStr(_M)),_O=B(_K(_L[2],_));return [1,_N,_O];}},_P=function(_Q,_R,_){_Q=E(_Q);var _S=jsFind(toJSStr(_Q)),_T=B(_K(_R,_));return [1,_S,_T];},_U=false,_V=true,_W="keyCode",_X="ctrlKey",_Y="altKey",_Z="shiftKey",_10="metaKey",_11=function(_12,_){_W=E(_W);var _13=_12[_W],_14=_13;_X=E(_X);var _15=_12[_X],_16=__jsTrue(),_17=_16,_18=__eq(_15,_17),_19=function(_,_1a){_Y=E(_Y);var _1b=_12[_Y],_1c=__eq(_1b,_17),_1d=function(_,_1e){_Z=E(_Z);var _1f=_12[_Z],_1g=__eq(_1f,_17),_1h=function(_,_1i){_10=E(_10);var _1j=_12[_10],_1k=__eq(_1j,_17),_1l=function(_,_1m){return new T(function(){var _1n=Number(_14),_1o=jsTrunc(_1n);_1a=E(_1a);_1e=E(_1e);_1i=E(_1i);_1m=E(_1m);return [0,_1o,E(_1a),E(_1e),E(_1i),E(_1m)];});};_1k=E(_1k);if(!_1k){return new F(function(){return _1l(_,_U);});}else{return new F(function(){return _1l(_,_V);});}};_1g=E(_1g);if(!_1g){return new F(function(){return _1h(_,_U);});}else{return new F(function(){return _1h(_,_V);});}};_1c=E(_1c);if(!_1c){return new F(function(){return _1d(_,_U);});}else{return new F(function(){return _1d(_,_V);});}};_18=E(_18);if(!_18){return new F(function(){return _19(_,_U);});}else{return new F(function(){return _19(_,_V);});}},_1p=0,_1q=function(_1r){_1r=E(_1r);return E(_1r[1]);},_1s=function(_1t,_1u,_1v,_1w,_1x){var _1y=function(_){_1w=E(_1w);_1x=E(_1x);var _1z=jsSetStyle(B(A(_1q,[_1t,_1v])),toJSStr(_1w),toJSStr(_1x));return _1p;};return new F(function(){return A(_1u,[_1y]);});},_1A="value",_1B=new T(function(){return B(unCStr("backgroundColor"));}),_1C=function(_1D,_1E){_1D=E(_1D);_1E=E(_1E);return _1D==_1E;},_1F=function(_1G,_1H){_1G=E(_1G);_1H=E(_1H);return _1G!=_1H;},_1I=[0,_1C,_1F],_1J=function(_1K,_1L){while(1){_1L=E(_1L);if(!_1L[0]){return true;}else{if(!B(A(_1K,[_1L[1]]))){return false;}else{var _1M=_1L[2];_1L=_1M;continue;}}}},_1N=function(_1O){_1O=E(_1O);return E(_1O[1]);},_1P=function(_1Q,_1R,_1S){while(1){_1S=E(_1S);if(!_1S[0]){return false;}else{if(!B(A(_1N,[_1Q,_1R,_1S[1]]))){var _1T=_1S[2];_1S=_1T;continue;}else{return true;}}}},_1U=function(_1V,_1W){while(1){_1V=E(_1V);if(!_1V[0]){return E(_1W);}else{var _1X=_1V[2],_1Y=_1W+1|0;_1V=_1X;_1W=_1Y;continue;}}},_1Z=function(_20){return new F(function(){return _1U(_20,0);});},_21=6,_22=[1,_21,_8],_23=3,_24=[1,_23,_22],_25=function(_26,_27){if(_26<=_27){var _28=new T(function(){return B(_25(_26+1|0,_27));});return [1,_26,_28];}else{return [0];}},_29=new T(function(){return B(_25(65,70));}),_2a=function(_2b){if(_2b<=57){var _2c=new T(function(){return B(_2a(_2b+1|0));});return [1,_2b,_2c];}else{return E(_29);}},_2d=new T(function(){return B(_2a(48));}),_2e=function(_2f,_2g){_2f=E(_2f);if(!_2f[0]){return E(_2g);}else{var _2h=_2f[2],_2i=new T(function(){return B(_2e(_2h,_2g));});return [1,_2f[1],_2i];}},_2j=function(_2k,_2l){var _2m=jsShowI(_2k);return new F(function(){return _2e(fromJSStr(_2m),_2l);});},_2n=41,_2o=40,_2p=function(_2q,_2r,_2s){if(_2r>=0){return new F(function(){return _2j(_2r,_2s);});}else{if(_2q<=6){return new F(function(){return _2j(_2r,_2s);});}else{var _2t=new T(function(){var _2u=jsShowI(_2r);return B(_2e(fromJSStr(_2u),[1,_2n,_2s]));});return [1,_2o,_2t];}}},_2v=function(_2w){var _2x=new T(function(){return B(_2p(9,_2w,_8));});return new F(function(){return err(B(unAppCStr("Prelude.chr: bad argument: ",_2x)));});},_2y=function(_2z){var _2A=u_towupper(_2z);if(_2A>>>0>1114111){return new F(function(){return _2v(_2A);});}else{return _2A;}},_2B=function(_2C){_2C=E(_2C);return new F(function(){return _2y(_2C);});},_2D=function(_2E){var _2F=new T(function(){return B(_2B(_2E));});return new F(function(){return _1P(_6,_2F,_2d);});},_2G=function(_2H,_2I){while(1){var _2J=(function(_2K,_2L){_2K=E(_2K);if(_2K==35){if(!B(_1J(_2D,_2L))){return [0];}else{var _2M=new T(function(){return B(_1Z(_2L));});return (!B(_1P(_1I,_2M,_24)))?[0]:[1,[1,35,_2L]];}}else{_2H=35;var _2N=[1,_2K,_2L];_2I=_2N;return null;}})(_2H,_2I);if(_2J!=null){return _2J;}}},_2O=new T(function(){return B(_2G(35,_8));}),_2P=function(_2Q){_2Q=E(_2Q);if(!_2Q[0]){return E(_2O);}else{var _2R=_2Q[1],_2S=_2Q[2];_2R=E(_2R);if(_2R==35){if(!B(_1J(_2D,_2S))){return [0];}else{var _2T=new T(function(){return B(_1Z(_2S));});return (!B(_1P(_1I,_2T,_24)))?[0]:[1,_2Q];}}else{return new F(function(){return _2G(35,_2Q);});}}},_2U=function(_2V,_2W,_){_1A=E(_1A);var _2X=jsGet(_2V,_1A),_2Y=B(_2P(fromJSStr(_2X)));if(!_2Y[0]){return _1p;}else{return new F(function(){return A(_1s,[_o,_m,_2W,_1B,_2Y[1],_]);});}},_2Z=function(_){var _30=jsAlert("I\'m missing some elements here! Make sure you have \'left\', \'right\', \'leftCol\' and \'rightCol\'!");return _1p;},_31=new T(function(){return B(unCStr("Prelude.(!!): negative index\n"));}),_32=new T(function(){return B(err(_31));}),_33=new T(function(){return B(unCStr("Prelude.(!!): index too large\n"));}),_34=new T(function(){return B(err(_33));}),_35=function(_36,_37){while(1){_36=E(_36);if(!_36[0]){return E(_34);}else{_37=E(_37);if(!_37){return E(_36[1]);}else{var _38=_36[2],_39=_37-1|0;_36=_38;_37=_39;continue;}}}},_3a=function(_3b,_3c){if(_3b<=0){if(_3b>=0){return new F(function(){return quot(_3b,_3c);});}else{if(_3c<=0){return new F(function(){return quot(_3b,_3c);});}else{return quot(_3b+1|0,_3c)-1|0;}}}else{if(_3c>=0){if(_3b>=0){return new F(function(){return quot(_3b,_3c);});}else{if(_3c<=0){return new F(function(){return quot(_3b,_3c);});}else{return quot(_3b+1|0,_3c)-1|0;}}}else{return quot(_3b-1|0,_3c)-1|0;}}},_3d=new T(function(){return B(unCStr("no negatives allowed"));}),_3e=new T(function(){return B(err(_3d));}),_3f=function(_3g,_3h){var _3i=_3g%_3h;if(_3g<=0){if(_3g>=0){return E(_3i);}else{if(_3h<=0){return E(_3i);}else{_3i=E(_3i);return (_3i==0)?0:_3i+_3h|0;}}}else{if(_3h>=0){if(_3g>=0){return E(_3i);}else{if(_3h<=0){return E(_3i);}else{_3i=E(_3i);return (_3i==0)?0:_3i+_3h|0;}}}else{_3i=E(_3i);return (_3i==0)?0:_3i+_3h|0;}}},_3j=function(_3k){if(_3k>=0){var _3l=function(_3m){var _3n=function(_3o){var _3p=new T(function(){return B(_3j(B(_3f(_3k,16))));},1);return new F(function(){return _2e(B(_3j(B(_3a(_3k,16)))),_3p);});};if(_3k<10){return new F(function(){return _3n(_);});}else{if(_3k>=16){return new F(function(){return _3n(_);});}else{var _3q=new T(function(){var _3r=_3k-10|0;if(_3r>=0){return B(_35(_29,_3r));}else{return E(_32);}});return [1,_3q,_8];}}};if(_3k<0){return new F(function(){return _3l(_);});}else{if(_3k>=10){return new F(function(){return _3l(_);});}else{return new F(function(){return _2p(0,_3k,_8);});}}}else{return E(_3e);}},_3s=48,_3t=function(_3u){_3u=E(_3u);if(!_3u[0]){return [0];}else{var _3v=_3u[1],_3w=_3u[2];_3v=E(_3v);var _3x=new T(function(){return B(_3t(_3w));}),_3y=B(_3j(B(_3a(_3v,2))+128|0));if(!_3y[0]){return E(_3x);}else{var _3z=_3y[1],_3A=_3y[2];_3A=E(_3A);if(!_3A[0]){return new F(function(){return _2e([1,_3s,[1,_3z,_8]],_3x);});}else{var _3B=function(_3C,_3D){_3C=E(_3C);if(!_3C[0]){return E(_3x);}else{var _3E=_3C[1],_3F=_3C[2];if(_3D>1){var _3G=new T(function(){return B(_3B(_3F,_3D-1|0));});return [1,_3E,_3G];}else{return [1,_3E,_3x];}}},_3H=_3z,_3I=_3A,_3J=2;if(_3J>1){var _3K=new T(function(){return B(_3B(_3I,_3J-1|0));});return [1,_3H,_3K];}else{return [1,_3H,_3x];}}}}},_3L=function(_3M,_3N){_3M=E(_3M);var _3O=new T(function(){return B(_3t(_3N));}),_3P=B(_3j(B(_3a(_3M,2))+128|0));if(!_3P[0]){return E(_3O);}else{var _3Q=_3P[1],_3R=_3P[2];_3R=E(_3R);if(!_3R[0]){return new F(function(){return _2e([1,_3s,[1,_3Q,_8]],_3O);});}else{var _3S=function(_3T,_3U){_3T=E(_3T);if(!_3T[0]){return E(_3O);}else{var _3V=_3T[1],_3W=_3T[2];if(_3U>1){var _3X=new T(function(){return B(_3S(_3W,_3U-1|0));});return [1,_3V,_3X];}else{return [1,_3V,_3O];}}},_3Y=_3Q,_3Z=_3R,_40=2;if(_40>1){var _41=new T(function(){return B(_3S(_3Z,_40-1|0));});return [1,_3Y,_41];}else{return [1,_3Y,_3O];}}}},_42=(function(){return window['md51'](jsRand().toString());}),_43=function(_){_42=E(_42);return new F(function(){return _42();});},_44=function(_){return new F(function(){return _43(_);});},_45=new T(function(){return B(unCStr("Control.Exception.Base"));}),_46=new T(function(){return B(unCStr("base"));}),_47=new T(function(){return B(unCStr("PatternMatchFail"));}),_48=new T(function(){var _49=hs_wordToWord64(18445595),_4a=hs_wordToWord64(52003073);return [0,_49,_4a,[0,_49,_4a,_46,_45,_47],_8];}),_4b=function(_4c){return E(_48);},_4d=function(_4e){_4e=E(_4e);return E(_4e[1]);},_4f=function(_4g,_4h,_4i){var _4j=B(A(_4g,[_])),_4k=B(A(_4h,[_])),_4l=hs_eqWord64(_4j[1],_4k[1]);_4l=E(_4l);if(!_4l){return [0];}else{var _4m=hs_eqWord64(_4j[2],_4k[2]);_4m=E(_4m);return (_4m==0)?[0]:[1,_4i];}},_4n=function(_4o){_4o=E(_4o);return new F(function(){return _4f(B(_4d(_4o[1])),_4b,_4o[2]);});},_4p=function(_4q){_4q=E(_4q);return E(_4q[1]);},_4r=function(_4s,_4t){_4s=E(_4s);return new F(function(){return _2e(_4s[1],_4t);});},_4u=44,_4v=93,_4w=91,_4x=function(_4y,_4z,_4A){_4z=E(_4z);if(!_4z[0]){return new F(function(){return unAppCStr("[]",_4A);});}else{var _4B=_4z[1],_4C=_4z[2],_4D=new T(function(){var _4E=new T(function(){var _4F=[1,_4v,_4A],_4G=function(_4H){_4H=E(_4H);if(!_4H[0]){return E(_4F);}else{var _4I=_4H[1],_4J=_4H[2],_4K=new T(function(){var _4L=new T(function(){return B(_4G(_4J));});return B(A(_4y,[_4I,_4L]));});return [1,_4u,_4K];}};return B(_4G(_4C));});return B(A(_4y,[_4B,_4E]));});return [1,_4w,_4D];}},_4M=function(_4N,_4O){return new F(function(){return _4x(_4r,_4N,_4O);});},_4P=function(_4Q,_4R,_4S){_4R=E(_4R);return new F(function(){return _2e(_4R[1],_4S);});},_4T=[0,_4P,_4p,_4M],_4U=new T(function(){return [0,_4b,_4T,_4V,_4n];}),_4V=function(_4W){return [0,_4U,_4W];},_4X=new T(function(){return B(unCStr("Irrefutable pattern failed for pattern"));}),_4Y=function(_4Z,_50){var _51=new T(function(){return B(A(_50,[_4Z]));});return new F(function(){return die(_51);});},_52=function(_53,_54){_54=E(_54);if(!_54[0]){return [0,_8,_8];}else{var _55=_54[1],_56=_54[2];if(!B(A(_53,[_55]))){return [0,_8,_54];}else{var _57=new T(function(){var _58=B(_52(_53,_56));return [0,_58[1],_58[2]];}),_59=new T(function(){_57=E(_57);return E(_57[2]);}),_5a=new T(function(){_57=E(_57);return E(_57[1]);});return [0,[1,_55,_5a],_59];}}},_5b=32,_5c=10,_5d=[1,_5c,_8],_5e=function(_5f){_5f=E(_5f);return (_5f==124)?false:true;},_5g=function(_5h,_5i){var _5j=B(_52(_5e,B(unCStr(_5h)))),_5k=_5j[1],_5l=_5j[2],_5m=function(_5n,_5o){var _5p=new T(function(){var _5q=new T(function(){var _5r=new T(function(){return B(_2e(_5o,_5d));},1);return B(_2e(_5i,_5r));});return B(unAppCStr(": ",_5q));},1);return new F(function(){return _2e(_5n,_5p);});};_5l=E(_5l);if(!_5l[0]){return new F(function(){return _5m(_5k,_8);});}else{var _5s=_5l[1];_5s=E(_5s);if(_5s==124){return new F(function(){return _5m(_5k,[1,_5b,_5l[2]]);});}else{return new F(function(){return _5m(_5k,_8);});}}},_5t=function(_5u){var _5v=new T(function(){return B(_5g(_5u,_4X));});return new F(function(){return _4Y([0,_5v],_4V);});},_5w=function(_5x){return new F(function(){return _5t("ColComp.hs:24:7-47|r : g : b : _");});},_5y=new T(function(){return B(unCStr("ArithException"));}),_5z=new T(function(){return B(unCStr("GHC.Exception"));}),_5A=new T(function(){return B(unCStr("base"));}),_5B=new T(function(){var _5C=hs_wordToWord64(4194982440),_5D=hs_wordToWord64(3110813675);return [0,_5C,_5D,[0,_5C,_5D,_5A,_5z,_5y],_8];}),_5E=function(_5F){return E(_5B);},_5G=function(_5H){_5H=E(_5H);return new F(function(){return _4f(B(_4d(_5H[1])),_5E,_5H[2]);});},_5I=new T(function(){return B(unCStr("arithmetic underflow"));}),_5J=new T(function(){return B(unCStr("arithmetic overflow"));}),_5K=new T(function(){return B(unCStr("Ratio has zero denominator"));}),_5L=new T(function(){return B(unCStr("denormal"));}),_5M=new T(function(){return B(unCStr("divide by zero"));}),_5N=new T(function(){return B(unCStr("loss of precision"));}),_5O=function(_5P){_5P=E(_5P);switch(_5P){case 0:return E(_5J);case 1:return E(_5I);case 2:return E(_5N);case 3:return E(_5M);case 4:return E(_5L);default:return E(_5K);}},_5Q=function(_5R){return new F(function(){return _2e(_5I,_5R);});},_5S=function(_5R){return new F(function(){return _2e(_5J,_5R);});},_5T=function(_5R){return new F(function(){return _2e(_5K,_5R);});},_5U=function(_5R){return new F(function(){return _2e(_5L,_5R);});},_5V=function(_5R){return new F(function(){return _2e(_5M,_5R);});},_5W=function(_5R){return new F(function(){return _2e(_5N,_5R);});},_5X=function(_5Y){_5Y=E(_5Y);switch(_5Y){case 0:return E(_5S);case 1:return E(_5Q);case 2:return E(_5W);case 3:return E(_5V);case 4:return E(_5U);default:return E(_5T);}},_5Z=function(_60,_61){return new F(function(){return _4x(_5X,_60,_61);});},_62=function(_63,_64){_64=E(_64);switch(_64){case 0:return E(_5S);case 1:return E(_5Q);case 2:return E(_5W);case 3:return E(_5V);case 4:return E(_5U);default:return E(_5T);}},_65=[0,_62,_5O,_5Z],_66=new T(function(){return [0,_5E,_65,_67,_5G];}),_67=function(_5R){return [0,_66,_5R];},_68=3,_69=new T(function(){return B(_67(_68));}),_6a=new T(function(){return die(_69);}),_6b=function(_6c){_6c=E(_6c);return E(_6c[1]);},_6d=function(_6e,_6f,_6g,_6h,_6i){_6h=E(_6h);_6i=E(_6i);var _6j=B(A(_6b,[_6e,_6i]));return new F(function(){return A(_6f,[_6g,[1,_6j,_6h]]);});},_6k=function(_6l,_6m){_6m=E(_6m);if(!_6m[0]){return [0];}else{var _6n=_6m[1],_6o=_6m[2],_6p=new T(function(){return B(_6k(_6l,_6o));}),_6q=new T(function(){return B(A(_6l,[_6n]));});return [1,_6q,_6p];}},_6r=function(_6s){return E(_6s);},_6t=function(_6u){return new F(function(){return __lst2arr(B(_6k(_6r,_6u)));});},_6v=[0,_6r,_6t],_6w=function(_6x,_){_6x=E(_6x);if(!_6x[0]){return _8;}else{var _6y=_6x[1],_6z=B(_6w(_6x[2],_)),_6A=new T(function(){_6y=E(_6y);var _6B=Number(_6y);return jsTrunc(_6B);});return [1,_6A,_6z];}},_6C=function(_6D,_){var _6E=__arr2lst(0,_6D);return new F(function(){return _6w(_6E,_);});},_6F=function(_6G,_){_6G=E(_6G);return new F(function(){return _6C(_6G,_);});},_6H=function(_6I,_){return new T(function(){_6I=E(_6I);var _6J=Number(_6I);return jsTrunc(_6J);});},_6K=[0,_6H,_6F],_6L=function(_6M,_6N,_6O,_){_6N=E(_6N);_6O=E(_6O);var _6P=__apply(_6N,_6O);return new F(function(){return A(_p,[_6M,_6P,_]);});},_6Q=function(_6R,_6S,_6T,_){return new F(function(){return _6L(_6R,_6S,_6T,_);});},_6U=function(_6V,_6W,_){return new F(function(){return _6Q(_6K,_6V,_6W,_);});},_6X=(function(s){return s[0];}),_6Y=function(_6Z){return new F(function(){return _6d(_6v,_6U,_6X,_8,_6Z);});},_70=[0,_h,_f],_71=function(_6V,_6W,_){return new F(function(){return _6Q(_70,_6V,_6W,_);});},_72=(function(s){return window['md51'](s.join(','));}),_73=function(_6Z){return new F(function(){return _6d(_6v,_71,_72,_8,_6Z);});},_74=function(_75){var _76=function(_){return new F(function(){return A(_73,[_75,0]);});};return new F(function(){return _r(_76);});},_77=function(_78,_79,_7a){while(1){var _7b=(function(_7c,_7d,_7e){if(_7c>_7d){var _7f=_7d,_7g=_7c,_7h=_7e;_78=_7f;_79=_7g;_7a=_7h;return null;}else{var _7i=new T(function(){return B(_74(_7e));}),_7j=new T(function(){var _7k=(_7d-_7c|0)+1|0;switch(_7k){case -1:return _7c;break;case 0:return E(_6a);break;default:var _7l=function(_){return new F(function(){return A(_6Y,[_7e,0]);});};return B(_3f(B(_r(_7l)),_7k))+_7c|0;}});return [0,_7j,_7i];}})(_78,_79,_7a);if(_7b!=null){return _7b;}}},_7m=function(_7n){return [1,new T(function(){var _7o=B(_77(0,255,_7n));return [0,_7o[1],_7o[2]];})];},_7p=35,_7q=function(_7r,_7s){var _7t=B(A(_7r,[_7s]));if(!_7t[0]){return [0];}else{var _7u=_7t[1];_7u=E(_7u);var _7v=_7u[2],_7w=new T(function(){return B(_7q(_7r,_7v));});return [1,_7u[1],_7w];}},_7x=function(_){var _7y=B(_44(_)),_7z=_7y,_7A=new T(function(){var _7B=new T(function(){var _7C=B(_7q(_7m,_7z));if(!_7C[0]){return B(_5w(_));}else{var _7D=_7C[2];_7D=E(_7D);if(!_7D[0]){return B(_5w(_));}else{var _7E=_7D[2];_7E=E(_7E);if(!_7E[0]){return B(_5w(_));}else{return [0,_7C[1],_7D[1],_7E[1]];}}}}),_7F=new T(function(){_7B=E(_7B);return E(_7B[3]);}),_7G=new T(function(){_7B=E(_7B);return E(_7B[2]);}),_7H=new T(function(){_7B=E(_7B);return E(_7B[1]);});return B(_3L(_7H,[1,_7G,[1,_7F,_8]]));});return [1,_7p,_7A];},_7I=function(_7J){while(1){var _7K=(function(_7L){_7L=E(_7L);if(!_7L[0]){return [0];}else{var _7M=_7L[1],_7N=_7L[2];_7M=E(_7M);if(!_7M[0]){_7J=_7N;return null;}else{var _7O=new T(function(){return B(_7I(_7N));});return [1,_7M[1],_7O];}}})(_7J);if(_7K!=null){return _7K;}}},_7P=function(_7Q,_7R){while(1){_7Q=E(_7Q);if(!_7Q){return E(_7R);}else{_7R=E(_7R);if(!_7R[0]){return [0];}else{var _7S=_7Q-1|0,_7T=_7R[2];_7Q=_7S;_7R=_7T;continue;}}}},_7U=[0],_7V=function(_){return new F(function(){return nMV(_7U);});},_7W=new T(function(){return B(_r(_7V));}),_7X=function(_7Y,_7Z,_80){while(1){_80=E(_80);if(!_80[0]){return [0];}else{var _81=_80[1];_81=E(_81);if(!B(A(_1N,[_7Y,_7Z,_81[1]]))){var _82=_80[2];_80=_82;continue;}else{return [1,_81[2]];}}}},_83=function(_84){_84=E(_84);if(!_84[0]){return [0];}else{var _85=_84[2];_85=E(_85);if(!_85[0]){return [0];}else{var _86=_85[1];_86=E(_86);return (_86==61)?[1,[0,_84[1],_85[2]]]:[0];}}},_87=38,_88=[1,_87,_8],_89=2,_8a=[1,_8],_8b=[1,_8a,_8],_8c=function(_8d){while(1){var _8e=(function(_8f){_8f=E(_8f);if(!_8f[0]){return [0];}else{var _8g=_8f[1],_8h=_8f[2];_8g=E(_8g);if(!_8g[0]){_8d=_8h;return null;}else{var _8i=new T(function(){return B(_8c(_8h));});return [1,_8g,_8i];}}})(_8d);if(_8e!=null){return _8e;}}},_8j=function(_8k){_8k=E(_8k);return (_8k[0]==0)?E(_8k[1]):E(_8k[1]);},_8l=1,_8m=function(_8n,_8o){_8o=E(_8o);if(!_8o[0]){return [0];}else{var _8p=_8o[1],_8q=_8o[2],_8r=function(_8s){_8p=E(_8p);if(!_8p[0]){_8q=E(_8q);if(!_8q[0]){return [1,_8p,_8b];}else{var _8t=_8q[1];_8t=E(_8t);if(!_8t[0]){var _8u=new T(function(){return B(_8m(_8n,_8q));});return [1,_8p,[1,_8a,_8u]];}else{var _8v=new T(function(){return B(_8m(_8n,_8q));});return [1,_8p,_8v];}}}else{var _8w=new T(function(){return B(_8m(_8n,_8q));});return [1,_8p,_8w];}};_8n=E(_8n);if(_8n==1){_8p=E(_8p);if(!_8p[0]){_8q=E(_8q);if(!_8q[0]){return new F(function(){return _8r(_);});}else{var _8x=_8q[1];_8x=E(_8x);if(!_8x[0]){var _8y=new T(function(){return B(_8m(_8l,_8q));});return [1,_8p,_8y];}else{return new F(function(){return _8r(_);});}}}else{return new F(function(){return _8r(_);});}}else{return new F(function(){return _8r(_);});}}},_8z=function(_8A,_8B){_8A=E(_8A);if(!_8A[0]){return [1,[0,_8,_8B]];}else{_8B=E(_8B);if(!_8B[0]){return [0];}else{var _8C=_8B[1];if(!B(A(_8A[1],[_8C]))){return [0];}else{var _8D=B(_8z(_8A[2],_8B[2]));if(!_8D[0]){return [0];}else{var _8E=_8D[1];_8E=E(_8E);return [1,[0,[1,_8C,_8E[1]],_8E[2]]];}}}}},_8F=function(_8G,_8H){_8G=E(_8G);if(!_8G[0]){return [0,_8,[1,[0,_8,_8H]]];}else{_8H=E(_8H);if(!_8H[0]){return [0,_8,_7U];}else{var _8I=_8H[2],_8J=B(_8z(_8G,_8H));if(!_8J[0]){var _8K=new T(function(){var _8L=B(_8F(_8G,_8I));return [0,_8L[1],_8L[2]];}),_8M=new T(function(){_8K=E(_8K);return E(_8K[2]);}),_8N=new T(function(){_8K=E(_8K);return E(_8K[1]);});return [0,[1,_8H[1],_8N],_8M];}else{return [0,_8,_8J];}}}},_8O=[0,_8],_8P=function(_8Q,_8R){_8R=E(_8R);if(!_8R[0]){return [0];}else{var _8S=B(_8F(_8Q,_8R)),_8T=_8S[1],_8U=_8S[2],_8V=function(_8W){_8W=E(_8W);if(!_8W[0]){return [0];}else{var _8X=_8W[1];_8X=E(_8X);var _8Y=_8X[1],_8Z=_8X[2];_8Y=E(_8Y);if(!_8Y[0]){_8Z=E(_8Z);if(!_8Z[0]){var _90=new T(function(){return B(_8P(_8Q,_8));});return [1,_8O,_90];}else{var _91=_8Z[2],_92=new T(function(){return B(_8P(_8Q,_91));});return [1,_8O,[1,[1,[1,_8Z[1],_8]],_92]];}}else{var _93=new T(function(){return B(_8P(_8Q,_8Z));});return [1,[0,_8Y],_93];}}};_8T=E(_8T);if(!_8T[0]){return new F(function(){return _8V(_8U);});}else{var _94=new T(function(){return B(_8V(_8U));});return [1,[1,_8T],_94];}}},_95=function(_96,_97){var _98=new T(function(){var _99=new T(function(){return B(_1N(_96));});return B(_6k(_99,_97));}),_9a=function(_9b){var _9c=B(_8P(_98,_9b));if(!_9c[0]){var _9d=B(_8c(_8b));if(!_9d[0]){return new F(function(){return _6k(_8j,_8);});}else{return new F(function(){return _6k(_8j,_9d);});}}else{var _9e=_9c[1];_9e=E(_9e);if(!_9e[0]){var _9f=new T(function(){return B(_8m(_89,_9c));}),_9g=B(_8c([1,_8a,_9f]));if(!_9g[0]){return new F(function(){return _6k(_8j,_8);});}else{return new F(function(){return _6k(_8j,_9g);});}}else{var _9h=B(_8c(B(_8m(_89,_9c))));if(!_9h[0]){return new F(function(){return _6k(_8j,_8);});}else{return new F(function(){return _6k(_8j,_9h);});}}}};return E(_9a);},_9i=new T(function(){return B(_95(_6,_88));}),_9j=114,_9k=108,_9l=new T(function(){return B(unCStr("left"));}),_9m=new T(function(){return B(unCStr("right"));}),_9n=new T(function(){return B(unCStr("leftCol"));}),_9o=new T(function(){return B(unCStr("rightCol"));}),_9p=[1,_9o,_8],_9q=[1,_9n,_9p],_9r=[1,_9m,_9q],_9s=new T(function(){return __jsNull();}),_9t=new T(function(){return E(_9s);}),_9u=new T(function(){return E(_9t);}),_9v=function(_9w,_){var _9x=B(A(_9w,[_]));return _9u;},_9y=(function(e,name,f){e.addEventListener(name,f,false);return [f];}),_9z=function(_){var _9A=function() {return window.location.hash},_9B=_9A,_9C=new T(function(){return E(_9B);});_9C=E(_9C);var _9D=_9C(),_9E=_9D,_9F=B(_P(_9l,_9r,_)),_9G=B(_7I(_9F));if(!_9G[0]){return new F(function(){return _2Z(_);});}else{var _9H=_9G[1],_9I=_9G[2];_9I=E(_9I);if(!_9I[0]){return new F(function(){return _2Z(_);});}else{var _9J=_9I[1],_9K=_9I[2];_9K=E(_9K);if(!_9K[0]){return new F(function(){return _2Z(_);});}else{var _9L=_9K[1],_9M=_9K[2];_9M=E(_9M);if(!_9M[0]){return new F(function(){return _2Z(_);});}else{var _9N=_9M[1],_9O=_9M[2];_9O=E(_9O);if(!_9O[0]){_9H=E(_9H);var _9P=_9H;_1A=E(_1A);var _9Q=_1A,_9R=jsGet(_9P,_9Q),_9S=function(_){var _9T=new T(function(){var _9U=new T(function(){var _9V=String(_9E);return B(_7P(1,fromJSStr(_9V)));});return B(_7I(B(_6k(_83,B(A(_9i,[_9U]))))));}),_9W=function(_){var _9X=function(_){var _9Y=jsGet(_9P,_9Q),_9Z=function(_){_9J=E(_9J);var _a0=_9J,_a1=jsGet(_a0,_9Q),_a2=function(_){_7=E(_7);var _a3=function(_a4,_){_7W=E(_7W);var _=wMV(_7W,[1,_a4]);_a4=E(_a4);var _a5=B(_11(_a4,_));return new F(function(){return _2U(_9P,_9L,_);});};_9y=E(_9y);var _a6=_9y(_9P,_7,B(_C(_j,_9v,_a3))),_a7=function(_a8,_){_7W=E(_7W);var _=wMV(_7W,[1,_a8]);_a8=E(_a8);var _a9=B(_11(_a8,_));return new F(function(){return _2U(_a0,_9N,_);});},_aa=_9y(_a0,_7,B(_C(_j,_9v,_a7)));return _1p;},_ab=B(_2P(fromJSStr(_a1)));if(!_ab[0]){return new F(function(){return _a2(_);});}else{var _ac=B(A(_1s,[_o,_m,_9N,_1B,_ab[1],_]));return new F(function(){return _a2(_);});}},_ad=B(_2P(fromJSStr(_9Y)));if(!_ad[0]){return new F(function(){return _9Z(_);});}else{var _ae=B(A(_1s,[_o,_m,_9L,_1B,_ad[1],_]));return new F(function(){return _9Z(_);});}},_af=B(_7X(_6,_9j,_9T));if(!_af[0]){var _ag=B(_7x(_));_9J=E(_9J);_ag=E(_ag);var _ah=jsSet(_9J,"value",toJSStr(_ag));return new F(function(){return _9X(_);});}else{var _ai=_af[1];_9J=E(_9J);_ai=E(_ai);var _aj=jsSet(_9J,"value",toJSStr(_ai));return new F(function(){return _9X(_);});}},_ak=B(_7X(_6,_9k,_9T));if(!_ak[0]){var _al=B(_7x(_));_al=E(_al);var _am=jsSet(_9P,"value",toJSStr(_al));return new F(function(){return _9W(_);});}else{var _an=_ak[1];_an=E(_an);var _ao=jsSet(_9P,"value",toJSStr(_an));return new F(function(){return _9W(_);});}},_ap=B(_2P(fromJSStr(_9R)));if(!_ap[0]){return new F(function(){return _9S(_);});}else{var _aq=B(A(_1s,[_o,_m,_9L,_1B,_ap[1],_]));return new F(function(){return _9S(_);});}}else{return new F(function(){return _2Z(_);});}}}}}},_ar=function(_){return new F(function(){return _9z(_);});};
var hasteMain = function() {B(A(_ar, [0]));};window.onload = hasteMain;