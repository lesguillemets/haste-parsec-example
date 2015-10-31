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

// "Zero" object; used to avoid creating a whole bunch of new objects
// in the extremely common case of a nil-like data constructor.
var __Z = {_:0};

// Special object used for blackholing.
var __blackhole = {};

// Used to indicate that an object is updatable.
var __updatable = {};

// Indicates that a closure-creating tail loop isn't done.
var __continue = {};

/* Generic apply.
   Applies a function *or* a partial application object to a list of arguments.
   See https://ghc.haskell.org/trac/ghc/wiki/Commentary/Rts/HaskellExecution/FunctionCalls
   for more information.
*/
function A(f, args) {
    while(true) {
        f = E(f);
        if(f instanceof Function) {
            if(args.length === f.length) {
                return f.apply(null, args);
            } else if(args.length < f.length) {
                return new PAP(f, args);
            } else {
                var f2 = f.apply(null, args.slice(0, f.length));
                args = args.slice(f.length);
                f = B(f2);
            }
        } else if(f instanceof PAP) {
            if(args.length === f.arity) {
                return f.f.apply(null, f.args.concat(args));
            } else if(args.length < f.arity) {
                return new PAP(f.f, f.args.concat(args));
            } else {
                var f2 = f.f.apply(null, f.args.concat(args.slice(0, f.arity)));
                args = args.slice(f.arity);
                f = B(f2);
            }
        } else {
            return f;
        }
    }
}

function A1(f, x) {
    f = E(f);
    if(f instanceof Function) {
        return f.length === 1 ? f(x) : new PAP(f, [x]);
    } else if(f instanceof PAP) {
        return f.arity === 1 ? f.f.apply(null, f.args.concat([x]))
                             : new PAP(f.f, f.args.concat([x]));
    } else {
        return f;
    }
}

function A2(f, x, y) {
    f = E(f);
    if(f instanceof Function) {
        switch(f.length) {
        case 2:  return f(x, y);
        case 1:  return A1(B(f(x)), y);
        default: return new PAP(f, [x,y]);
        }
    } else if(f instanceof PAP) {
        switch(f.arity) {
        case 2:  return f.f.apply(null, f.args.concat([x,y]));
        case 1:  return A1(B(f.f.apply(null, f.args.concat([x]))), y);
        default: return new PAP(f.f, f.args.concat([x,y]));
        }
    } else {
        return f;
    }
}

function A3(f, x, y, z) {
    f = E(f);
    if(f instanceof Function) {
        switch(f.length) {
        case 3:  return f(x, y, z);
        case 2:  return A1(B(f(x, y)), z);
        case 1:  return A2(B(f(x)), y, z);
        default: return new PAP(f, [x,y,z]);
        }
    } else if(f instanceof PAP) {
        switch(f.arity) {
        case 3:  return f.f.apply(null, f.args.concat([x,y,z]));
        case 2:  return A1(B(f.f.apply(null, f.args.concat([x,y]))), z);
        case 1:  return A2(B(f.f.apply(null, f.args.concat([x]))), y, z);
        default: return new PAP(f.f, f.args.concat([x,y,z]));
        }
    } else {
        return f;
    }
}

/* Eval
   Evaluate the given thunk t into head normal form.
   If the "thunk" we get isn't actually a thunk, just return it.
*/
function E(t) {
    if(t instanceof T) {
        if(t.f !== __blackhole) {
            if(t.x === __updatable) {
                var f = t.f;
                t.f = __blackhole;
                t.x = f();
            } else {
                return t.f();
            }
        }
        if(t.x === __updatable) {
            throw 'Infinite loop!';
        } else {
            return t.x;
        }
    } else {
        return t;
    }
}

/* Tail call chain counter. */
var C = 0, Cs = [];

/* Bounce
   Bounce on a trampoline for as long as we get a function back.
*/
function B(f) {
    Cs.push(C);
    while(f instanceof F) {
        var fun = f.f;
        f.f = __blackhole;
        C = 0;
        f = fun();
    }
    C = Cs.pop();
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
    return {_:0, a:(a-a%b)/b, b:a%b};
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
    return {_:0, a:x & 0xffffffff, b:x > 0x7fffffff};
}

function subC(a, b) {
    var x = a-b;
    return {_:0, a:x & 0xffffffff, b:x < -2147483648};
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
function unCStr(str) {return unAppCStr(str, __Z);}

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
        return {_:1,a:str.charCodeAt(i),b:new T(function() {
            return unAppCStr(str,chrs,i+1);
        })};
    }
}

function charCodeAt(str, i) {return str.charCodeAt(i);}

function fromJSStr(str) {
    return unCStr(E(str));
}

function toJSStr(hsstr) {
    var s = '';
    for(var str = E(hsstr); str._ == 1; str = E(str.b)) {
        s += String.fromCharCode(E(str.a));
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
    mv.x = x.a;
    return x.b;
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
    if(x instanceof Object) {
        return x._;
    } else {
        return x;
    }
}

function __word_encodeDouble(d, e) {
    return d * Math.pow(2,e);
}

var __word_encodeFloat = __word_encodeDouble;
var jsRound = Math.round, rintDouble = jsRound, rintFloat = jsRound;
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

function popCnt64(i) {
    return popCnt(I_getBits(i,0)) + popCnt(I_getBits(i,1));
}

function popCnt(i) {
    i = i - ((i >> 1) & 0x55555555);
    i = (i & 0x33333333) + ((i >> 2) & 0x33333333);
    return (((i + (i >> 4)) & 0x0F0F0F0F) * 0x01010101) >> 24;
}

function __clz(bits, x) {
    x &= (Math.pow(2, bits)-1);
    if(x === 0) {
        return bits;
    } else {
        return bits - (1 + Math.floor(Math.log(x)/Math.LN2));
    }
}

// TODO: can probably be done much faster with arithmetic tricks like __clz
function __ctz(bits, x) {
    var y = 1;
    x &= (Math.pow(2, bits)-1);
    if(x === 0) {
        return bits;
    }
    for(var i = 0; i < bits; ++i) {
        if(y & x) {
            return i;
        } else {
            y <<= 1;
        }
    }
    return 0;
}

// Scratch space for byte arrays.
var rts_scratchBuf = new ArrayBuffer(8);
var rts_scratchW32 = new Uint32Array(rts_scratchBuf);
var rts_scratchFloat = new Float32Array(rts_scratchBuf);
var rts_scratchDouble = new Float64Array(rts_scratchBuf);

function decodeFloat(x) {
    if(x === 0) {
        return __decodedZeroF;
    }
    rts_scratchFloat[0] = x;
    var sign = x < 0 ? -1 : 1;
    var exp = ((rts_scratchW32[0] >> 23) & 0xff) - 150;
    var man = rts_scratchW32[0] & 0x7fffff;
    if(exp === 0) {
        ++exp;
    } else {
        man |= (1 << 23);
    }
    return {_:0, a:sign*man, b:exp};
}

var __decodedZero = {_:0,a:1,b:0,c:0,d:0};
var __decodedZeroF = {_:0,a:1,b:0};

function decodeDouble(x) {
    if(x === 0) {
        // GHC 7.10+ *really* doesn't like 0 to be represented as anything
        // but zeroes all the way.
        return __decodedZero;
    }
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
    return {_:0, a:sign, b:manHigh, c:manLow, d:exp};
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

var jsRand = Math.random;

// Concatenate a Haskell list of JS strings
function jsCat(strs, sep) {
    var arr = [];
    strs = E(strs);
    while(strs._) {
        strs = E(strs);
        arr.push(E(strs.a));
        strs = E(strs.b);
    }
    return arr.join(sep);
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
        return __Z;
    }
    return {_:1,a:hs};
}

function toHS(obj) {
    switch(typeof obj) {
    case 'number':
        return {_:0, a:jsRead(obj)};
    case 'string':
        return {_:1, a:obj};
    case 'boolean':
        return {_:2, b:obj}; // Booleans are special wrt constructor tags!
    case 'object':
        if(obj instanceof Array) {
            return {_:3, a:arr2lst_json(obj, 0)};
        } else if (obj == null) {
            return {_:5};
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
                xs = {_:1, a:{_:0, a:ks[i], b:toHS(obj[ks[i]])}, b:xs};
            }
            return {_:4, a:xs};
        }
    }
}

function arr2lst_json(arr, elem) {
    if(elem >= arr.length) {
        return __Z;
    }
    return {_:1, a:toHS(arr[elem]), b:new T(function() {return arr2lst_json(arr,elem+1);}),c:true}
}

/* gettimeofday(2) */
function gettimeofday(tv, _tz) {
    var t = new Date().getTime();
    writeOffAddr("i32", 4, tv, 0, (t/1000)|0);
    writeOffAddr("i32", 4, tv, 1, ((t%1000)*1000)|0);
    return 0;
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
        return {_:0, a:0, b:undefined};
    } else {
        var val = mv.x;
        mv.empty = true;
        mv.x = null;
        return {_:0, a:1, b:val};
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
  return {_:0, a:I_quot(self, other), b:I_rem(self, other)};
}

var I_divMod = function(self, other) {
  return {_:0, a:I_div(self, other), b:I_mod(self, other)};
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
  return {_:0, a:dec[4], b:mantissa};
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

// Joseph Myers' MD5 implementation, ported to work on typed arrays.
// Used under the BSD license.
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

function md51(s, n) {
    var a = s['v']['w8'];
    var orig_n = n,
        state = [1732584193, -271733879, -1732584194, 271733878], i;
    for (i=64; i<=n; i+=64) {
        md5cycle(state, md5blk(a.subarray(i-64, i)));
    }
    a = a.subarray(i-64);
    n = n < (i-64) ? 0 : n-(i-64);
    var tail = [0,0,0,0, 0,0,0,0, 0,0,0,0, 0,0,0,0];
    for (i=0; i<n; i++)
        tail[i>>2] |= a[i] << ((i%4) << 3);
    tail[i>>2] |= 0x80 << ((i%4) << 3);
    if (i > 55) {
        md5cycle(state, tail);
        for (i=0; i<16; i++) tail[i] = 0;
    }
    tail[14] = orig_n*8;
    md5cycle(state, tail);
    return state;
}
window['md51'] = md51;

function md5blk(s) {
    var md5blks = [], i;
    for (i=0; i<64; i+=4) {
        md5blks[i>>2] = s[i]
            + (s[i+1] << 8)
            + (s[i+2] << 16)
            + (s[i+3] << 24);
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

function md5(s, n) {
    return hex(md51(s, n));
}

window['md5'] = md5;

function add32(a, b) {
    return (a + b) & 0xFFFFFFFF;
}

function __hsbase_MD5Init(ctx) {}
// Note that this is a one time "update", since that's all that's used by
// GHC.Fingerprint.
function __hsbase_MD5Update(ctx, s, n) {
    ctx.md5 = md51(s, n);
}
function __hsbase_MD5Final(out, ctx) {
    var a = out['v']['i32'];
    a[0] = ctx.md5[0];
    a[1] = ctx.md5[1];
    a[2] = ctx.md5[2];
    a[3] = ctx.md5[3];
}

// Functions for dealing with arrays.

function newArr(n, x) {
    var arr = new Array(n);
    for(var i = 0; i < n; ++i) {
        arr[i] = x;
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
window['newByteArr'] = newByteArr;

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
    return {_:0, a:1, b:E(w).val};
}

function finalizeWeak(w) {
    return {_:0, a:B(A(E(w).fin, __Z))};
}

/* For foreign import ccall "wrapper" */
function createAdjustor(args, f, a, b) {
    return function(){
        var x = f.apply(null, arguments);
        while(x instanceof F) {x = x.f();}
        return x;
    };
}

var __apply = function(f,as) {
    var arr = [];
    for(; as._ === 1; as = as.b) {
        arr.push(as.a);
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
var __eq = function(a,b) {return a===b;}
var __createJSFunc = function(arity, f){
    if(f instanceof Function && arity === f.length) {
        return (function() {
            var x = f.apply(null,arguments);
            if(x instanceof T) {
                if(x.f !== __blackhole) {
                    var ff = x.f;
                    x.f = __blackhole;
                    return x.x = ff();
                }
                return x.x;
            } else {
                while(x instanceof F) {
                    x = x.f();
                }
                return E(x);
            }
        });
    } else {
        return (function(){
            var as = Array.prototype.slice.call(arguments);
            as.push(0);
            return E(B(A(f,as)));
        });
    }
}


function __arr2lst(elem,arr) {
    if(elem >= arr.length) {
        return __Z;
    }
    return {_:1,
            a:arr[elem],
            b:new T(function(){return __arr2lst(elem+1,arr);})};
}

function __lst2arr(xs) {
    var arr = [];
    xs = E(xs);
    for(;xs._ === 1; xs = E(xs.b)) {
        arr.push(E(xs.a));
    }
    return arr;
}

var __new = function() {return ({});}
var __set = function(o,k,v) {o[k]=v;}
var __get = function(o,k) {return o[k];}
var __has = function(o,k) {return o[k]!==undefined;}

var _0=function(_1,_){var _2=_1["keyCode"],_3=_1["ctrlKey"],_4=_1["altKey"],_5=_1["shiftKey"],_6=_1["metaKey"];return new T(function(){var _7=Number(_2),_8=jsTrunc(_7);return {_:0,a:_8,b:E(_3),c:E(_4),d:E(_5),e:E(_6)};});},_9=function(_a,_b,_){return _0(E(_b),_);},_c=function(_d){switch(E(_d)){case 0:return "keypress";case 1:return "keyup";default:return "keydown";}},_e=function(_){return 0;},_f=function(_g,_){return {_:1,a:_g};},_h=function(_i){return E(_i);},_j=function(_k,_l,_){var _m=B(A1(_k,_)),_n=B(A1(_l,_));return new T(function(){return B(A1(_m,_n));});},_o=function(_p,_q,_){var _r=B(A1(_q,_));return new T(function(){return B(A1(_p,_r));});},_s=function(_t,_){return _t;},_u=function(_v,_w,_){var _x=B(A1(_v,_));return C > 19 ? new F(function(){return A1(_w,_);}) : (++C,A1(_w,_));},_y=new T(function(){var _z=hs_wordToWord64(I_fromBits([4053623282,1685460941])),_A=hs_wordToWord64(I_fromBits([3693590983,2507416641]));return {_:0,a:_z,b:_A,c:{_:0,a:_z,b:_A,c:new T(function(){return unCStr("base");}),d:new T(function(){return unCStr("GHC.IO.Exception");}),e:new T(function(){return unCStr("IOException");})},d:__Z,e:__Z};}),_B=function(_C){return E(_y);},_D=function(_E){return E(E(_E).a);},_F=function(_G,_H,_I){var _J=B(A1(_G,_)),_K=B(A1(_H,_)),_L=hs_eqWord64(_J.a,_K.a);if(!_L){return __Z;}else{var _M=hs_eqWord64(_J.b,_K.b);return (!_M)?__Z:{_:1,a:_I};}},_N=new T(function(){return unCStr(": ");}),_O=new T(function(){return unCStr(")");}),_P=new T(function(){return unCStr(" (");}),_Q=function(_R,_S){var _T=E(_R);return (_T._==0)?E(_S):{_:1,a:_T.a,b:new T(function(){return _Q(_T.b,_S);})};},_U=new T(function(){return unCStr("interrupted");}),_V=new T(function(){return unCStr("system error");}),_W=new T(function(){return unCStr("unsatisified constraints");}),_X=new T(function(){return unCStr("user error");}),_Y=new T(function(){return unCStr("permission denied");}),_Z=new T(function(){return unCStr("illegal operation");}),_10=new T(function(){return unCStr("end of file");}),_11=new T(function(){return unCStr("resource exhausted");}),_12=new T(function(){return unCStr("resource busy");}),_13=new T(function(){return unCStr("does not exist");}),_14=new T(function(){return unCStr("already exists");}),_15=new T(function(){return unCStr("resource vanished");}),_16=new T(function(){return unCStr("timeout");}),_17=new T(function(){return unCStr("unsupported operation");}),_18=new T(function(){return unCStr("hardware fault");}),_19=new T(function(){return unCStr("inappropriate type");}),_1a=new T(function(){return unCStr("invalid argument");}),_1b=new T(function(){return unCStr("failed");}),_1c=new T(function(){return unCStr("protocol error");}),_1d=function(_1e,_1f){switch(E(_1e)){case 0:return _Q(_14,_1f);case 1:return _Q(_13,_1f);case 2:return _Q(_12,_1f);case 3:return _Q(_11,_1f);case 4:return _Q(_10,_1f);case 5:return _Q(_Z,_1f);case 6:return _Q(_Y,_1f);case 7:return _Q(_X,_1f);case 8:return _Q(_W,_1f);case 9:return _Q(_V,_1f);case 10:return _Q(_1c,_1f);case 11:return _Q(_1b,_1f);case 12:return _Q(_1a,_1f);case 13:return _Q(_19,_1f);case 14:return _Q(_18,_1f);case 15:return _Q(_17,_1f);case 16:return _Q(_16,_1f);case 17:return _Q(_15,_1f);default:return _Q(_U,_1f);}},_1g=new T(function(){return unCStr("}");}),_1h=new T(function(){return unCStr("{handle: ");}),_1i=function(_1j,_1k,_1l,_1m,_1n,_1o){var _1p=new T(function(){var _1q=new T(function(){var _1r=new T(function(){var _1s=E(_1m);if(!_1s._){return E(_1o);}else{var _1t=new T(function(){return _Q(_1s,new T(function(){return _Q(_O,_1o);},1));},1);return _Q(_P,_1t);}},1);return _1d(_1k,_1r);}),_1u=E(_1l);if(!_1u._){return E(_1q);}else{return _Q(_1u,new T(function(){return _Q(_N,_1q);},1));}}),_1v=E(_1n);if(!_1v._){var _1w=E(_1j);if(!_1w._){return E(_1p);}else{var _1x=E(_1w.a);if(!_1x._){var _1y=new T(function(){var _1z=new T(function(){return _Q(_1g,new T(function(){return _Q(_N,_1p);},1));},1);return _Q(_1x.a,_1z);},1);return _Q(_1h,_1y);}else{var _1A=new T(function(){var _1B=new T(function(){return _Q(_1g,new T(function(){return _Q(_N,_1p);},1));},1);return _Q(_1x.a,_1B);},1);return _Q(_1h,_1A);}}}else{return _Q(_1v.a,new T(function(){return _Q(_N,_1p);},1));}},_1C=function(_1D){var _1E=E(_1D);return _1i(_1E.a,_1E.b,_1E.c,_1E.d,_1E.f,__Z);},_1F=function(_1G,_1H){var _1I=E(_1G);return _1i(_1I.a,_1I.b,_1I.c,_1I.d,_1I.f,_1H);},_1J=function(_1K,_1L,_1M){var _1N=E(_1L);if(!_1N._){return unAppCStr("[]",_1M);}else{var _1O=new T(function(){var _1P=new T(function(){var _1Q=function(_1R){var _1S=E(_1R);if(!_1S._){return E({_:1,a:93,b:_1M});}else{var _1T=new T(function(){return B(A2(_1K,_1S.a,new T(function(){return _1Q(_1S.b);})));});return {_:1,a:44,b:_1T};}};return _1Q(_1N.b);});return B(A2(_1K,_1N.a,_1P));});return {_:1,a:91,b:_1O};}},_1U=new T(function(){return {_:0,a:_B,b:{_:0,a:function(_1V,_1W,_1X){var _1Y=E(_1W);return _1i(_1Y.a,_1Y.b,_1Y.c,_1Y.d,_1Y.f,_1X);},b:_1C,c:function(_1Z,_20){return _1J(_1F,_1Z,_20);}},c:_21,d:function(_22){var _23=E(_22);return _F(_D(_23.a),_B,_23.b);},e:_1C};}),_21=function(_24){return {_:0,a:_1U,b:_24};},_25=function(_26){return {_:0,a:__Z,b:7,c:__Z,d:_26,e:__Z,f:__Z};},_27=function(_28,_){var _29=new T(function(){return _21(new T(function(){return _25(_28);}));});return die(_29);},_2a={_:0,a:{_:0,a:{_:0,a:{_:0,a:_o,b:function(_2b,_2c,_){var _2d=B(A1(_2c,_));return _2b;}},b:_s,c:_j,d:_u,e:function(_2e,_2f,_){var _2g=B(A1(_2e,_)),_2h=B(A1(_2f,_));return _2g;}},b:function(_2i,_2j,_){var _2k=B(A1(_2i,_));return C > 19 ? new F(function(){return A2(_2j,_2k,_);}) : (++C,A2(_2j,_2k,_));},c:_u,d:_s,e:_27},b:_h},_2l=function(_2m){return E(_2m);},_2n=function(_2o){return E(E(_2o).b);},_2p=function(_2q,_2r){return C > 19 ? new F(function(){return A3(_2n,_2s,_2q,function(_2t){return E(_2r);});}) : (++C,A3(_2n,_2s,_2q,function(_2t){return E(_2r);}));},_2s=new T(function(){return {_:0,a:{_:0,a:{_:0,a:function(_2u){return E(_2u);},b:function(_2v,_2w){return E(_2v);}},b:_2l,c:function(_2x){return E(_2x);},d:function(_2y,_2z){return E(_2z);},e:function(_2A,_2B){return E(_2A);}},b:function(_2C,_2D){return C > 19 ? new F(function(){return A1(_2D,_2C);}) : (++C,A1(_2D,_2C));},c:_2p,d:_2l,e:function(_2E){return err(_2E);}};}),_2F={_:0,a:_2s,b:function(_2G){var _2H=E(_2G);return (_2H._==0)?__Z:{_:1,a:{_:0,a:_2H.a,b:_2H.b}};}},_2I=function(_2J,_2K){switch(E(_2J)._){case 0:switch(E(_2K)._){case 0:return 1;case 1:return 0;case 2:return 0;default:return 0;}break;case 1:switch(E(_2K)._){case 0:return 2;case 1:return 1;case 2:return 0;default:return 0;}break;case 2:switch(E(_2K)._){case 2:return 1;case 3:return 0;default:return 2;}break;default:return (E(_2K)._==3)?1:2;}},_2L=new T(function(){return unCStr("end of input");}),_2M=new T(function(){return unCStr("unexpected");}),_2N=new T(function(){return unCStr("expecting");}),_2O=new T(function(){return unCStr("unknown parse error");}),_2P=new T(function(){return unCStr("or");}),_2Q=new T(function(){return unCStr(")");}),_2R=function(_2S,_2T){var _2U=jsShowI(_2S);return _Q(fromJSStr(_2U),_2T);},_2V=function(_2W,_2X,_2Y){if(_2X>=0){return _2R(_2X,_2Y);}else{if(_2W<=6){return _2R(_2X,_2Y);}else{return {_:1,a:40,b:new T(function(){var _2Z=jsShowI(_2X);return _Q(fromJSStr(_2Z),{_:1,a:41,b:_2Y});})};}}},_30=function(_31,_32,_33){var _34=new T(function(){var _35=new T(function(){var _36=new T(function(){return unAppCStr(", column ",new T(function(){return _Q(_2V(0,_33,__Z),_2Q);}));},1);return _Q(_2V(0,_32,__Z),_36);});return unAppCStr("(line ",_35);}),_37=E(_31);if(!_37._){return E(_34);}else{var _38=new T(function(){return _Q(_37,new T(function(){return unAppCStr("\" ",_34);},1));});return unAppCStr("\"",_38);}},_39=function(_3a,_3b){while(1){var _3c=E(_3a);if(!_3c._){return E(_3b);}else{_3a=_3c.b;_3b=_3c.a;continue;}}},_3d=function(_3e,_3f,_3g){return _39(_3f,_3e);},_3h=function(_3i,_3j,_3k){var _3l=E(_3k);if(!_3l._){return E(_3j);}else{var _3m=new T(function(){return _Q(_3i,new T(function(){return _3h(_3i,_3l.a,_3l.b);},1));},1);return _Q(_3j,_3m);}},_3n=function(_3o,_3p){var _3q=E(_3p);if(!_3q._){return {_:0,a:__Z,b:__Z};}else{var _3r=_3q.a;if(!B(A1(_3o,_3r))){return {_:0,a:__Z,b:_3q};}else{var _3s=new T(function(){var _3t=_3n(_3o,_3q.b);return {_:0,a:_3t.a,b:_3t.b};});return {_:0,a:{_:1,a:_3r,b:new T(function(){return E(E(_3s).a);})},b:new T(function(){return E(E(_3s).b);})};}}},_3u=new T(function(){return unCStr(", ");}),_3v=function(_3w){return (E(_3w)._==0)?false:true;},_3x=function(_3y,_3z){while(1){var _3A=E(_3y);if(!_3A._){return (E(_3z)._==0)?true:false;}else{var _3B=E(_3z);if(!_3B._){return false;}else{if(E(_3A.a)!=E(_3B.a)){return false;}else{_3y=_3A.b;_3z=_3B.b;continue;}}}}},_3C=function(_3D,_3E){while(1){var _3F=(function(_3G,_3H){var _3I=E(_3H);if(!_3I._){return __Z;}else{var _3J=_3I.a,_3K=_3I.b;if(!B(A1(_3G,_3J))){var _3L=_3G;_3D=_3L;_3E=_3K;return __continue;}else{return {_:1,a:_3J,b:new T(function(){return _3C(_3G,_3K);})};}}})(_3D,_3E);if(_3F!=__continue){return _3F;}}},_3M=new T(function(){return unCStr("\n");}),_3N=function(_3O){var _3P=E(_3O);if(!_3P._){return __Z;}else{return _Q(_Q(_3M,_3P.a),new T(function(){return _3N(_3P.b);},1));}},_3Q=function(_3R,_3S){var _3T=E(_3S);return (_3T._==0)?__Z:{_:1,a:_3R,b:new T(function(){return _3Q(_3T.a,_3T.b);})};},_3U=new T(function(){return unCStr(": empty list");}),_3V=new T(function(){return unCStr("Prelude.");}),_3W=function(_3X){return err(_Q(_3V,new T(function(){return _Q(_3X,_3U);},1)));},_3Y=new T(function(){return _3W(new T(function(){return unCStr("last");}));}),_3Z=function(_40){switch(E(_40)._){case 0:return true;case 1:return false;case 2:return false;default:return false;}},_41=function(_42){return (E(_42)._==1)?true:false;},_43=function(_44){return (E(_44)._==2)?true:false;},_45=function(_46,_47){var _48=E(_47);return (_48._==0)?__Z:{_:1,a:new T(function(){return B(A1(_46,_48.a));}),b:new T(function(){return _45(_46,_48.b);})};},_49=function(_4a){var _4b=E(_4a);switch(_4b._){case 0:return E(_4b.a);case 1:return E(_4b.a);case 2:return E(_4b.a);default:return E(_4b.a);}},_4c=function(_4d,_4e,_4f){while(1){var _4g=E(_4f);if(!_4g._){return false;}else{if(!B(A2(_4d,_4g.a,_4e))){_4f=_4g.b;continue;}else{return true;}}}},_4h=function(_4i,_4j){var _4k=function(_4l,_4m){while(1){var _4n=(function(_4o,_4p){var _4q=E(_4o);if(!_4q._){return __Z;}else{var _4r=_4q.a,_4s=_4q.b;if(!_4c(_4i,_4r,_4p)){return {_:1,a:_4r,b:new T(function(){return _4k(_4s,{_:1,a:_4r,b:_4p});})};}else{var _4t=_4p;_4l=_4s;_4m=_4t;return __continue;}}})(_4l,_4m);if(_4n!=__continue){return _4n;}}};return _4k(_4j,__Z);},_4u=function(_4v,_4w,_4x,_4y,_4z,_4A){var _4B=E(_4A);if(!_4B._){return E(_4w);}else{var _4C=new T(function(){var _4D=_3n(_3Z,_4B);return {_:0,a:_4D.a,b:_4D.b};}),_4E=new T(function(){var _4F=_3n(_41,E(_4C).b);return {_:0,a:_4F.a,b:_4F.b};}),_4G=new T(function(){return E(E(_4E).a);}),_4H=function(_4I,_4J){var _4K=E(_4J);if(!_4K._){return E(_4I);}else{var _4L=new T(function(){var _4M=new T(function(){var _4N=new T(function(){return unAppCStr(" ",new T(function(){return _3d(_4I,_4K,_3Y);}));},1);return _Q(_4v,_4N);});return unAppCStr(" ",_4M);}),_4O=_4h(_3x,_3C(_3v,_3Q(_4I,_4K)));if(!_4O._){return _Q(__Z,_4L);}else{var _4P=_4O.a,_4Q=E(_4O.b);if(!_4Q._){return _Q(_4P,_4L);}else{var _4R=new T(function(){return _Q(_3u,new T(function(){return _3h(_3u,_4Q.a,_4Q.b);},1));},1);return _Q(_Q(_4P,_4R),_4L);}}}},_4S=function(_4T,_4U){var _4V=_4h(_3x,_3C(_3v,_45(_49,_4U)));if(!_4V._){return __Z;}else{var _4W=_4V.a,_4X=_4V.b,_4Y=E(_4T);if(!_4Y._){return _4H(_4W,_4X);}else{var _4Z=new T(function(){return unAppCStr(" ",new T(function(){return _4H(_4W,_4X);}));},1);return _Q(_4Y,_4Z);}}},_50=new T(function(){var _51=_3n(_43,E(_4E).b);return {_:0,a:_51.a,b:_51.b};}),_52=new T(function(){if(!E(_4G)._){var _53=E(E(_4C).a);if(!_53._){return __Z;}else{var _54=E(_53.a);switch(_54._){case 0:var _55=E(_54.a);if(!_55._){return _Q(_4y,new T(function(){return unAppCStr(" ",_4z);},1));}else{return _Q(_4y,new T(function(){return unAppCStr(" ",_55);},1));}break;case 1:var _56=E(_54.a);if(!_56._){return _Q(_4y,new T(function(){return unAppCStr(" ",_4z);},1));}else{return _Q(_4y,new T(function(){return unAppCStr(" ",_56);},1));}break;case 2:var _57=E(_54.a);if(!_57._){return _Q(_4y,new T(function(){return unAppCStr(" ",_4z);},1));}else{return _Q(_4y,new T(function(){return unAppCStr(" ",_57);},1));}break;default:var _58=E(_54.a);if(!_58._){return _Q(_4y,new T(function(){return unAppCStr(" ",_4z);},1));}else{return _Q(_4y,new T(function(){return unAppCStr(" ",_58);},1));}}}}else{return __Z;}});return _3N(_4h(_3x,_3C(_3v,{_:1,a:_52,b:{_:1,a:new T(function(){return _4S(_4y,_4G);}),b:{_:1,a:new T(function(){return _4S(_4x,E(_50).a);}),b:{_:1,a:new T(function(){var _59=E(_50).b,_5a=_4h(_3x,_3C(_3v,_45(_49,_59)));if(!_5a._){return __Z;}else{return _4H(_5a.a,_5a.b);}}),b:__Z}}}})));}},_5b=function(_5c,_5d){var _5e=function(_5f,_5g){var _5h=E(_5f);if(!_5h._){return E(_5g);}else{var _5i=_5h.a,_5j=E(_5g);if(!_5j._){return _5h;}else{var _5k=_5j.a;return (B(A2(_5c,_5i,_5k))==2)?{_:1,a:_5k,b:new T(function(){return _5e(_5h,_5j.b);})}:{_:1,a:_5i,b:new T(function(){return _5e(_5h.b,_5j);})};}}},_5l=function(_5m){var _5n=E(_5m);if(!_5n._){return __Z;}else{var _5o=E(_5n.b);return (_5o._==0)?_5n:{_:1,a:new T(function(){return _5e(_5n.a,_5o.a);}),b:new T(function(){return _5l(_5o.b);})};}},_5p=new T(function(){return _5q(_5l(__Z));}),_5q=function(_5r){while(1){var _5s=E(_5r);if(!_5s._){return E(_5p);}else{if(!E(_5s.b)._){return E(_5s.a);}else{_5r=_5l(_5s);continue;}}}},_5t=new T(function(){return _5u(__Z);}),_5v=function(_5w,_5x,_5y){while(1){var _5z=(function(_5A,_5B,_5C){var _5D=E(_5C);if(!_5D._){return {_:1,a:{_:1,a:_5A,b:_5B},b:_5t};}else{var _5E=_5D.a;if(B(A2(_5c,_5A,_5E))==2){var _5F={_:1,a:_5A,b:_5B};_5w=_5E;_5x=_5F;_5y=_5D.b;return __continue;}else{return {_:1,a:{_:1,a:_5A,b:_5B},b:new T(function(){return _5u(_5D);})};}}})(_5w,_5x,_5y);if(_5z!=__continue){return _5z;}}},_5G=function(_5H,_5I,_5J){while(1){var _5K=(function(_5L,_5M,_5N){var _5O=E(_5N);if(!_5O._){return {_:1,a:new T(function(){return B(A1(_5M,{_:1,a:_5L,b:__Z}));}),b:_5t};}else{var _5P=_5O.a,_5Q=_5O.b;switch(B(A2(_5c,_5L,_5P))){case 0:_5H=_5P;_5I=function(_5R){return C > 19 ? new F(function(){return A1(_5M,{_:1,a:_5L,b:_5R});}) : (++C,A1(_5M,{_:1,a:_5L,b:_5R}));};_5J=_5Q;return __continue;case 1:_5H=_5P;_5I=function(_5S){return C > 19 ? new F(function(){return A1(_5M,{_:1,a:_5L,b:_5S});}) : (++C,A1(_5M,{_:1,a:_5L,b:_5S}));};_5J=_5Q;return __continue;default:return {_:1,a:new T(function(){return B(A1(_5M,{_:1,a:_5L,b:__Z}));}),b:new T(function(){return _5u(_5O);})};}}})(_5H,_5I,_5J);if(_5K!=__continue){return _5K;}}},_5u=function(_5T){var _5U=E(_5T);if(!_5U._){return E({_:1,a:__Z,b:__Z});}else{var _5V=_5U.a,_5W=E(_5U.b);if(!_5W._){return {_:1,a:_5U,b:__Z};}else{var _5X=_5W.a,_5Y=_5W.b;if(B(A2(_5c,_5V,_5X))==2){return _5v(_5X,{_:1,a:_5V,b:__Z},_5Y);}else{return _5G(_5X,function(_5Z){return {_:1,a:_5V,b:_5Z};},_5Y);}}}};return _5q(_5u(_5d));},_60=function(_61,_62,_63,_64){var _65=new T(function(){return unAppCStr(":",new T(function(){return _4u(_2P,_2O,_2N,_2M,_2L,_5b(_2I,_64));}));},1);return _Q(_30(_61,_62,_63),_65);},_66=(function(id){return document.getElementById(id);}),_67=function(_68){var _69=B(A1(_68,_));return E(_69);},_6a=new T(function(){return _67(function(_){return __jsNull();});}),_6b=function(_6c){return E(E(_6c).b);},_6d=function(_6e,_6f){return C > 19 ? new F(function(){return A2(_6b,_6e,function(_){var _6g=_66(E(_6f)),_6h=__eq(_6g,E(_6a));return (E(_6h)==0)?{_:1,a:_6g}:__Z;});}) : (++C,A2(_6b,_6e,function(_){var _6g=_66(E(_6f)),_6h=__eq(_6g,E(_6a));return (E(_6h)==0)?{_:1,a:_6g}:__Z;}));},_6i=function(_6j,_6k){while(1){var _6l=E(_6j);if(!_6l._){return (E(_6k)._==0)?1:0;}else{var _6m=E(_6k);if(!_6m._){return 2;}else{var _6n=E(_6l.a),_6o=E(_6m.a);if(_6n!=_6o){return (_6n>_6o)?2:0;}else{_6j=_6l.b;_6k=_6m.b;continue;}}}}},_6p=new T(function(){return _Q(__Z,__Z);}),_6q=function(_6r,_6s,_6t,_6u,_6v,_6w,_6x,_6y){var _6z={_:0,a:_6r,b:_6s,c:_6t},_6A=function(_6B){var _6C=E(_6u);if(!_6C._){var _6D=E(_6y);if(!_6D._){switch(_6i(_6r,_6v)){case 0:return {_:0,a:{_:0,a:_6v,b:_6w,c:_6x},b:__Z};case 1:return (_6s>=_6w)?(_6s!=_6w)?{_:0,a:_6z,b:__Z}:(_6t>=_6x)?(_6t!=_6x)?{_:0,a:_6z,b:__Z}:{_:0,a:_6z,b:_6p}:{_:0,a:{_:0,a:_6v,b:_6w,c:_6x},b:__Z}:{_:0,a:{_:0,a:_6v,b:_6w,c:_6x},b:__Z};default:return {_:0,a:_6z,b:__Z};}}else{return {_:0,a:{_:0,a:_6v,b:_6w,c:_6x},b:_6D};}}else{switch(_6i(_6r,_6v)){case 0:return {_:0,a:{_:0,a:_6v,b:_6w,c:_6x},b:_6y};case 1:return (_6s>=_6w)?(_6s!=_6w)?{_:0,a:_6z,b:_6C}:(_6t>=_6x)?(_6t!=_6x)?{_:0,a:_6z,b:_6C}:{_:0,a:_6z,b:new T(function(){return _Q(_6C,_6y);})}:{_:0,a:{_:0,a:_6v,b:_6w,c:_6x},b:_6y}:{_:0,a:{_:0,a:_6v,b:_6w,c:_6x},b:_6y};default:return {_:0,a:_6z,b:_6C};}}};if(!E(_6y)._){var _6E=E(_6u);if(!_6E._){return _6A(_);}else{return {_:0,a:_6z,b:_6E};}}else{return _6A(_);}},_6F=function(_6G,_6H){while(1){var _6I=E(_6G);if(!_6I._){return E(_6H);}else{var _6J={_:1,a:_6I.a,b:_6H};_6G=_6I.b;_6H=_6J;continue;}}},_6K=new T(function(){return _6F(__Z,__Z);}),_6L=new T(function(){return err(new T(function(){return unCStr("Text.ParserCombinators.Parsec.Prim.many: combinator \'many\' is applied to a parser that accepts an empty string.");}));}),_6M=function(_6N,_6O,_6P,_6Q,_6R){var _6S=function(_6T){return C > 19 ? new F(function(){return A3(_6R,_6K,_6O,new T(function(){var _6U=E(E(_6O).b),_6V=E(_6T),_6W=E(_6V.a),_6X=_6q(_6W.a,_6W.b,_6W.c,_6V.b,_6U.a,_6U.b,_6U.c,__Z);return {_:0,a:E(_6X.a),b:_6X.b};}));}) : (++C,A3(_6R,_6K,_6O,new T(function(){var _6U=E(E(_6O).b),_6V=E(_6T),_6W=E(_6V.a),_6X=_6q(_6W.a,_6W.b,_6W.c,_6V.b,_6U.a,_6U.b,_6U.c,__Z);return {_:0,a:E(_6X.a),b:_6X.b};})));},_6Y=function(_6Z,_70,_71){var _72={_:1,a:_70,b:_6Z},_73=new T(function(){return _6F(_72,__Z);}),_74=function(_75){return C > 19 ? new F(function(){return A3(_6P,_73,_71,new T(function(){var _76=E(E(_71).b),_77=E(_75),_78=E(_77.a),_79=_6q(_78.a,_78.b,_78.c,_77.b,_76.a,_76.b,_76.c,__Z);return {_:0,a:E(_79.a),b:_79.b};}));}) : (++C,A3(_6P,_73,_71,new T(function(){var _76=E(E(_71).b),_77=E(_75),_78=E(_77.a),_79=_6q(_78.a,_78.b,_78.c,_77.b,_76.a,_76.b,_76.c,__Z);return {_:0,a:E(_79.a),b:_79.b};})));},_7a=new T(function(){var _7b=E(_6Z);return function(_7c,_7d,_7e){return C > 19 ? new F(function(){return _6Y(_72,_7c,_7d);}) : (++C,_6Y(_72,_7c,_7d));};});return C > 19 ? new F(function(){return A(_6N,[_71,_7a,_6Q,_6L,_74]);}) : (++C,A(_6N,[_71,_7a,_6Q,_6L,_74]));};return C > 19 ? new F(function(){return A(_6N,[_6O,function(_7f,_7g,_7h){return C > 19 ? new F(function(){return _6Y(__Z,_7f,_7g);}) : (++C,_6Y(__Z,_7f,_7g));},_6Q,_6L,_6S]);}) : (++C,A(_6N,[_6O,function(_7f,_7g,_7h){return C > 19 ? new F(function(){return _6Y(__Z,_7f,_7g);}) : (++C,_6Y(__Z,_7f,_7g));},_6Q,_6L,_6S]));},_7i=function(_7j,_7k){var _7l=E(_7j),_7m=E(_7l.a),_7n=E(_7k),_7o=E(_7n.a),_7p=_6q(_7m.a,_7m.b,_7m.c,_7l.b,_7o.a,_7o.b,_7o.c,_7n.b);return {_:0,a:E(_7p.a),b:_7p.b};},_7q=function(_7r,_7s,_7t,_7u,_7v,_7w,_7x){var _7y=function(_7z,_7A,_7B,_7C,_7D,_7E){var _7F=function(_7G,_7H,_7I){return C > 19 ? new F(function(){return A3(_7D,new T(function(){return B(A1(_7z,_7G));}),_7H,new T(function(){var _7J=E(E(_7H).b),_7K=E(_7I),_7L=E(_7K.a),_7M=_6q(_7L.a,_7L.b,_7L.c,_7K.b,_7J.a,_7J.b,_7J.c,__Z);return {_:0,a:E(_7M.a),b:_7M.b};}));}) : (++C,A3(_7D,new T(function(){return B(A1(_7z,_7G));}),_7H,new T(function(){var _7J=E(E(_7H).b),_7K=E(_7I),_7L=E(_7K.a),_7M=_6q(_7L.a,_7L.b,_7L.c,_7K.b,_7J.a,_7J.b,_7J.c,__Z);return {_:0,a:E(_7M.a),b:_7M.b};})));},_7N=function(_7O,_7P,_7Q){return C > 19 ? new F(function(){return A3(_7B,new T(function(){return B(A1(_7z,_7O));}),_7P,new T(function(){var _7R=E(E(_7P).b),_7S=E(_7Q),_7T=E(_7S.a),_7U=_6q(_7T.a,_7T.b,_7T.c,_7S.b,_7R.a,_7R.b,_7R.c,__Z);return {_:0,a:E(_7U.a),b:_7U.b};}));}) : (++C,A3(_7B,new T(function(){return B(A1(_7z,_7O));}),_7P,new T(function(){var _7R=E(E(_7P).b),_7S=E(_7Q),_7T=E(_7S.a),_7U=_6q(_7T.a,_7T.b,_7T.c,_7S.b,_7R.a,_7R.b,_7R.c,__Z);return {_:0,a:E(_7U.a),b:_7U.b};})));};return C > 19 ? new F(function(){return A(_7s,[_7A,_7N,_7C,_7F,_7E]);}) : (++C,A(_7s,[_7A,_7N,_7C,_7F,_7E]));},_7V=function(_7W,_7X,_7Y){var _7Z=function(_80){return C > 19 ? new F(function(){return A1(_7x,new T(function(){return _7i(_7Y,_80);}));}) : (++C,A1(_7x,new T(function(){return _7i(_7Y,_80);})));},_81=function(_82,_83,_84){return C > 19 ? new F(function(){return A3(_7w,_82,_83,new T(function(){return _7i(_7Y,_84);}));}) : (++C,A3(_7w,_82,_83,new T(function(){return _7i(_7Y,_84);})));};return C > 19 ? new F(function(){return _7y(_7W,_7X,_7u,_7v,_81,_7Z);}) : (++C,_7y(_7W,_7X,_7u,_7v,_81,_7Z));},_85=function(_86,_87,_88){var _89=function(_8a){return C > 19 ? new F(function(){return A1(_7v,new T(function(){return _7i(_88,_8a);}));}) : (++C,A1(_7v,new T(function(){return _7i(_88,_8a);})));},_8b=function(_8c,_8d,_8e){return C > 19 ? new F(function(){return A3(_7u,_8c,_8d,new T(function(){return _7i(_88,_8e);}));}) : (++C,A3(_7u,_8c,_8d,new T(function(){return _7i(_88,_8e);})));};return C > 19 ? new F(function(){return _7y(_86,_87,_7u,_7v,_8b,_89);}) : (++C,_7y(_86,_87,_7u,_7v,_8b,_89));};return C > 19 ? new F(function(){return A(_7r,[_7t,_85,_7v,_7V,_7x]);}) : (++C,A(_7r,[_7t,_85,_7v,_7V,_7x]));},_8f=function(_8g,_8h){while(1){var _8i=E(_8g);if(!_8i._){return E(_8h);}else{var _8j=B(A1(_8i.a,_8h));_8g=_8i.b;_8h=_8j;continue;}}},_8k=function(_8l,_8m){while(1){var _8n=E(_8l);if(!_8n._){return E(_8m);}else{var _8o=B(A1(_8n.a,_8m));_8l=_8n.b;_8m=_8o;continue;}}},_8p=new T(function(){var _8q=hs_wordToWord64(I_fromBits([18445595,3739165398])),_8r=hs_wordToWord64(I_fromBits([52003073,3246954884]));return {_:0,a:_8q,b:_8r,c:{_:0,a:_8q,b:_8r,c:new T(function(){return unCStr("base");}),d:new T(function(){return unCStr("Control.Exception.Base");}),e:new T(function(){return unCStr("PatternMatchFail");})},d:__Z,e:__Z};}),_8s=function(_8t){return E(_8p);},_8u=function(_8v){return E(E(_8v).a);},_8w=function(_8x,_8y){return _Q(E(_8x).a,_8y);},_8z=new T(function(){return {_:0,a:_8s,b:{_:0,a:function(_8A,_8B,_8C){return _Q(E(_8B).a,_8C);},b:_8u,c:function(_8D,_8E){return _1J(_8w,_8D,_8E);}},c:function(_8F){return {_:0,a:_8z,b:_8F};},d:function(_8G){var _8H=E(_8G);return _F(_D(_8H.a),_8s,_8H.b);},e:_8u};}),_8I=new T(function(){return unCStr("Non-exhaustive patterns in");}),_8J=function(_8K){return E(E(_8K).c);},_8L=function(_8M,_8N){return die(new T(function(){return B(A2(_8J,_8N,_8M));}));},_8O=function(_8P,_8Q){return _8L(_8P,_8Q);},_8R=new T(function(){return unCStr("\n");}),_8S=function(_8T){return (E(_8T)==124)?false:true;},_8U=function(_8V,_8W){var _8X=_3n(_8S,unCStr(_8V)),_8Y=_8X.a,_8Z=function(_90,_91){var _92=new T(function(){var _93=new T(function(){return _Q(_8W,new T(function(){return _Q(_91,_8R);},1));});return unAppCStr(": ",_93);},1);return _Q(_90,_92);},_94=E(_8X.b);if(!_94._){return _8Z(_8Y,__Z);}else{if(E(_94.a)==124){return _8Z(_8Y,{_:1,a:32,b:_94.b});}else{return _8Z(_8Y,__Z);}}},_95=function(_96){return _8O({_:0,a:new T(function(){return _8U(_96,_8I);})},_8z);},_97=new T(function(){return B(_95("Text/ParserCombinators/ReadP.hs:(128,3)-(151,52)|function <|>"));}),_98=function(_99,_9a){while(1){var _9b=(function(_9c,_9d){var _9e=E(_9c);switch(_9e._){case 0:var _9f=E(_9d);if(!_9f._){return __Z;}else{_99=B(A1(_9e.a,_9f.a));_9a=_9f.b;return __continue;}break;case 1:var _9g=B(A1(_9e.a,_9d)),_9h=_9d;_99=_9g;_9a=_9h;return __continue;case 2:return __Z;case 3:return {_:1,a:{_:0,a:_9e.a,b:_9d},b:new T(function(){return _98(_9e.b,_9d);})};default:return E(_9e.a);}})(_99,_9a);if(_9b!=__continue){return _9b;}}},_9i=function(_9j,_9k){var _9l=function(_9m){var _9n=E(_9k);if(_9n._==3){return {_:3,a:_9n.a,b:new T(function(){return _9i(_9j,_9n.b);})};}else{var _9o=E(_9j);if(_9o._==2){return _9n;}else{if(_9n._==2){return _9o;}else{var _9p=function(_9q){if(_9n._==4){var _9r=function(_9s){return {_:4,a:new T(function(){return _Q(_98(_9o,_9s),_9n.a);})};};return {_:1,a:_9r};}else{if(_9o._==1){var _9t=_9o.a;if(!_9n._){return {_:1,a:function(_9u){return _9i(B(A1(_9t,_9u)),_9n);}};}else{var _9v=function(_9w){return _9i(B(A1(_9t,_9w)),new T(function(){return B(A1(_9n.a,_9w));}));};return {_:1,a:_9v};}}else{if(!_9n._){return E(_97);}else{var _9x=function(_9y){return _9i(_9o,new T(function(){return B(A1(_9n.a,_9y));}));};return {_:1,a:_9x};}}}};switch(_9o._){case 1:if(_9n._==4){var _9z=function(_9A){return {_:4,a:new T(function(){return _Q(_98(B(A1(_9o.a,_9A)),_9A),_9n.a);})};};return {_:1,a:_9z};}else{return _9p(_);}break;case 4:var _9B=_9o.a;switch(_9n._){case 0:var _9C=function(_9D){var _9E=new T(function(){return _Q(_9B,new T(function(){return _98(_9n,_9D);},1));});return {_:4,a:_9E};};return {_:1,a:_9C};case 1:var _9F=function(_9G){var _9H=new T(function(){return _Q(_9B,new T(function(){return _98(B(A1(_9n.a,_9G)),_9G);},1));});return {_:4,a:_9H};};return {_:1,a:_9F};default:return {_:4,a:new T(function(){return _Q(_9B,_9n.a);})};}break;default:return _9p(_);}}}}},_9I=E(_9j);switch(_9I._){case 0:var _9J=E(_9k);if(!_9J._){var _9K=function(_9L){return _9i(B(A1(_9I.a,_9L)),new T(function(){return B(A1(_9J.a,_9L));}));};return {_:0,a:_9K};}else{return _9l(_);}break;case 3:return {_:3,a:_9I.a,b:new T(function(){return _9i(_9I.b,_9k);})};default:return _9l(_);}},_9M=new T(function(){return unCStr("(");}),_9N=new T(function(){return unCStr(")");}),_9O=function(_9P,_9Q){return E(_9P)==E(_9Q);},_9R={_:0,a:_9O,b:function(_9S,_9T){return E(_9S)!=E(_9T);}},_9U=function(_9V,_9W){while(1){var _9X=E(_9V);if(!_9X._){return (E(_9W)._==0)?true:false;}else{var _9Y=E(_9W);if(!_9Y._){return false;}else{if(E(_9X.a)!=E(_9Y.a)){return false;}else{_9V=_9X.b;_9W=_9Y.b;continue;}}}}},_9Z=function(_a0,_a1){return (!_9U(_a0,_a1))?true:false;},_a2=function(_a3,_a4){var _a5=E(_a3);switch(_a5._){case 0:return {_:0,a:function(_a6){return C > 19 ? new F(function(){return _a2(B(A1(_a5.a,_a6)),_a4);}) : (++C,_a2(B(A1(_a5.a,_a6)),_a4));}};case 1:return {_:1,a:function(_a7){return C > 19 ? new F(function(){return _a2(B(A1(_a5.a,_a7)),_a4);}) : (++C,_a2(B(A1(_a5.a,_a7)),_a4));}};case 2:return {_:2};case 3:return _9i(B(A1(_a4,_a5.a)),new T(function(){return B(_a2(_a5.b,_a4));}));default:var _a8=function(_a9){var _aa=E(_a9);if(!_aa._){return __Z;}else{var _ab=E(_aa.a);return _Q(_98(B(A1(_a4,_ab.a)),_ab.b),new T(function(){return _a8(_aa.b);},1));}},_ac=_a8(_a5.a);return (_ac._==0)?{_:2}:{_:4,a:_ac};}},_ad={_:2},_ae=function(_af){return {_:3,a:_af,b:_ad};},_ag=function(_ah,_ai){var _aj=E(_ah);if(!_aj){return C > 19 ? new F(function(){return A1(_ai,0);}) : (++C,A1(_ai,0));}else{var _ak=new T(function(){return B(_ag(_aj-1|0,_ai));});return {_:0,a:function(_al){return E(_ak);}};}},_am=function(_an,_ao,_ap){var _aq=new T(function(){return B(A1(_an,_ae));}),_ar=function(_as,_at,_au,_av){while(1){var _aw=B((function(_ax,_ay,_az,_aA){var _aB=E(_ax);switch(_aB._){case 0:var _aC=E(_ay);if(!_aC._){return C > 19 ? new F(function(){return A1(_ao,_aA);}) : (++C,A1(_ao,_aA));}else{var _aD=_az+1|0,_aE=_aA;_as=B(A1(_aB.a,_aC.a));_at=_aC.b;_au=_aD;_av=_aE;return __continue;}break;case 1:var _aF=B(A1(_aB.a,_ay)),_aG=_ay,_aD=_az,_aE=_aA;_as=_aF;_at=_aG;_au=_aD;_av=_aE;return __continue;case 2:return C > 19 ? new F(function(){return A1(_ao,_aA);}) : (++C,A1(_ao,_aA));break;case 3:var _aH=new T(function(){return B(_a2(_aB,_aA));});return C > 19 ? new F(function(){return _ag(_az,function(_aI){return E(_aH);});}) : (++C,_ag(_az,function(_aI){return E(_aH);}));break;default:return C > 19 ? new F(function(){return _a2(_aB,_aA);}) : (++C,_a2(_aB,_aA));}})(_as,_at,_au,_av));if(_aw!=__continue){return _aw;}}};return function(_aJ){return _ar(_aq,_aJ,0,_ap);};},_aK=function(_aL){return C > 19 ? new F(function(){return A1(_aL,__Z);}) : (++C,A1(_aL,__Z));},_aM=function(_aN,_aO){var _aP=function(_aQ){var _aR=E(_aQ);if(!_aR._){return _aK;}else{var _aS=_aR.a;if(!B(A1(_aN,_aS))){return _aK;}else{var _aT=new T(function(){return _aP(_aR.b);}),_aU=function(_aV){var _aW=new T(function(){return B(A1(_aT,function(_aX){return C > 19 ? new F(function(){return A1(_aV,{_:1,a:_aS,b:_aX});}) : (++C,A1(_aV,{_:1,a:_aS,b:_aX}));}));});return {_:0,a:function(_aY){return E(_aW);}};};return _aU;}}};return function(_aZ){return C > 19 ? new F(function(){return A2(_aP,_aZ,_aO);}) : (++C,A2(_aP,_aZ,_aO));};},_b0=new T(function(){return err(new T(function(){return unCStr("valDig: Bad base");}));}),_b1=function(_b2,_b3){var _b4=function(_b5,_b6){var _b7=E(_b5);if(!_b7._){var _b8=new T(function(){return B(A1(_b6,__Z));});return function(_b9){return C > 19 ? new F(function(){return A1(_b9,_b8);}) : (++C,A1(_b9,_b8));};}else{var _ba=E(_b7.a),_bb=function(_bc){var _bd=new T(function(){return _b4(_b7.b,function(_be){return C > 19 ? new F(function(){return A1(_b6,{_:1,a:_bc,b:_be});}) : (++C,A1(_b6,{_:1,a:_bc,b:_be}));});}),_bf=function(_bg){var _bh=new T(function(){return B(A1(_bd,_bg));});return {_:0,a:function(_bi){return E(_bh);}};};return _bf;};switch(E(_b2)){case 8:if(48>_ba){var _bj=new T(function(){return B(A1(_b6,__Z));});return function(_bk){return C > 19 ? new F(function(){return A1(_bk,_bj);}) : (++C,A1(_bk,_bj));};}else{if(_ba>55){var _bl=new T(function(){return B(A1(_b6,__Z));});return function(_bm){return C > 19 ? new F(function(){return A1(_bm,_bl);}) : (++C,A1(_bm,_bl));};}else{return _bb(_ba-48|0);}}break;case 10:if(48>_ba){var _bn=new T(function(){return B(A1(_b6,__Z));});return function(_bo){return C > 19 ? new F(function(){return A1(_bo,_bn);}) : (++C,A1(_bo,_bn));};}else{if(_ba>57){var _bp=new T(function(){return B(A1(_b6,__Z));});return function(_bq){return C > 19 ? new F(function(){return A1(_bq,_bp);}) : (++C,A1(_bq,_bp));};}else{return _bb(_ba-48|0);}}break;case 16:if(48>_ba){if(97>_ba){if(65>_ba){var _br=new T(function(){return B(A1(_b6,__Z));});return function(_bs){return C > 19 ? new F(function(){return A1(_bs,_br);}) : (++C,A1(_bs,_br));};}else{if(_ba>70){var _bt=new T(function(){return B(A1(_b6,__Z));});return function(_bu){return C > 19 ? new F(function(){return A1(_bu,_bt);}) : (++C,A1(_bu,_bt));};}else{return _bb((_ba-65|0)+10|0);}}}else{if(_ba>102){if(65>_ba){var _bv=new T(function(){return B(A1(_b6,__Z));});return function(_bw){return C > 19 ? new F(function(){return A1(_bw,_bv);}) : (++C,A1(_bw,_bv));};}else{if(_ba>70){var _bx=new T(function(){return B(A1(_b6,__Z));});return function(_by){return C > 19 ? new F(function(){return A1(_by,_bx);}) : (++C,A1(_by,_bx));};}else{return _bb((_ba-65|0)+10|0);}}}else{return _bb((_ba-97|0)+10|0);}}}else{if(_ba>57){if(97>_ba){if(65>_ba){var _bz=new T(function(){return B(A1(_b6,__Z));});return function(_bA){return C > 19 ? new F(function(){return A1(_bA,_bz);}) : (++C,A1(_bA,_bz));};}else{if(_ba>70){var _bB=new T(function(){return B(A1(_b6,__Z));});return function(_bC){return C > 19 ? new F(function(){return A1(_bC,_bB);}) : (++C,A1(_bC,_bB));};}else{return _bb((_ba-65|0)+10|0);}}}else{if(_ba>102){if(65>_ba){var _bD=new T(function(){return B(A1(_b6,__Z));});return function(_bE){return C > 19 ? new F(function(){return A1(_bE,_bD);}) : (++C,A1(_bE,_bD));};}else{if(_ba>70){var _bF=new T(function(){return B(A1(_b6,__Z));});return function(_bG){return C > 19 ? new F(function(){return A1(_bG,_bF);}) : (++C,A1(_bG,_bF));};}else{return _bb((_ba-65|0)+10|0);}}}else{return _bb((_ba-97|0)+10|0);}}}else{return _bb(_ba-48|0);}}break;default:return E(_b0);}}},_bH=function(_bI){var _bJ=E(_bI);if(!_bJ._){return {_:2};}else{return C > 19 ? new F(function(){return A1(_b3,_bJ);}) : (++C,A1(_b3,_bJ));}};return function(_bK){return C > 19 ? new F(function(){return A3(_b4,_bK,_h,_bH);}) : (++C,A3(_b4,_bK,_h,_bH));};},_bL=function(_bM){var _bN=function(_bO){return C > 19 ? new F(function(){return A1(_bM,{_:5,a:{_:0,a:8,b:_bO}});}) : (++C,A1(_bM,{_:5,a:{_:0,a:8,b:_bO}}));},_bP=function(_bQ){return C > 19 ? new F(function(){return A1(_bM,{_:5,a:{_:0,a:16,b:_bQ}});}) : (++C,A1(_bM,{_:5,a:{_:0,a:16,b:_bQ}}));},_bR=function(_bS){switch(E(_bS)){case 79:return {_:1,a:_b1(8,_bN)};case 88:return {_:1,a:_b1(16,_bP)};case 111:return {_:1,a:_b1(8,_bN)};case 120:return {_:1,a:_b1(16,_bP)};default:return {_:2};}};return function(_bT){return (E(_bT)==48)?E({_:0,a:_bR}):{_:2};};},_bU=function(_bV){return {_:0,a:_bL(_bV)};},_bW=function(_bX){return C > 19 ? new F(function(){return A1(_bX,__Z);}) : (++C,A1(_bX,__Z));},_bY=function(_bZ){return C > 19 ? new F(function(){return A1(_bZ,__Z);}) : (++C,A1(_bZ,__Z));},_c0={_:0,a:1},_c1=function(_c2,_c3){while(1){var _c4=E(_c2);if(!_c4._){var _c5=_c4.a,_c6=E(_c3);if(!_c6._){var _c7=_c6.a,_c8=addC(_c5,_c7);if(!E(_c8.b)){return {_:0,a:_c8.a};}else{_c2={_:1,a:I_fromInt(_c5)};_c3={_:1,a:I_fromInt(_c7)};continue;}}else{_c2={_:1,a:I_fromInt(_c5)};_c3=_c6;continue;}}else{var _c9=E(_c3);if(!_c9._){_c2=_c4;_c3={_:1,a:I_fromInt(_c9.a)};continue;}else{return {_:1,a:I_add(_c4.a,_c9.a)};}}}},_ca=new T(function(){return _c1({_:0,a:2147483647},_c0);}),_cb=function(_cc){var _cd=E(_cc);if(!_cd._){var _ce=E(_cd.a);return (_ce==(-2147483648))?E(_ca):{_:0,a: -_ce};}else{return {_:1,a:I_negate(_cd.a)};}},_cf={_:0,a:10},_cg=function(_ch,_ci){while(1){var _cj=E(_ch);if(!_cj._){return E(_ci);}else{var _ck=_ci+1|0;_ch=_cj.b;_ci=_ck;continue;}}},_cl=function(_cm){return {_:0,a:_cm};},_cn=function(_co){return _cl(E(_co));},_cp=new T(function(){return err(new T(function(){return unCStr("this should not happen");}));}),_cq=function(_cr,_cs){while(1){var _ct=E(_cr);if(!_ct._){var _cu=_ct.a,_cv=E(_cs);if(!_cv._){var _cw=_cv.a;if(!(imul(_cu,_cw)|0)){return {_:0,a:imul(_cu,_cw)|0};}else{_cr={_:1,a:I_fromInt(_cu)};_cs={_:1,a:I_fromInt(_cw)};continue;}}else{_cr={_:1,a:I_fromInt(_cu)};_cs=_cv;continue;}}else{var _cx=E(_cs);if(!_cx._){_cr=_ct;_cs={_:1,a:I_fromInt(_cx.a)};continue;}else{return {_:1,a:I_mul(_ct.a,_cx.a)};}}}},_cy=function(_cz,_cA){var _cB=E(_cA);if(!_cB._){return __Z;}else{var _cC=E(_cB.b);return (_cC._==0)?E(_cp):{_:1,a:_c1(_cq(_cB.a,_cz),_cC.a),b:new T(function(){return _cy(_cz,_cC.b);})};}},_cD={_:0,a:0},_cE=function(_cF,_cG,_cH){while(1){var _cI=(function(_cJ,_cK,_cL){var _cM=E(_cL);if(!_cM._){return E(_cD);}else{if(!E(_cM.b)._){return E(_cM.a);}else{var _cN=E(_cK);if(_cN<=40){var _cO=_cD,_cP=_cM;while(1){var _cQ=E(_cP);if(!_cQ._){return E(_cO);}else{var _cR=_c1(_cq(_cO,_cJ),_cQ.a);_cO=_cR;_cP=_cQ.b;continue;}}}else{var _cS=_cq(_cJ,_cJ);if(!(_cN%2)){var _cT=_cy(_cJ,_cM);_cF=_cS;_cG=quot(_cN+1|0,2);_cH=_cT;return __continue;}else{var _cT=_cy(_cJ,{_:1,a:_cD,b:_cM});_cF=_cS;_cG=quot(_cN+1|0,2);_cH=_cT;return __continue;}}}}})(_cF,_cG,_cH);if(_cI!=__continue){return _cI;}}},_cU=function(_cV,_cW){return _cE(_cV,new T(function(){return _cg(_cW,0);},1),_45(_cn,_cW));},_cX=function(_cY){var _cZ=new T(function(){var _d0=new T(function(){var _d1=function(_d2){return C > 19 ? new F(function(){return A1(_cY,{_:1,a:new T(function(){return _cU(_cf,_d2);})});}) : (++C,A1(_cY,{_:1,a:new T(function(){return _cU(_cf,_d2);})}));};return {_:1,a:_b1(10,_d1)};}),_d3=function(_d4){if(E(_d4)==43){var _d5=function(_d6){return C > 19 ? new F(function(){return A1(_cY,{_:1,a:new T(function(){return _cU(_cf,_d6);})});}) : (++C,A1(_cY,{_:1,a:new T(function(){return _cU(_cf,_d6);})}));};return {_:1,a:_b1(10,_d5)};}else{return {_:2};}},_d7=function(_d8){if(E(_d8)==45){var _d9=function(_da){return C > 19 ? new F(function(){return A1(_cY,{_:1,a:new T(function(){return _cb(_cU(_cf,_da));})});}) : (++C,A1(_cY,{_:1,a:new T(function(){return _cb(_cU(_cf,_da));})}));};return {_:1,a:_b1(10,_d9)};}else{return {_:2};}};return _9i(_9i({_:0,a:_d7},{_:0,a:_d3}),_d0);});return _9i({_:0,a:function(_db){return (E(_db)==101)?E(_cZ):{_:2};}},{_:0,a:function(_dc){return (E(_dc)==69)?E(_cZ):{_:2};}});},_dd=function(_de){var _df=function(_dg){return C > 19 ? new F(function(){return A1(_de,{_:1,a:_dg});}) : (++C,A1(_de,{_:1,a:_dg}));};return function(_dh){return (E(_dh)==46)?{_:1,a:_b1(10,_df)}:{_:2};};},_di=function(_dj){return {_:0,a:_dd(_dj)};},_dk=function(_dl){var _dm=function(_dn){var _do=function(_dp){return {_:1,a:_am(_cX,_bW,function(_dq){return C > 19 ? new F(function(){return A1(_dl,{_:5,a:{_:1,a:_dn,b:_dp,c:_dq}});}) : (++C,A1(_dl,{_:5,a:{_:1,a:_dn,b:_dp,c:_dq}}));})};};return {_:1,a:_am(_di,_bY,_do)};};return _b1(10,_dm);},_dr=function(_ds){return {_:1,a:_dk(_ds)};},_dt=function(_du){return E(E(_du).a);},_dv=function(_dw,_dx,_dy){while(1){var _dz=E(_dy);if(!_dz._){return false;}else{if(!B(A3(_dt,_dw,_dx,_dz.a))){_dy=_dz.b;continue;}else{return true;}}}},_dA=new T(function(){return unCStr("!@#$%&*+./<=>?\\^|:-~");}),_dB=function(_dC){return _dv(_9R,_dC,_dA);},_dD=function(_dE){var _dF=new T(function(){return B(A1(_dE,8));}),_dG=new T(function(){return B(A1(_dE,16));});return function(_dH){switch(E(_dH)){case 79:return E(_dF);case 88:return E(_dG);case 111:return E(_dF);case 120:return E(_dG);default:return {_:2};}};},_dI=function(_dJ){return {_:0,a:_dD(_dJ)};},_dK=function(_dL){return C > 19 ? new F(function(){return A1(_dL,10);}) : (++C,A1(_dL,10));},_dM=function(_dN){return err(unAppCStr("Prelude.chr: bad argument: ",new T(function(){return _2V(9,_dN,__Z);})));},_dO=function(_dP){var _dQ=E(_dP);if(!_dQ._){return E(_dQ.a);}else{return I_toInt(_dQ.a);}},_dR=function(_dS,_dT){var _dU=E(_dS);if(!_dU._){var _dV=_dU.a,_dW=E(_dT);return (_dW._==0)?_dV<=_dW.a:I_compareInt(_dW.a,_dV)>=0;}else{var _dX=_dU.a,_dY=E(_dT);return (_dY._==0)?I_compareInt(_dX,_dY.a)<=0:I_compare(_dX,_dY.a)<=0;}},_dZ=function(_e0){return {_:2};},_e1=function(_e2){var _e3=E(_e2);if(!_e3._){return _dZ;}else{var _e4=_e3.a,_e5=E(_e3.b);if(!_e5._){return E(_e4);}else{var _e6=new T(function(){return _e1(_e5);}),_e7=function(_e8){return _9i(B(A1(_e4,_e8)),new T(function(){return B(A1(_e6,_e8));}));};return _e7;}}},_e9=function(_ea,_eb){var _ec=function(_ed,_ee,_ef){var _eg=E(_ed);if(!_eg._){return C > 19 ? new F(function(){return A1(_ef,_ea);}) : (++C,A1(_ef,_ea));}else{var _eh=E(_ee);if(!_eh._){return {_:2};}else{if(E(_eg.a)!=E(_eh.a)){return {_:2};}else{var _ei=new T(function(){return B(_ec(_eg.b,_eh.b,_ef));});return {_:0,a:function(_ej){return E(_ei);}};}}}};return function(_ek){return C > 19 ? new F(function(){return _ec(_ea,_ek,_eb);}) : (++C,_ec(_ea,_ek,_eb));};},_el=new T(function(){return unCStr("SO");}),_em=function(_en){var _eo=new T(function(){return B(A1(_en,14));});return {_:1,a:_e9(_el,function(_ep){return E(_eo);})};},_eq=new T(function(){return unCStr("SOH");}),_er=function(_es){var _et=new T(function(){return B(A1(_es,1));});return {_:1,a:_e9(_eq,function(_eu){return E(_et);})};},_ev=new T(function(){return unCStr("NUL");}),_ew=function(_ex){var _ey=new T(function(){return B(A1(_ex,0));});return {_:1,a:_e9(_ev,function(_ez){return E(_ey);})};},_eA=new T(function(){return unCStr("STX");}),_eB=function(_eC){var _eD=new T(function(){return B(A1(_eC,2));});return {_:1,a:_e9(_eA,function(_eE){return E(_eD);})};},_eF=new T(function(){return unCStr("ETX");}),_eG=function(_eH){var _eI=new T(function(){return B(A1(_eH,3));});return {_:1,a:_e9(_eF,function(_eJ){return E(_eI);})};},_eK=new T(function(){return unCStr("EOT");}),_eL=function(_eM){var _eN=new T(function(){return B(A1(_eM,4));});return {_:1,a:_e9(_eK,function(_eO){return E(_eN);})};},_eP=new T(function(){return unCStr("ENQ");}),_eQ=function(_eR){var _eS=new T(function(){return B(A1(_eR,5));});return {_:1,a:_e9(_eP,function(_eT){return E(_eS);})};},_eU=new T(function(){return unCStr("ACK");}),_eV=function(_eW){var _eX=new T(function(){return B(A1(_eW,6));});return {_:1,a:_e9(_eU,function(_eY){return E(_eX);})};},_eZ=new T(function(){return unCStr("BEL");}),_f0=function(_f1){var _f2=new T(function(){return B(A1(_f1,7));});return {_:1,a:_e9(_eZ,function(_f3){return E(_f2);})};},_f4=new T(function(){return unCStr("BS");}),_f5=function(_f6){var _f7=new T(function(){return B(A1(_f6,8));});return {_:1,a:_e9(_f4,function(_f8){return E(_f7);})};},_f9=new T(function(){return unCStr("HT");}),_fa=function(_fb){var _fc=new T(function(){return B(A1(_fb,9));});return {_:1,a:_e9(_f9,function(_fd){return E(_fc);})};},_fe=new T(function(){return unCStr("LF");}),_ff=function(_fg){var _fh=new T(function(){return B(A1(_fg,10));});return {_:1,a:_e9(_fe,function(_fi){return E(_fh);})};},_fj=new T(function(){return unCStr("VT");}),_fk=function(_fl){var _fm=new T(function(){return B(A1(_fl,11));});return {_:1,a:_e9(_fj,function(_fn){return E(_fm);})};},_fo=new T(function(){return unCStr("FF");}),_fp=function(_fq){var _fr=new T(function(){return B(A1(_fq,12));});return {_:1,a:_e9(_fo,function(_fs){return E(_fr);})};},_ft=new T(function(){return unCStr("CR");}),_fu=function(_fv){var _fw=new T(function(){return B(A1(_fv,13));});return {_:1,a:_e9(_ft,function(_fx){return E(_fw);})};},_fy=new T(function(){return unCStr("SI");}),_fz=function(_fA){var _fB=new T(function(){return B(A1(_fA,15));});return {_:1,a:_e9(_fy,function(_fC){return E(_fB);})};},_fD=new T(function(){return unCStr("DLE");}),_fE=function(_fF){var _fG=new T(function(){return B(A1(_fF,16));});return {_:1,a:_e9(_fD,function(_fH){return E(_fG);})};},_fI=new T(function(){return unCStr("DC1");}),_fJ=function(_fK){var _fL=new T(function(){return B(A1(_fK,17));});return {_:1,a:_e9(_fI,function(_fM){return E(_fL);})};},_fN=new T(function(){return unCStr("DC2");}),_fO=function(_fP){var _fQ=new T(function(){return B(A1(_fP,18));});return {_:1,a:_e9(_fN,function(_fR){return E(_fQ);})};},_fS=new T(function(){return unCStr("DC3");}),_fT=function(_fU){var _fV=new T(function(){return B(A1(_fU,19));});return {_:1,a:_e9(_fS,function(_fW){return E(_fV);})};},_fX=new T(function(){return unCStr("DC4");}),_fY=function(_fZ){var _g0=new T(function(){return B(A1(_fZ,20));});return {_:1,a:_e9(_fX,function(_g1){return E(_g0);})};},_g2=new T(function(){return unCStr("NAK");}),_g3=function(_g4){var _g5=new T(function(){return B(A1(_g4,21));});return {_:1,a:_e9(_g2,function(_g6){return E(_g5);})};},_g7=new T(function(){return unCStr("SYN");}),_g8=function(_g9){var _ga=new T(function(){return B(A1(_g9,22));});return {_:1,a:_e9(_g7,function(_gb){return E(_ga);})};},_gc=new T(function(){return unCStr("ETB");}),_gd=function(_ge){var _gf=new T(function(){return B(A1(_ge,23));});return {_:1,a:_e9(_gc,function(_gg){return E(_gf);})};},_gh=new T(function(){return unCStr("CAN");}),_gi=function(_gj){var _gk=new T(function(){return B(A1(_gj,24));});return {_:1,a:_e9(_gh,function(_gl){return E(_gk);})};},_gm=new T(function(){return unCStr("EM");}),_gn=function(_go){var _gp=new T(function(){return B(A1(_go,25));});return {_:1,a:_e9(_gm,function(_gq){return E(_gp);})};},_gr=new T(function(){return unCStr("SUB");}),_gs=function(_gt){var _gu=new T(function(){return B(A1(_gt,26));});return {_:1,a:_e9(_gr,function(_gv){return E(_gu);})};},_gw=new T(function(){return unCStr("ESC");}),_gx=function(_gy){var _gz=new T(function(){return B(A1(_gy,27));});return {_:1,a:_e9(_gw,function(_gA){return E(_gz);})};},_gB=new T(function(){return unCStr("FS");}),_gC=function(_gD){var _gE=new T(function(){return B(A1(_gD,28));});return {_:1,a:_e9(_gB,function(_gF){return E(_gE);})};},_gG=new T(function(){return unCStr("GS");}),_gH=function(_gI){var _gJ=new T(function(){return B(A1(_gI,29));});return {_:1,a:_e9(_gG,function(_gK){return E(_gJ);})};},_gL=new T(function(){return unCStr("RS");}),_gM=function(_gN){var _gO=new T(function(){return B(A1(_gN,30));});return {_:1,a:_e9(_gL,function(_gP){return E(_gO);})};},_gQ=new T(function(){return unCStr("US");}),_gR=function(_gS){var _gT=new T(function(){return B(A1(_gS,31));});return {_:1,a:_e9(_gQ,function(_gU){return E(_gT);})};},_gV=new T(function(){return unCStr("SP");}),_gW=function(_gX){var _gY=new T(function(){return B(A1(_gX,32));});return {_:1,a:_e9(_gV,function(_gZ){return E(_gY);})};},_h0=new T(function(){return unCStr("DEL");}),_h1=function(_h2){var _h3=new T(function(){return B(A1(_h2,127));});return {_:1,a:_e9(_h0,function(_h4){return E(_h3);})};},_h5=new T(function(){return _e1({_:1,a:function(_h6){return {_:1,a:_am(_er,_em,_h6)};},b:{_:1,a:_ew,b:{_:1,a:_eB,b:{_:1,a:_eG,b:{_:1,a:_eL,b:{_:1,a:_eQ,b:{_:1,a:_eV,b:{_:1,a:_f0,b:{_:1,a:_f5,b:{_:1,a:_fa,b:{_:1,a:_ff,b:{_:1,a:_fk,b:{_:1,a:_fp,b:{_:1,a:_fu,b:{_:1,a:_fz,b:{_:1,a:_fE,b:{_:1,a:_fJ,b:{_:1,a:_fO,b:{_:1,a:_fT,b:{_:1,a:_fY,b:{_:1,a:_g3,b:{_:1,a:_g8,b:{_:1,a:_gd,b:{_:1,a:_gi,b:{_:1,a:_gn,b:{_:1,a:_gs,b:{_:1,a:_gx,b:{_:1,a:_gC,b:{_:1,a:_gH,b:{_:1,a:_gM,b:{_:1,a:_gR,b:{_:1,a:_gW,b:{_:1,a:_h1,b:__Z}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}});}),_h7=function(_h8){var _h9=new T(function(){return B(A1(_h8,7));}),_ha=new T(function(){return B(A1(_h8,8));}),_hb=new T(function(){return B(A1(_h8,9));}),_hc=new T(function(){return B(A1(_h8,10));}),_hd=new T(function(){return B(A1(_h8,11));}),_he=new T(function(){return B(A1(_h8,12));}),_hf=new T(function(){return B(A1(_h8,13));}),_hg=new T(function(){return B(A1(_h8,92));}),_hh=new T(function(){return B(A1(_h8,39));}),_hi=new T(function(){return B(A1(_h8,34));}),_hj=new T(function(){var _hk=function(_hl){var _hm=new T(function(){return _cl(E(_hl));}),_hn=function(_ho){var _hp=_cU(_hm,_ho);if(!_dR(_hp,{_:0,a:1114111})){return {_:2};}else{return C > 19 ? new F(function(){return A1(_h8,new T(function(){var _hq=_dO(_hp);if(_hq>>>0>1114111){return _dM(_hq);}else{return _hq;}}));}) : (++C,A1(_h8,new T(function(){var _hq=_dO(_hp);if(_hq>>>0>1114111){return _dM(_hq);}else{return _hq;}})));}};return {_:1,a:_b1(_hl,_hn)};},_hr=new T(function(){var _hs=new T(function(){return B(A1(_h8,31));}),_ht=new T(function(){return B(A1(_h8,30));}),_hu=new T(function(){return B(A1(_h8,29));}),_hv=new T(function(){return B(A1(_h8,28));}),_hw=new T(function(){return B(A1(_h8,27));}),_hx=new T(function(){return B(A1(_h8,26));}),_hy=new T(function(){return B(A1(_h8,25));}),_hz=new T(function(){return B(A1(_h8,24));}),_hA=new T(function(){return B(A1(_h8,23));}),_hB=new T(function(){return B(A1(_h8,22));}),_hC=new T(function(){return B(A1(_h8,21));}),_hD=new T(function(){return B(A1(_h8,20));}),_hE=new T(function(){return B(A1(_h8,19));}),_hF=new T(function(){return B(A1(_h8,18));}),_hG=new T(function(){return B(A1(_h8,17));}),_hH=new T(function(){return B(A1(_h8,16));}),_hI=new T(function(){return B(A1(_h8,15));}),_hJ=new T(function(){return B(A1(_h8,14));}),_hK=new T(function(){return B(A1(_h8,6));}),_hL=new T(function(){return B(A1(_h8,5));}),_hM=new T(function(){return B(A1(_h8,4));}),_hN=new T(function(){return B(A1(_h8,3));}),_hO=new T(function(){return B(A1(_h8,2));}),_hP=new T(function(){return B(A1(_h8,1));}),_hQ=new T(function(){return B(A1(_h8,0));}),_hR=function(_hS){switch(E(_hS)){case 64:return E(_hQ);case 65:return E(_hP);case 66:return E(_hO);case 67:return E(_hN);case 68:return E(_hM);case 69:return E(_hL);case 70:return E(_hK);case 71:return E(_h9);case 72:return E(_ha);case 73:return E(_hb);case 74:return E(_hc);case 75:return E(_hd);case 76:return E(_he);case 77:return E(_hf);case 78:return E(_hJ);case 79:return E(_hI);case 80:return E(_hH);case 81:return E(_hG);case 82:return E(_hF);case 83:return E(_hE);case 84:return E(_hD);case 85:return E(_hC);case 86:return E(_hB);case 87:return E(_hA);case 88:return E(_hz);case 89:return E(_hy);case 90:return E(_hx);case 91:return E(_hw);case 92:return E(_hv);case 93:return E(_hu);case 94:return E(_ht);case 95:return E(_hs);default:return {_:2};}};return _9i({_:0,a:function(_hT){return (E(_hT)==94)?E({_:0,a:_hR}):{_:2};}},new T(function(){return B(A1(_h5,_h8));}));});return _9i({_:1,a:_am(_dI,_dK,_hk)},_hr);});return _9i({_:0,a:function(_hU){switch(E(_hU)){case 34:return E(_hi);case 39:return E(_hh);case 92:return E(_hg);case 97:return E(_h9);case 98:return E(_ha);case 102:return E(_he);case 110:return E(_hc);case 114:return E(_hf);case 116:return E(_hb);case 118:return E(_hd);default:return {_:2};}}},_hj);},_hV=function(_hW){return C > 19 ? new F(function(){return A1(_hW,0);}) : (++C,A1(_hW,0));},_hX=function(_hY){var _hZ=E(_hY);if(!_hZ._){return _hV;}else{var _i0=E(_hZ.a),_i1=_i0>>>0,_i2=new T(function(){return _hX(_hZ.b);});if(_i1>887){var _i3=u_iswspace(_i0);if(!E(_i3)){return _hV;}else{var _i4=function(_i5){var _i6=new T(function(){return B(A1(_i2,_i5));});return {_:0,a:function(_i7){return E(_i6);}};};return _i4;}}else{if(_i1==32){var _i8=function(_i9){var _ia=new T(function(){return B(A1(_i2,_i9));});return {_:0,a:function(_ib){return E(_ia);}};};return _i8;}else{if(_i1-9>>>0>4){if(_i1==160){var _ic=function(_id){var _ie=new T(function(){return B(A1(_i2,_id));});return {_:0,a:function(_if){return E(_ie);}};};return _ic;}else{return _hV;}}else{var _ig=function(_ih){var _ii=new T(function(){return B(A1(_i2,_ih));});return {_:0,a:function(_ij){return E(_ii);}};};return _ig;}}}}},_ik=function(_il){var _im=new T(function(){return B(_ik(_il));}),_in=function(_io){return (E(_io)==92)?E(_im):{_:2};},_ip=function(_iq){return E({_:0,a:_in});},_ir={_:1,a:function(_is){return C > 19 ? new F(function(){return A2(_hX,_is,_ip);}) : (++C,A2(_hX,_is,_ip));}},_it=new T(function(){return B(_h7(function(_iu){return C > 19 ? new F(function(){return A1(_il,{_:0,a:_iu,b:true});}) : (++C,A1(_il,{_:0,a:_iu,b:true}));}));}),_iv=function(_iw){var _ix=E(_iw);if(_ix==38){return E(_im);}else{var _iy=_ix>>>0;if(_iy>887){var _iz=u_iswspace(_ix);return (E(_iz)==0)?{_:2}:E(_ir);}else{return (_iy==32)?E(_ir):(_iy-9>>>0>4)?(_iy==160)?E(_ir):{_:2}:E(_ir);}}};return _9i({_:0,a:function(_iA){return (E(_iA)==92)?E({_:0,a:_iv}):{_:2};}},{_:0,a:function(_iB){var _iC=E(_iB);if(_iC==92){return E(_it);}else{return C > 19 ? new F(function(){return A1(_il,{_:0,a:_iC,b:false});}) : (++C,A1(_il,{_:0,a:_iC,b:false}));}}});},_iD=function(_iE,_iF){var _iG=new T(function(){return B(A1(_iF,{_:1,a:new T(function(){return B(A1(_iE,__Z));})}));}),_iH=function(_iI){var _iJ=E(_iI),_iK=E(_iJ.a);if(_iK==34){if(!E(_iJ.b)){return E(_iG);}else{return C > 19 ? new F(function(){return _iD(function(_iL){return C > 19 ? new F(function(){return A1(_iE,{_:1,a:_iK,b:_iL});}) : (++C,A1(_iE,{_:1,a:_iK,b:_iL}));},_iF);}) : (++C,_iD(function(_iL){return C > 19 ? new F(function(){return A1(_iE,{_:1,a:_iK,b:_iL});}) : (++C,A1(_iE,{_:1,a:_iK,b:_iL}));},_iF));}}else{return C > 19 ? new F(function(){return _iD(function(_iM){return C > 19 ? new F(function(){return A1(_iE,{_:1,a:_iK,b:_iM});}) : (++C,A1(_iE,{_:1,a:_iK,b:_iM}));},_iF);}) : (++C,_iD(function(_iM){return C > 19 ? new F(function(){return A1(_iE,{_:1,a:_iK,b:_iM});}) : (++C,A1(_iE,{_:1,a:_iK,b:_iM}));},_iF));}};return C > 19 ? new F(function(){return _ik(_iH);}) : (++C,_ik(_iH));},_iN=new T(function(){return unCStr("_\'");}),_iO=function(_iP){var _iQ=u_iswalnum(_iP);if(!E(_iQ)){return _dv(_9R,_iP,_iN);}else{return true;}},_iR=function(_iS){return _iO(E(_iS));},_iT=new T(function(){return unCStr(",;()[]{}`");}),_iU=new T(function(){return unCStr("=>");}),_iV=new T(function(){return unCStr("~");}),_iW=new T(function(){return unCStr("@");}),_iX=new T(function(){return unCStr("->");}),_iY=new T(function(){return unCStr("<-");}),_iZ=new T(function(){return unCStr("|");}),_j0=new T(function(){return unCStr("\\");}),_j1=new T(function(){return unCStr("=");}),_j2=new T(function(){return unCStr("::");}),_j3=new T(function(){return unCStr("..");}),_j4=function(_j5){var _j6=new T(function(){return B(A1(_j5,{_:6}));}),_j7=new T(function(){var _j8=new T(function(){var _j9=function(_ja){var _jb=new T(function(){return B(A1(_j5,{_:0,a:_ja}));});return {_:0,a:function(_jc){return (E(_jc)==39)?E(_jb):{_:2};}};};return B(_h7(_j9));}),_jd=function(_je){var _jf=E(_je);switch(_jf){case 39:return {_:2};case 92:return E(_j8);default:var _jg=new T(function(){return B(A1(_j5,{_:0,a:_jf}));});return {_:0,a:function(_jh){return (E(_jh)==39)?E(_jg):{_:2};}};}},_ji=new T(function(){var _jj=new T(function(){return B(_iD(_h,_j5));}),_jk=new T(function(){var _jl=new T(function(){var _jm=new T(function(){var _jn=function(_jo){var _jp=E(_jo),_jq=u_iswalpha(_jp);return (E(_jq)==0)?(_jp==95)?{_:1,a:_aM(_iR,function(_jr){return C > 19 ? new F(function(){return A1(_j5,{_:3,a:{_:1,a:_jp,b:_jr}});}) : (++C,A1(_j5,{_:3,a:{_:1,a:_jp,b:_jr}}));})}:{_:2}:{_:1,a:_aM(_iR,function(_js){return C > 19 ? new F(function(){return A1(_j5,{_:3,a:{_:1,a:_jp,b:_js}});}) : (++C,A1(_j5,{_:3,a:{_:1,a:_jp,b:_js}}));})};};return _9i({_:0,a:_jn},new T(function(){return {_:1,a:_am(_bU,_dr,_j5)};}));}),_jt=function(_ju){return (!_dv(_9R,_ju,_dA))?{_:2}:{_:1,a:_aM(_dB,function(_jv){var _jw={_:1,a:_ju,b:_jv};if(!_dv({_:0,a:_9U,b:_9Z},_jw,{_:1,a:_j3,b:{_:1,a:_j2,b:{_:1,a:_j1,b:{_:1,a:_j0,b:{_:1,a:_iZ,b:{_:1,a:_iY,b:{_:1,a:_iX,b:{_:1,a:_iW,b:{_:1,a:_iV,b:{_:1,a:_iU,b:__Z}}}}}}}}}})){return C > 19 ? new F(function(){return A1(_j5,{_:4,a:_jw});}) : (++C,A1(_j5,{_:4,a:_jw}));}else{return C > 19 ? new F(function(){return A1(_j5,{_:2,a:_jw});}) : (++C,A1(_j5,{_:2,a:_jw}));}})};};return _9i({_:0,a:_jt},_jm);});return _9i({_:0,a:function(_jx){if(!_dv(_9R,_jx,_iT)){return {_:2};}else{return C > 19 ? new F(function(){return A1(_j5,{_:2,a:{_:1,a:_jx,b:__Z}});}) : (++C,A1(_j5,{_:2,a:{_:1,a:_jx,b:__Z}}));}}},_jl);});return _9i({_:0,a:function(_jy){return (E(_jy)==34)?E(_jj):{_:2};}},_jk);});return _9i({_:0,a:function(_jz){return (E(_jz)==39)?E({_:0,a:_jd}):{_:2};}},_ji);});return _9i({_:1,a:function(_jA){return (E(_jA)._==0)?E(_j6):{_:2};}},_j7);},_jB=function(_jC,_jD){var _jE=new T(function(){var _jF=new T(function(){var _jG=function(_jH){var _jI=new T(function(){var _jJ=new T(function(){return B(A1(_jD,_jH));});return B(_j4(function(_jK){var _jL=E(_jK);return (_jL._==2)?(!_3x(_jL.a,_9N))?{_:2}:E(_jJ):{_:2};}));}),_jM=function(_jN){return E(_jI);};return {_:1,a:function(_jO){return C > 19 ? new F(function(){return A2(_hX,_jO,_jM);}) : (++C,A2(_hX,_jO,_jM));}};};return B(A2(_jC,0,_jG));});return B(_j4(function(_jP){var _jQ=E(_jP);return (_jQ._==2)?(!_3x(_jQ.a,_9M))?{_:2}:E(_jF):{_:2};}));}),_jR=function(_jS){return E(_jE);};return function(_jT){return C > 19 ? new F(function(){return A2(_hX,_jT,_jR);}) : (++C,A2(_hX,_jT,_jR));};},_jU=function(_jV,_jW){var _jX=function(_jY){var _jZ=new T(function(){return B(A1(_jV,_jY));}),_k0=function(_k1){return _9i(B(A1(_jZ,_k1)),new T(function(){return {_:1,a:_jB(_jX,_k1)};}));};return _k0;},_k2=new T(function(){return B(A1(_jV,_jW));}),_k3=function(_k4){return _9i(B(A1(_k2,_k4)),new T(function(){return {_:1,a:_jB(_jX,_k4)};}));};return _k3;},_k5=function(_k6,_k7){var _k8=function(_k9,_ka){var _kb=function(_kc){return C > 19 ? new F(function(){return A1(_ka,new T(function(){return  -E(_kc);}));}) : (++C,A1(_ka,new T(function(){return  -E(_kc);})));},_kd=new T(function(){return B(_j4(function(_ke){return C > 19 ? new F(function(){return A3(_k6,_ke,_k9,_kb);}) : (++C,A3(_k6,_ke,_k9,_kb));}));}),_kf=function(_kg){return E(_kd);},_kh=function(_ki){return C > 19 ? new F(function(){return A2(_hX,_ki,_kf);}) : (++C,A2(_hX,_ki,_kf));},_kj=new T(function(){return B(_j4(function(_kk){var _kl=E(_kk);if(_kl._==4){var _km=E(_kl.a);if(!_km._){return C > 19 ? new F(function(){return A3(_k6,_kl,_k9,_ka);}) : (++C,A3(_k6,_kl,_k9,_ka));}else{if(E(_km.a)==45){if(!E(_km.b)._){return E({_:1,a:_kh});}else{return C > 19 ? new F(function(){return A3(_k6,_kl,_k9,_ka);}) : (++C,A3(_k6,_kl,_k9,_ka));}}else{return C > 19 ? new F(function(){return A3(_k6,_kl,_k9,_ka);}) : (++C,A3(_k6,_kl,_k9,_ka));}}}else{return C > 19 ? new F(function(){return A3(_k6,_kl,_k9,_ka);}) : (++C,A3(_k6,_kl,_k9,_ka));}}));}),_kn=function(_ko){return E(_kj);};return {_:1,a:function(_kp){return C > 19 ? new F(function(){return A2(_hX,_kp,_kn);}) : (++C,A2(_hX,_kp,_kn));}};};return _jU(_k8,_k7);},_kq=new T(function(){return 1/0;}),_kr=function(_ks,_kt){return C > 19 ? new F(function(){return A1(_kt,_kq);}) : (++C,A1(_kt,_kq));},_ku=new T(function(){return 0/0;}),_kv=function(_kw,_kx){return C > 19 ? new F(function(){return A1(_kx,_ku);}) : (++C,A1(_kx,_ku));},_ky=new T(function(){return unCStr("NaN");}),_kz=new T(function(){return unCStr("Infinity");}),_kA=new T(function(){var _kB=hs_wordToWord64(I_fromBits([4194982440,719304104])),_kC=hs_wordToWord64(I_fromBits([3110813675,1843557400]));return {_:0,a:_kB,b:_kC,c:{_:0,a:_kB,b:_kC,c:new T(function(){return unCStr("base");}),d:new T(function(){return unCStr("GHC.Exception");}),e:new T(function(){return unCStr("ArithException");})},d:__Z,e:__Z};}),_kD=function(_kE){return E(_kA);},_kF=new T(function(){return unCStr("Ratio has zero denominator");}),_kG=new T(function(){return unCStr("denormal");}),_kH=new T(function(){return unCStr("divide by zero");}),_kI=new T(function(){return unCStr("loss of precision");}),_kJ=new T(function(){return unCStr("arithmetic underflow");}),_kK=new T(function(){return unCStr("arithmetic overflow");}),_kL=function(_kM,_kN){switch(E(_kM)){case 0:return _Q(_kK,_kN);case 1:return _Q(_kJ,_kN);case 2:return _Q(_kI,_kN);case 3:return _Q(_kH,_kN);case 4:return _Q(_kG,_kN);default:return _Q(_kF,_kN);}},_kO=function(_kP){return _kL(_kP,__Z);},_kQ=new T(function(){return {_:0,a:_kD,b:{_:0,a:function(_kR,_kS,_kT){return _kL(_kS,_kT);},b:_kO,c:function(_kU,_kV){return _1J(_kL,_kU,_kV);}},c:_kW,d:function(_kX){var _kY=E(_kX);return _F(_D(_kY.a),_kD,_kY.b);},e:_kO};}),_kW=function(_8Q){return {_:0,a:_kQ,b:_8Q};},_kZ=new T(function(){return die(new T(function(){return _kW(3);}));}),_l0=function(_l1,_l2){var _l3=E(_l1);if(!_l3._){var _l4=_l3.a,_l5=E(_l2);return (_l5._==0)?_l4==_l5.a:(I_compareInt(_l5.a,_l4)==0)?true:false;}else{var _l6=_l3.a,_l7=E(_l2);return (_l7._==0)?(I_compareInt(_l6,_l7.a)==0)?true:false:(I_compare(_l6,_l7.a)==0)?true:false;}},_l8={_:0,a:0},_l9=function(_la,_lb){while(1){var _lc=E(_la);if(!_lc._){var _ld=E(_lc.a);if(_ld==(-2147483648)){_la={_:1,a:I_fromInt(-2147483648)};continue;}else{var _le=E(_lb);if(!_le._){return {_:0,a:_ld%_le.a};}else{_la={_:1,a:I_fromInt(_ld)};_lb=_le;continue;}}}else{var _lf=_lc.a,_lg=E(_lb);return (_lg._==0)?{_:1,a:I_rem(_lf,I_fromInt(_lg.a))}:{_:1,a:I_rem(_lf,_lg.a)};}}},_lh=function(_li,_lj){if(!_l0(_lj,_l8)){return _l9(_li,_lj);}else{return E(_kZ);}},_lk=function(_ll,_lm){while(1){if(!_l0(_lm,_l8)){var _ln=_lm,_lo=_lh(_ll,_lm);_ll=_ln;_lm=_lo;continue;}else{return E(_ll);}}},_lp=function(_lq){var _lr=E(_lq);if(!_lr._){var _ls=E(_lr.a);return (_ls==(-2147483648))?E(_ca):(_ls<0)?{_:0,a: -_ls}:_lr;}else{var _lt=_lr.a;return (I_compareInt(_lt,0)>=0)?_lr:{_:1,a:I_negate(_lt)};}},_lu=function(_lv,_lw){while(1){var _lx=E(_lv);if(!_lx._){var _ly=E(_lx.a);if(_ly==(-2147483648)){_lv={_:1,a:I_fromInt(-2147483648)};continue;}else{var _lz=E(_lw);if(!_lz._){return {_:0,a:quot(_ly,_lz.a)};}else{_lv={_:1,a:I_fromInt(_ly)};_lw=_lz;continue;}}}else{var _lA=_lx.a,_lB=E(_lw);return (_lB._==0)?{_:0,a:I_toInt(I_quot(_lA,I_fromInt(_lB.a)))}:{_:1,a:I_quot(_lA,_lB.a)};}}},_lC=new T(function(){return die(new T(function(){return _kW(5);}));}),_lD=function(_lE,_lF){if(!_l0(_lF,_l8)){var _lG=_lk(_lp(_lE),_lp(_lF));return (!_l0(_lG,_l8))?{_:0,a:_lu(_lE,_lG),b:_lu(_lF,_lG)}:E(_kZ);}else{return E(_lC);}},_lH={_:0,a:1},_lI=new T(function(){return err(new T(function(){return unCStr("Negative exponent");}));}),_lJ={_:0,a:2},_lK=new T(function(){return _l0(_lJ,_l8);}),_lL=function(_lM,_lN){while(1){var _lO=E(_lM);if(!_lO._){var _lP=_lO.a,_lQ=E(_lN);if(!_lQ._){var _lR=_lQ.a,_lS=subC(_lP,_lR);if(!E(_lS.b)){return {_:0,a:_lS.a};}else{_lM={_:1,a:I_fromInt(_lP)};_lN={_:1,a:I_fromInt(_lR)};continue;}}else{_lM={_:1,a:I_fromInt(_lP)};_lN=_lQ;continue;}}else{var _lT=E(_lN);if(!_lT._){_lM=_lO;_lN={_:1,a:I_fromInt(_lT.a)};continue;}else{return {_:1,a:I_sub(_lO.a,_lT.a)};}}}},_lU=function(_lV,_lW,_lX){while(1){if(!E(_lK)){if(!_l0(_l9(_lW,_lJ),_l8)){if(!_l0(_lW,_lH)){var _lY=_cq(_lV,_lV),_lZ=_lu(_lL(_lW,_lH),_lJ),_m0=_cq(_lV,_lX);_lV=_lY;_lW=_lZ;_lX=_m0;continue;}else{return _cq(_lV,_lX);}}else{var _lY=_cq(_lV,_lV),_lZ=_lu(_lW,_lJ);_lV=_lY;_lW=_lZ;continue;}}else{return E(_kZ);}}},_m1=function(_m2,_m3){while(1){if(!E(_lK)){if(!_l0(_l9(_m3,_lJ),_l8)){if(!_l0(_m3,_lH)){return _lU(_cq(_m2,_m2),_lu(_lL(_m3,_lH),_lJ),_m2);}else{return E(_m2);}}else{var _m4=_cq(_m2,_m2),_m5=_lu(_m3,_lJ);_m2=_m4;_m3=_m5;continue;}}else{return E(_kZ);}}},_m6=function(_m7,_m8){var _m9=E(_m7);if(!_m9._){var _ma=_m9.a,_mb=E(_m8);return (_mb._==0)?_ma<_mb.a:I_compareInt(_mb.a,_ma)>0;}else{var _mc=_m9.a,_md=E(_m8);return (_md._==0)?I_compareInt(_mc,_md.a)<0:I_compare(_mc,_md.a)<0;}},_me=function(_mf,_mg){if(!_m6(_mg,_l8)){if(!_l0(_mg,_l8)){return _m1(_mf,_mg);}else{return E(_lH);}}else{return E(_lI);}},_mh={_:0,a:1},_mi={_:0,a:0},_mj={_:0,a:-1},_mk=function(_ml){var _mm=E(_ml);if(!_mm._){var _mn=_mm.a;return (_mn>=0)?(E(_mn)==0)?E(_mi):E(_c0):E(_mj);}else{var _mo=I_compareInt(_mm.a,0);return (_mo<=0)?(E(_mo)==0)?E(_mi):E(_mj):E(_c0);}},_mp=function(_mq,_mr,_ms){while(1){var _mt=E(_ms);if(!_mt._){if(!_m6(_mq,_cD)){return {_:0,a:_cq(_mr,B(_me(_cf,_mq))),b:_lH};}else{var _mu=B(_me(_cf,_cb(_mq)));return _lD(_cq(_mr,_mk(_mu)),_lp(_mu));}}else{var _mv=_lL(_mq,_mh),_mw=_c1(_cq(_mr,_cf),_cl(E(_mt.a)));_mq=_mv;_mr=_mw;_ms=_mt.b;continue;}}},_mx=function(_my,_mz){var _mA=E(_my);if(!_mA._){var _mB=_mA.a,_mC=E(_mz);return (_mC._==0)?_mB>=_mC.a:I_compareInt(_mC.a,_mB)<=0;}else{var _mD=_mA.a,_mE=E(_mz);return (_mE._==0)?I_compareInt(_mD,_mE.a)>=0:I_compare(_mD,_mE.a)>=0;}},_mF=function(_mG){var _mH=E(_mG);if(!_mH._){var _mI=_mH.b;return _lD(_cq(_cE(new T(function(){return _cl(E(_mH.a));}),new T(function(){return _cg(_mI,0);},1),_45(_cn,_mI)),_mh),_mh);}else{var _mJ=_mH.a,_mK=_mH.c,_mL=E(_mH.b);if(!_mL._){var _mM=E(_mK);if(!_mM._){return _lD(_cq(_cU(_cf,_mJ),_mh),_mh);}else{var _mN=_mM.a;if(!_mx(_mN,_cD)){var _mO=B(_me(_cf,_cb(_mN)));return _lD(_cq(_cU(_cf,_mJ),_mk(_mO)),_lp(_mO));}else{return _lD(_cq(_cq(_cU(_cf,_mJ),B(_me(_cf,_mN))),_mh),_mh);}}}else{var _mP=_mL.a,_mQ=E(_mK);if(!_mQ._){return _mp(_cD,_cU(_cf,_mJ),_mP);}else{return _mp(_mQ.a,_cU(_cf,_mJ),_mP);}}}},_mR=function(_mS,_mT){while(1){var _mU=E(_mT);if(!_mU._){return __Z;}else{if(!B(A1(_mS,_mU.a))){return _mU;}else{_mT=_mU.b;continue;}}}},_mV=function(_mW,_mX){var _mY=E(_mW);if(!_mY._){var _mZ=_mY.a,_n0=E(_mX);return (_n0._==0)?_mZ>_n0.a:I_compareInt(_n0.a,_mZ)<0;}else{var _n1=_mY.a,_n2=E(_mX);return (_n2._==0)?I_compareInt(_n1,_n2.a)>0:I_compare(_n1,_n2.a)>0;}},_n3=function(_n4,_n5){return E(_n4)==E(_n5);},_n6=function(_n7){return _n3(0,_n7);},_n8={_:1,a:{_:0,a:E(_cD),b:E(_lH)}},_n9=function(_na,_nb,_nc){var _nd=E(_nc);if(!_nd._){return {_:1,a:new T(function(){var _ne=_mF(_nd);return {_:0,a:E(_ne.a),b:E(_ne.b)};})};}else{var _nf=E(_nd.c);if(!_nf._){return {_:1,a:new T(function(){var _ng=_mF(_nd);return {_:0,a:E(_ng.a),b:E(_ng.b)};})};}else{var _nh=_nf.a;if(!_mV(_nh,{_:0,a:2147483647})){if(!_m6(_nh,{_:0,a:-2147483648})){var _ni=function(_nj){var _nk=_nj+_dO(_nh)|0;return (_nk<=(E(_nb)+3|0))?(_nk>=(E(_na)-3|0))?{_:1,a:new T(function(){var _nl=_mF(_nd);return {_:0,a:E(_nl.a),b:E(_nl.b)};})}:E(_n8):__Z;},_nm=_mR(_n6,_nd.a);if(!_nm._){var _nn=E(_nd.b);if(!_nn._){return E(_n8);}else{var _no=_3n(_n6,_nn.a);if(!E(_no.b)._){return E(_n8);}else{return _ni( -_cg(_no.a,0));}}}else{return _ni(_cg(_nm,0));}}else{return __Z;}}else{return __Z;}}}},_np=function(_nq,_nr){return {_:2};},_ns={_:0,a:1},_nt=function(_nu,_nv){var _nw=E(_nu);if(!_nw._){var _nx=_nw.a,_ny=E(_nv);if(!_ny._){var _nz=_ny.a;return (_nx!=_nz)?(_nx>_nz)?2:0:1;}else{var _nA=I_compareInt(_ny.a,_nx);return (_nA<=0)?(_nA>=0)?1:2:0;}}else{var _nB=_nw.a,_nC=E(_nv);if(!_nC._){var _nD=I_compareInt(_nB,_nC.a);return (_nD>=0)?(_nD<=0)?1:2:0;}else{var _nE=I_compare(_nB,_nC.a);return (_nE>=0)?(_nE<=0)?1:2:0;}}},_nF=function(_nG,_nH){var _nI=E(_nG);return (_nI._==0)?_nI.a*Math.pow(2,_nH):I_toNumber(_nI.a)*Math.pow(2,_nH);},_nJ=function(_nK,_nL){while(1){var _nM=E(_nK);if(!_nM._){var _nN=E(_nM.a);if(_nN==(-2147483648)){_nK={_:1,a:I_fromInt(-2147483648)};continue;}else{var _nO=E(_nL);if(!_nO._){var _nP=_nO.a;return {_:0,a:{_:0,a:quot(_nN,_nP)},b:{_:0,a:_nN%_nP}};}else{_nK={_:1,a:I_fromInt(_nN)};_nL=_nO;continue;}}}else{var _nQ=E(_nL);if(!_nQ._){_nK=_nM;_nL={_:1,a:I_fromInt(_nQ.a)};continue;}else{var _nR=I_quotRem(_nM.a,_nQ.a);return {_:0,a:{_:1,a:_nR.a},b:{_:1,a:_nR.b}};}}}},_nS={_:0,a:0},_nT=function(_nU,_nV){while(1){var _nW=E(_nU);if(!_nW._){_nU={_:1,a:I_fromInt(_nW.a)};continue;}else{return {_:1,a:I_shiftLeft(_nW.a,_nV)};}}},_nX=function(_nY,_nZ,_o0){if(!_l0(_o0,_nS)){var _o1=_nJ(_nZ,_o0),_o2=_o1.a;switch(_nt(_nT(_o1.b,1),_o0)){case 0:return _nF(_o2,_nY);case 1:if(!(_dO(_o2)&1)){return _nF(_o2,_nY);}else{return _nF(_c1(_o2,_ns),_nY);}break;default:return _nF(_c1(_o2,_ns),_nY);}}else{return E(_kZ);}},_o3=function(_o4){var _o5=_c0,_o6=0;while(1){if(!_m6(_o5,_o4)){if(!_mV(_o5,_o4)){if(!_l0(_o5,_o4)){return C > 19 ? new F(function(){return _95("GHC/Integer/Type.lhs:(553,5)-(555,32)|function l2");}) : (++C,_95("GHC/Integer/Type.lhs:(553,5)-(555,32)|function l2"));}else{return _o6;}}else{return _o6-1|0;}}else{var _o7=_nT(_o5,1),_o8=_o6+1|0;_o5=_o7;_o6=_o8;continue;}}},_o9=function(_oa){var _ob=E(_oa);if(!_ob._){var _oc=_ob.a>>>0;if(!_oc){return -1;}else{var _od=1,_oe=0;while(1){if(_od>=_oc){if(_od<=_oc){if(_od!=_oc){return C > 19 ? new F(function(){return _95("GHC/Integer/Type.lhs:(610,5)-(612,40)|function l2");}) : (++C,_95("GHC/Integer/Type.lhs:(610,5)-(612,40)|function l2"));}else{return _oe;}}else{return _oe-1|0;}}else{var _of=imul(_od,2)>>>0,_og=_oe+1|0;_od=_of;_oe=_og;continue;}}}}else{return C > 19 ? new F(function(){return _o3(_ob);}) : (++C,_o3(_ob));}},_oh=function(_oi){var _oj=E(_oi);if(!_oj._){var _ok=_oj.a>>>0;if(!_ok){return {_:0,a:-1,b:0};}else{return {_:0,a:B((function(_ol,_om){while(1){if(_ol>=_ok){if(_ol<=_ok){if(_ol!=_ok){return C > 19 ? new F(function(){return _95("GHC/Integer/Type.lhs:(610,5)-(612,40)|function l2");}) : (++C,_95("GHC/Integer/Type.lhs:(610,5)-(612,40)|function l2"));}else{return E(_om);}}else{return _om-1|0;}}else{var _on=imul(_ol,2)>>>0,_oo=_om+1|0;_ol=_on;_om=_oo;continue;}}})(1,0)),b:(_ok&_ok-1>>>0)>>>0&4294967295};}}else{var _op=B(_o9(_oj)),_oq=_op>>>0;if(!_oq){var _or=E(_op);return (_or==(-2))?{_:0,a:-2,b:0}:{_:0,a:_or,b:1};}else{var _os=B((function(_ot,_ou){while(1){if(_ot>=_oq){if(_ot<=_oq){if(_ot!=_oq){return C > 19 ? new F(function(){return _95("GHC/Integer/Type.lhs:(610,5)-(612,40)|function l2");}) : (++C,_95("GHC/Integer/Type.lhs:(610,5)-(612,40)|function l2"));}else{return E(_ou);}}else{return _ou-1|0;}}else{var _ov=imul(_ot,2)>>>0,_ow=_ou+1|0;_ot=_ov;_ou=_ow;continue;}}})(1,0));return ((_os+_os|0)!=_op)?{_:0,a:_op,b:1}:{_:0,a:_op,b:0};}}},_ox=function(_oy,_oz){while(1){var _oA=E(_oy);if(!_oA._){var _oB=_oA.a,_oC=E(_oz);if(!_oC._){return {_:0,a:(_oB>>>0&_oC.a>>>0)>>>0&4294967295};}else{_oy={_:1,a:I_fromInt(_oB)};_oz=_oC;continue;}}else{var _oD=E(_oz);if(!_oD._){_oy=_oA;_oz={_:1,a:I_fromInt(_oD.a)};continue;}else{return {_:1,a:I_and(_oA.a,_oD.a)};}}}},_oE=function(_oF,_oG){var _oH=E(_oF);if(!_oH._){var _oI=(_oH.a>>>0&(2<<_oG>>>0)-1>>>0)>>>0,_oJ=1<<_oG>>>0;return (_oJ<=_oI)?(_oJ>=_oI)?1:2:0;}else{var _oK=_ox(_oH,_lL(_nT({_:0,a:2},_oG),_c0)),_oL=_nT(_c0,_oG);return (!_mV(_oL,_oK))?(!_m6(_oL,_oK))?1:2:0;}},_oM=function(_oN,_oO){while(1){var _oP=E(_oN);if(!_oP._){_oN={_:1,a:I_fromInt(_oP.a)};continue;}else{return {_:1,a:I_shiftRight(_oP.a,_oO)};}}},_oQ=function(_oR,_oS,_oT,_oU){var _oV=_oh(_oU),_oW=_oV.a;if(!E(_oV.b)){var _oX=B(_o9(_oT));if(_oX<((_oW+_oR|0)-1|0)){var _oY=_oW+(_oR-_oS|0)|0;if(_oY>0){if(_oY>_oX){if(_oY<=(_oX+1|0)){if(!E(_oh(_oT).b)){return 0;}else{return _nF(_ns,_oR-_oS|0);}}else{return 0;}}else{var _oZ=_oM(_oT,_oY);switch(_oE(_oT,_oY-1|0)){case 0:return _nF(_oZ,_oR-_oS|0);case 1:if(!(_dO(_oZ)&1)){return _nF(_oZ,_oR-_oS|0);}else{return _nF(_c1(_oZ,_ns),_oR-_oS|0);}break;default:return _nF(_c1(_oZ,_ns),_oR-_oS|0);}}}else{return _nF(_oT,(_oR-_oS|0)-_oY|0);}}else{if(_oX>=_oS){var _p0=_oM(_oT,(_oX+1|0)-_oS|0);switch(_oE(_oT,_oX-_oS|0)){case 0:return _nF(_p0,((_oX-_oW|0)+1|0)-_oS|0);case 2:return _nF(_c1(_p0,_ns),((_oX-_oW|0)+1|0)-_oS|0);default:if(!(_dO(_p0)&1)){return _nF(_p0,((_oX-_oW|0)+1|0)-_oS|0);}else{return _nF(_c1(_p0,_ns),((_oX-_oW|0)+1|0)-_oS|0);}}}else{return _nF(_oT, -_oW);}}}else{var _p1=B(_o9(_oT))-_oW|0,_p2=function(_p3){var _p4=function(_p5,_p6){if(!_dR(_nT(_p6,_oS),_p5)){return _nX(_p3-_oS|0,_p5,_p6);}else{return _nX((_p3-_oS|0)+1|0,_p5,_nT(_p6,1));}};if(_p3>=_oS){if(_p3!=_oS){return _p4(_oT,new T(function(){return _nT(_oU,_p3-_oS|0);}));}else{return _p4(_oT,_oU);}}else{return _p4(new T(function(){return _nT(_oT,_oS-_p3|0);}),_oU);}};if(_oR>_p1){return C > 19 ? new F(function(){return _p2(_oR);}) : (++C,_p2(_oR));}else{return C > 19 ? new F(function(){return _p2(_p1);}) : (++C,_p2(_p1));}}},_p7=new T(function(){return 0/0;}),_p8=new T(function(){return -1/0;}),_p9=new T(function(){return 1/0;}),_pa=function(_pb,_pc){if(!_l0(_pc,_nS)){if(!_l0(_pb,_nS)){if(!_m6(_pb,_nS)){return C > 19 ? new F(function(){return _oQ(-1021,53,_pb,_pc);}) : (++C,_oQ(-1021,53,_pb,_pc));}else{return  -B(_oQ(-1021,53,_cb(_pb),_pc));}}else{return 0;}}else{return (!_l0(_pb,_nS))?(!_m6(_pb,_nS))?E(_p9):E(_p8):E(_p7);}},_pd=function(_pe){var _pf=E(_pe);switch(_pf._){case 3:var _pg=_pf.a;return (!_3x(_pg,_kz))?(!_3x(_pg,_ky))?_np:_kv:_kr;case 5:var _ph=_n9(-1021,1024,_pf.a);if(!_ph._){return _kr;}else{var _pi=new T(function(){var _pj=E(_ph.a);return B(_pa(_pj.a,_pj.b));});return function(_pk,_pl){return C > 19 ? new F(function(){return A1(_pl,_pi);}) : (++C,A1(_pl,_pi));};}break;default:return _np;}},_pm=function(_pn){return {_:2,a:E(_pn)};},_po=new T(function(){return {_:0,a:function(_pp,_pq){switch(E(_pp)._){case 0:switch(E(_pq)._){case 0:return true;case 1:return false;case 2:return false;default:return false;}break;case 1:return (E(_pq)._==1)?true:false;case 2:return (E(_pq)._==2)?true:false;default:return (E(_pq)._==3)?true:false;}},b:_pr};}),_pr=function(_ps,_pt){return (!B(A3(_dt,_po,_ps,_pt)))?true:false;},_pu={_:2,a:E(__Z)},_pv=function(_pw){return _pr(_pu,_pw);},_px=function(_py,_pz,_pA){var _pB=E(_pA);if(!_pB._){return {_:0,a:_py,b:{_:1,a:_pu,b:new T(function(){return _3C(_pv,_pz);})}};}else{var _pC=_pB.a,_pD=E(_pB.b);if(!_pD._){var _pE=new T(function(){return {_:2,a:E(_pC)};}),_pF=new T(function(){return _3C(function(_pw){return _pr(_pE,_pw);},_pz);});return {_:0,a:_py,b:{_:1,a:_pE,b:_pF}};}else{var _pG=new T(function(){return {_:2,a:E(_pC)};}),_pH=new T(function(){return _3C(function(_pw){return _pr(_pG,_pw);},_pz);}),_pI=function(_pJ){var _pK=E(_pJ);if(!_pK._){return {_:0,a:_py,b:{_:1,a:_pG,b:_pH}};}else{var _pL=_pI(_pK.b);return {_:0,a:_pL.a,b:{_:1,a:new T(function(){return _pm(_pK.a);}),b:_pL.b}};}},_pM=_pI(_pD.b);return {_:0,a:_pM.a,b:{_:1,a:new T(function(){return _pm(_pD.a);}),b:_pM.b}};}}},_pN=function(_pO,_pP){var _pQ=E(_pO),_pR=_px(_pQ.a,_pQ.b,_pP);return {_:0,a:E(_pR.a),b:_pR.b};},_pS=function(_pT,_pU,_pV,_pW,_pX,_pY,_pZ){var _q0=function(_q1){return C > 19 ? new F(function(){return A1(_pZ,new T(function(){return _pN(_q1,_pU);}));}) : (++C,A1(_pZ,new T(function(){return _pN(_q1,_pU);})));},_q2=function(_q3,_q4,_q5){return C > 19 ? new F(function(){return A3(_pY,_q3,_q4,new T(function(){var _q6=E(_q5),_q7=E(_q6.b);if(!_q7._){return _q6;}else{var _q8=_px(_q6.a,_q7,_pU);return {_:0,a:E(_q8.a),b:_q8.b};}}));}) : (++C,A3(_pY,_q3,_q4,new T(function(){var _q6=E(_q5),_q7=E(_q6.b);if(!_q7._){return _q6;}else{var _q8=_px(_q6.a,_q7,_pU);return {_:0,a:E(_q8.a),b:_q8.b};}})));};return C > 19 ? new F(function(){return A(_pT,[_pV,_pW,_pX,_q2,_q0]);}) : (++C,A(_pT,[_pV,_pW,_pX,_q2,_q0]));},_q9=function(_qa){return E(E(_qa).a);},_qb={_:1,a:34,b:__Z},_qc=function(_qd,_qe){var _qf=_qd%_qe;if(_qd<=0){if(_qd>=0){return _qf;}else{if(_qe<=0){return _qf;}else{return (_qf==0)?0:_qf+_qe|0;}}}else{if(_qe>=0){if(_qd>=0){return _qf;}else{if(_qe<=0){return _qf;}else{return (_qf==0)?0:_qf+_qe|0;}}}else{return (_qf==0)?0:_qf+_qe|0;}}},_qg=new T(function(){return err(new T(function(){return _Q(_3V,new T(function(){return unCStr("!!: negative index");}));}));}),_qh=new T(function(){return err(new T(function(){return _Q(_3V,new T(function(){return unCStr("!!: index too large");}));}));}),_qi=function(_qj,_qk){while(1){var _ql=E(_qj);if(!_ql._){return E(_qh);}else{var _qm=E(_qk);if(!_qm){return E(_ql.a);}else{_qj=_ql.b;_qk=_qm-1|0;continue;}}}},_qn=function(_qo,_qp){if(_qp>=0){return _qi(_qo,_qp);}else{return E(_qg);}},_qq=new T(function(){return unCStr("ACK");}),_qr=new T(function(){return unCStr("BEL");}),_qs=new T(function(){return unCStr("BS");}),_qt=new T(function(){return unCStr("SP");}),_qu=new T(function(){return unCStr("US");}),_qv=new T(function(){return unCStr("RS");}),_qw=new T(function(){return unCStr("GS");}),_qx=new T(function(){return unCStr("FS");}),_qy=new T(function(){return unCStr("ESC");}),_qz=new T(function(){return unCStr("SUB");}),_qA=new T(function(){return unCStr("EM");}),_qB=new T(function(){return unCStr("CAN");}),_qC=new T(function(){return unCStr("ETB");}),_qD=new T(function(){return unCStr("SYN");}),_qE=new T(function(){return unCStr("NAK");}),_qF=new T(function(){return unCStr("DC4");}),_qG=new T(function(){return unCStr("DC3");}),_qH=new T(function(){return unCStr("DC2");}),_qI=new T(function(){return unCStr("DC1");}),_qJ=new T(function(){return unCStr("DLE");}),_qK=new T(function(){return unCStr("SI");}),_qL=new T(function(){return unCStr("SO");}),_qM=new T(function(){return unCStr("CR");}),_qN=new T(function(){return unCStr("FF");}),_qO=new T(function(){return unCStr("VT");}),_qP=new T(function(){return unCStr("LF");}),_qQ=new T(function(){return unCStr("HT");}),_qR=new T(function(){return unCStr("ENQ");}),_qS=new T(function(){return unCStr("EOT");}),_qT=new T(function(){return unCStr("ETX");}),_qU=new T(function(){return unCStr("STX");}),_qV=new T(function(){return unCStr("SOH");}),_qW=new T(function(){return unCStr("NUL");}),_qX=new T(function(){return unCStr("\\DEL");}),_qY=new T(function(){return unCStr("\\a");}),_qZ=new T(function(){return unCStr("\\\\");}),_r0=new T(function(){return unCStr("\\SO");}),_r1=new T(function(){return unCStr("\\r");}),_r2=new T(function(){return unCStr("\\f");}),_r3=new T(function(){return unCStr("\\v");}),_r4=new T(function(){return unCStr("\\n");}),_r5=new T(function(){return unCStr("\\t");}),_r6=new T(function(){return unCStr("\\b");}),_r7=function(_r8,_r9){if(_r8<=127){var _ra=E(_r8);switch(_ra){case 92:return _Q(_qZ,_r9);case 127:return _Q(_qX,_r9);default:if(_ra<32){switch(_ra){case 7:return _Q(_qY,_r9);case 8:return _Q(_r6,_r9);case 9:return _Q(_r5,_r9);case 10:return _Q(_r4,_r9);case 11:return _Q(_r3,_r9);case 12:return _Q(_r2,_r9);case 13:return _Q(_r1,_r9);case 14:return _Q(_r0,new T(function(){var _rb=E(_r9);if(!_rb._){return __Z;}else{if(E(_rb.a)==72){return unAppCStr("\\&",_rb);}else{return _rb;}}},1));default:return _Q({_:1,a:92,b:new T(function(){return _qn({_:1,a:_qW,b:{_:1,a:_qV,b:{_:1,a:_qU,b:{_:1,a:_qT,b:{_:1,a:_qS,b:{_:1,a:_qR,b:{_:1,a:_qq,b:{_:1,a:_qr,b:{_:1,a:_qs,b:{_:1,a:_qQ,b:{_:1,a:_qP,b:{_:1,a:_qO,b:{_:1,a:_qN,b:{_:1,a:_qM,b:{_:1,a:_qL,b:{_:1,a:_qK,b:{_:1,a:_qJ,b:{_:1,a:_qI,b:{_:1,a:_qH,b:{_:1,a:_qG,b:{_:1,a:_qF,b:{_:1,a:_qE,b:{_:1,a:_qD,b:{_:1,a:_qC,b:{_:1,a:_qB,b:{_:1,a:_qA,b:{_:1,a:_qz,b:{_:1,a:_qy,b:{_:1,a:_qx,b:{_:1,a:_qw,b:{_:1,a:_qv,b:{_:1,a:_qu,b:{_:1,a:_qt,b:__Z}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}},_ra);})},_r9);}}else{return {_:1,a:_ra,b:_r9};}}}else{var _rc=new T(function(){var _rd=jsShowI(_r8);return _Q(fromJSStr(_rd),new T(function(){var _re=E(_r9);if(!_re._){return __Z;}else{var _rf=E(_re.a);if(_rf<48){return _re;}else{if(_rf>57){return _re;}else{return unAppCStr("\\&",_re);}}}},1));});return {_:1,a:92,b:_rc};}},_rg=new T(function(){return unCStr("\\\"");}),_rh=function(_ri,_rj){var _rk=E(_ri);if(!_rk._){return E(_rj);}else{var _rl=_rk.b,_rm=E(_rk.a);if(_rm==34){return _Q(_rg,new T(function(){return _rh(_rl,_rj);},1));}else{return _r7(_rm,new T(function(){return _rh(_rl,_rj);}));}}},_rn=function(_ro){return E(E(_ro).b);},_rp=function(_rq,_rr,_rs,_rt,_ru,_rv,_rw,_rx,_ry){var _rz={_:0,a:_rt,b:_ru,c:_rv},_rA=new T(function(){return B(A1(_ry,{_:0,a:E(_rz),b:{_:1,a:{_:0,a:E(__Z)},b:__Z}}));}),_rB=function(_rC){var _rD=E(_rC);if(!_rD._){return E(_rA);}else{var _rE=E(_rD.a),_rF=_rE.a;if(!B(A1(_rr,_rF))){return C > 19 ? new F(function(){return A1(_ry,{_:0,a:E(_rz),b:{_:1,a:{_:0,a:E({_:1,a:34,b:new T(function(){return _rh({_:1,a:_rF,b:__Z},_qb);})})},b:__Z}});}) : (++C,A1(_ry,{_:0,a:E(_rz),b:{_:1,a:{_:0,a:E({_:1,a:34,b:new T(function(){return _rh({_:1,a:_rF,b:__Z},_qb);})})},b:__Z}}));}else{var _rG=E(_rF);switch(_rG){case 9:var _rH={_:0,a:_rt,b:_ru,c:(_rv+8|0)-_qc(_rv-1|0,8)|0};break;case 10:var _rH=E({_:0,a:_rt,b:_ru+1|0,c:1});break;default:var _rH=E({_:0,a:_rt,b:_ru,c:_rv+1|0});}return C > 19 ? new F(function(){return A3(_rx,_rG,{_:0,a:_rE.b,b:E(_rH),c:E(_rw)},{_:0,a:E(_rH),b:__Z});}) : (++C,A3(_rx,_rG,{_:0,a:_rE.b,b:E(_rH),c:E(_rw)},{_:0,a:E(_rH),b:__Z}));}}};return C > 19 ? new F(function(){return A3(_2n,_q9(_rq),new T(function(){return B(A2(_rn,_rq,_rs));}),_rB);}) : (++C,A3(_2n,_q9(_rq),new T(function(){return B(A2(_rn,_rq,_rs));}),_rB));},_rI=function(_rJ){return (E(_rJ)-48|0)>>>0<=9;},_rK=function(_rL,_rM,_rN,_rO,_rP){var _rQ=E(_rL),_rR=E(_rQ.b);return C > 19 ? new F(function(){return _rp(_2F,_rI,_rQ.a,_rR.a,_rR.b,_rR.c,_rQ.c,_rM,_rP);}) : (++C,_rp(_2F,_rI,_rQ.a,_rR.a,_rR.b,_rR.c,_rQ.c,_rM,_rP));},_rS=new T(function(){return unCStr("digit");}),_rT=function(_rU,_rV,_rW,_rX,_rY){return C > 19 ? new F(function(){return _pS(_rK,{_:1,a:_rS,b:__Z},_rU,_rV,_rW,_rX,_rY);}) : (++C,_pS(_rK,{_:1,a:_rS,b:__Z},_rU,_rV,_rW,_rX,_rY));},_rZ=function(_s0,_s1,_s2,_s3,_s4,_s5){var _s6=function(_s7,_s8,_s9,_sa,_sb){var _sc=function(_sd,_se,_sf){return C > 19 ? new F(function(){return A3(_sb,{_:1,a:_s7,b:_sd},_se,new T(function(){var _sg=E(E(_se).b),_sh=E(_sf),_si=E(_sh.a),_sj=_6q(_si.a,_si.b,_si.c,_sh.b,_sg.a,_sg.b,_sg.c,__Z);return {_:0,a:E(_sj.a),b:_sj.b};}));}) : (++C,A3(_sb,{_:1,a:_s7,b:_sd},_se,new T(function(){var _sg=E(E(_se).b),_sh=E(_sf),_si=E(_sh.a),_sj=_6q(_si.a,_si.b,_si.c,_sh.b,_sg.a,_sg.b,_sg.c,__Z);return {_:0,a:E(_sj.a),b:_sj.b};})));},_sk=function(_sl,_sm,_sn){return C > 19 ? new F(function(){return A3(_s9,{_:1,a:_s7,b:_sl},_sm,new T(function(){var _so=E(E(_sm).b),_sp=E(_sn),_sq=E(_sp.a),_sr=_6q(_sq.a,_sq.b,_sq.c,_sp.b,_so.a,_so.b,_so.c,__Z);return {_:0,a:E(_sr.a),b:_sr.b};}));}) : (++C,A3(_s9,{_:1,a:_s7,b:_sl},_sm,new T(function(){var _so=E(E(_sm).b),_sp=E(_sn),_sq=E(_sp.a),_sr=_6q(_sq.a,_sq.b,_sq.c,_sp.b,_so.a,_so.b,_so.c,__Z);return {_:0,a:E(_sr.a),b:_sr.b};})));};return C > 19 ? new F(function(){return _6M(_s0,_s8,_sk,_sa,_sc);}) : (++C,_6M(_s0,_s8,_sk,_sa,_sc));},_ss=function(_st,_su,_sv){var _sw=function(_sx,_sy,_sz){return C > 19 ? new F(function(){return A3(_s4,_sx,_sy,new T(function(){return _7i(_sv,_sz);}));}) : (++C,A3(_s4,_sx,_sy,new T(function(){return _7i(_sv,_sz);})));};return C > 19 ? new F(function(){return _s6(_st,_su,_s2,_s3,_sw);}) : (++C,_s6(_st,_su,_s2,_s3,_sw));},_sA=function(_sB,_sC,_sD){var _sE=function(_sF,_sG,_sH){return C > 19 ? new F(function(){return A3(_s2,_sF,_sG,new T(function(){return _7i(_sD,_sH);}));}) : (++C,A3(_s2,_sF,_sG,new T(function(){return _7i(_sD,_sH);})));};return C > 19 ? new F(function(){return _s6(_sB,_sC,_s2,_s3,_sE);}) : (++C,_s6(_sB,_sC,_s2,_s3,_sE));};return C > 19 ? new F(function(){return A(_s0,[_s1,_sA,_s3,_ss,_s5]);}) : (++C,A(_s0,[_s1,_sA,_s3,_ss,_s5]));},_sI=function(_sJ,_sK,_sL,_sM,_sN){return C > 19 ? new F(function(){return _rZ(_rT,_sJ,_sK,_sL,_sM,_sN);}) : (++C,_rZ(_rT,_sJ,_sK,_sL,_sM,_sN));},_sO=function(_sP,_sQ){var _sR=function(_sS){return _9O(_sS,_sQ);},_sT=function(_sU,_sV,_sW,_sX,_sY){var _sZ=E(_sU),_t0=E(_sZ.b);return C > 19 ? new F(function(){return _rp(_sP,_sR,_sZ.a,_t0.a,_t0.b,_t0.c,_sZ.c,_sV,_sY);}) : (++C,_rp(_sP,_sR,_sZ.a,_t0.a,_t0.b,_t0.c,_sZ.c,_sV,_sY));},_t1=new T(function(){return _rh({_:1,a:_sQ,b:__Z},_qb);});return function(_t2,_t3,_t4,_t5,_t6){return C > 19 ? new F(function(){return _pS(_sT,{_:1,a:{_:1,a:34,b:_t1},b:__Z},_t2,_t3,_t4,_t5,_t6);}) : (++C,_pS(_sT,{_:1,a:{_:1,a:34,b:_t1},b:__Z},_t2,_t3,_t4,_t5,_t6));};},_t7=new T(function(){return _sO(_2F,46);}),_t8=function(_t9,_ta,_tb,_tc,_td){var _te=function(_tf){return C > 19 ? new F(function(){return A1(_tc,function(_tg){return {_:1,a:_tf,b:_tg};});}) : (++C,A1(_tc,function(_tg){return {_:1,a:_tf,b:_tg};}));},_th=function(_ti){return C > 19 ? new F(function(){return A1(_ta,function(_tg){return {_:1,a:_ti,b:_tg};});}) : (++C,A1(_ta,function(_tg){return {_:1,a:_ti,b:_tg};}));};return C > 19 ? new F(function(){return A(_t7,[_t9,_th,_tb,_te,_td]);}) : (++C,A(_t7,[_t9,_th,_tb,_te,_td]));},_tj=new T(function(){return unCStr("Prelude.read: ambiguous parse");}),_tk=new T(function(){return unCStr("Prelude.read: no parse");}),_tl=function(_tm){var _tn=function(_to){return E({_:3,a:_tm,b:_ad});};return {_:1,a:function(_tp){return C > 19 ? new F(function(){return A2(_hX,_tp,_tn);}) : (++C,A2(_hX,_tp,_tn));}};},_tq=function(_tr){while(1){var _ts=(function(_tt){var _tu=E(_tt);if(!_tu._){return __Z;}else{var _tv=_tu.b,_tw=E(_tu.a);if(!E(_tw.b)._){return {_:1,a:_tw.a,b:new T(function(){return _tq(_tv);})};}else{_tr=_tv;return __continue;}}})(_tr);if(_ts!=__continue){return _ts;}}},_tx=function(_ty,_tz,_tA,_tB,_tC){var _tD=function(_tE,_tF,_tG){var _tH=new T(function(){var _tI=_tq(_98(B(A3(_k5,_pd,0,_tl)),new T(function(){return _Q(_ty,_tE);})));if(!_tI._){return err(_tk);}else{if(!E(_tI.b)._){return E(_tI.a);}else{return err(_tj);}}});return C > 19 ? new F(function(){return A3(_tC,_tH,_tF,new T(function(){var _tJ=E(E(_tF).b),_tK=E(_tG),_tL=E(_tK.a),_tM=_6q(_tL.a,_tL.b,_tL.c,_tK.b,_tJ.a,_tJ.b,_tJ.c,__Z);return {_:0,a:E(_tM.a),b:_tM.b};}));}) : (++C,A3(_tC,_tH,_tF,new T(function(){var _tJ=E(E(_tF).b),_tK=E(_tG),_tL=E(_tK.a),_tM=_6q(_tL.a,_tL.b,_tL.c,_tK.b,_tJ.a,_tJ.b,_tJ.c,__Z);return {_:0,a:E(_tM.a),b:_tM.b};})));},_tN=function(_tO){return C > 19 ? new F(function(){return _tD(__Z,_tz,new T(function(){var _tP=E(E(_tz).b),_tQ=E(_tO),_tR=E(_tQ.a),_tS=_6q(_tR.a,_tR.b,_tR.c,_tQ.b,_tP.a,_tP.b,_tP.c,__Z);return {_:0,a:E(_tS.a),b:_tS.b};},1));}) : (++C,_tD(__Z,_tz,new T(function(){var _tP=E(E(_tz).b),_tQ=E(_tO),_tR=E(_tQ.a),_tS=_6q(_tR.a,_tR.b,_tR.c,_tQ.b,_tP.a,_tP.b,_tP.c,__Z);return {_:0,a:E(_tS.a),b:_tS.b};},1)));},_tT=function(_tU,_tV,_tW){var _tX=new T(function(){var _tY=_tq(_98(B(A3(_k5,_pd,0,_tl)),new T(function(){return _Q(_ty,_tU);})));if(!_tY._){return err(_tk);}else{if(!E(_tY.b)._){return E(_tY.a);}else{return err(_tj);}}});return C > 19 ? new F(function(){return A3(_tA,_tX,_tV,new T(function(){var _tZ=E(E(_tV).b),_u0=E(_tW),_u1=E(_u0.a),_u2=_6q(_u1.a,_u1.b,_u1.c,_u0.b,_tZ.a,_tZ.b,_tZ.c,__Z);return {_:0,a:E(_u2.a),b:_u2.b};}));}) : (++C,A3(_tA,_tX,_tV,new T(function(){var _tZ=E(E(_tV).b),_u0=E(_tW),_u1=E(_u0.a),_u2=_6q(_u1.a,_u1.b,_u1.c,_u0.b,_tZ.a,_tZ.b,_tZ.c,__Z);return {_:0,a:E(_u2.a),b:_u2.b};})));};return C > 19 ? new F(function(){return _7q(_t8,_sI,_tz,_tT,_tB,_tD,_tN);}) : (++C,_7q(_t8,_sI,_tz,_tT,_tB,_tD,_tN));},_u3=new T(function(){return _sO(_2F,40);}),_u4=function(_u5,_u6,_u7,_u8,_u9){var _ua=new T(function(){return B(A1(_u8,_h));}),_ub=new T(function(){return B(A1(_u6,_h));});return C > 19 ? new F(function(){return A(_u3,[_u5,function(_uc){return E(_ub);},_u7,function(_ud){return E(_ua);},_u9]);}) : (++C,A(_u3,[_u5,function(_uc){return E(_ub);},_u7,function(_ud){return E(_ua);},_u9]));},_ue=function(_uf,_ug,_uh,_ui,_uj){var _uk=function(_ul){return C > 19 ? new F(function(){return A1(_ui,function(_um){return E(_ul);});}) : (++C,A1(_ui,function(_um){return E(_ul);}));},_un=function(_uo){return C > 19 ? new F(function(){return A1(_ug,function(_up){return E(_uo);});}) : (++C,A1(_ug,function(_up){return E(_uo);}));};return C > 19 ? new F(function(){return _7q(_u4,_uq,_uf,_un,_uh,_uk,_uj);}) : (++C,_7q(_u4,_uq,_uf,_un,_uh,_uk,_uj));},_ur=new T(function(){return _sO(_2F,41);}),_us=function(_ut,_uu,_uv,_uw,_ux){var _uy=function(_uz,_uA,_uB){var _uC=function(_uD,_uE,_uF){return C > 19 ? new F(function(){return A3(_uu,_uD,_uE,new T(function(){return _7i(_uB,_uF);}));}) : (++C,A3(_uu,_uD,_uE,new T(function(){return _7i(_uB,_uF);})));};return C > 19 ? new F(function(){return _tx(_uz,_uA,_uu,_uv,_uC);}) : (++C,_tx(_uz,_uA,_uu,_uv,_uC));},_uG=function(_uH){var _uI=function(_uJ){return C > 19 ? new F(function(){return A1(_ux,new T(function(){return _7i(_uH,_uJ);}));}) : (++C,A1(_ux,new T(function(){return _7i(_uH,_uJ);})));},_uK=function(_uL,_uM,_uN){var _uO=function(_uP,_uQ,_uR){return C > 19 ? new F(function(){return A3(_uw,_uP,_uQ,new T(function(){var _uS=E(_uH),_uT=E(_uS.a),_uU=E(_uN),_uV=E(_uU.a),_uW=E(_uR),_uX=E(_uW.a),_uY=_6q(_uV.a,_uV.b,_uV.c,_uU.b,_uX.a,_uX.b,_uX.c,_uW.b),_uZ=E(_uY.a),_v0=_6q(_uT.a,_uT.b,_uT.c,_uS.b,_uZ.a,_uZ.b,_uZ.c,_uY.b);return {_:0,a:E(_v0.a),b:_v0.b};}));}) : (++C,A3(_uw,_uP,_uQ,new T(function(){var _uS=E(_uH),_uT=E(_uS.a),_uU=E(_uN),_uV=E(_uU.a),_uW=E(_uR),_uX=E(_uW.a),_uY=_6q(_uV.a,_uV.b,_uV.c,_uU.b,_uX.a,_uX.b,_uX.c,_uW.b),_uZ=E(_uY.a),_v0=_6q(_uT.a,_uT.b,_uT.c,_uS.b,_uZ.a,_uZ.b,_uZ.c,_uY.b);return {_:0,a:E(_v0.a),b:_v0.b};})));};return C > 19 ? new F(function(){return _tx(_uL,_uM,_uu,_uv,_uO);}) : (++C,_tx(_uL,_uM,_uu,_uv,_uO));};return C > 19 ? new F(function(){return _rZ(_rT,_ut,_uy,_uv,_uK,_uI);}) : (++C,_rZ(_rT,_ut,_uy,_uv,_uK,_uI));};return C > 19 ? new F(function(){return _7q(_ue,_ur,_ut,_uu,_uv,_uw,_uG);}) : (++C,_7q(_ue,_ur,_ut,_uu,_uv,_uw,_uG));},_v1=function(_v2,_v3,_v4,_v5,_v6){var _v7=function(_v8){return C > 19 ? new F(function(){return A3(_v6,0,_v3,new T(function(){var _v9=E(E(_v3).b),_va=E(_v8),_vb=E(_va.a),_vc=_6q(_vb.a,_vb.b,_vb.c,_va.b,_v9.a,_v9.b,_v9.c,__Z);return {_:0,a:E(_vc.a),b:_vc.b};}));}) : (++C,A3(_v6,0,_v3,new T(function(){var _v9=E(E(_v3).b),_va=E(_v8),_vb=E(_va.a),_vc=_6q(_vb.a,_vb.b,_vb.c,_va.b,_v9.a,_v9.b,_v9.c,__Z);return {_:0,a:E(_vc.a),b:_vc.b};})));},_vd=function(_ve,_vf,_vg){return C > 19 ? new F(function(){return _vh(__Z,_vf);}) : (++C,_vh(__Z,_vf));},_vh=function(_vi,_vj){var _vk=function(_vl){return C > 19 ? new F(function(){return A3(_v4,0,_vj,new T(function(){var _vm=E(E(_vj).b),_vn=E(_vl),_vo=E(_vn.a),_vp=_6q(_vo.a,_vo.b,_vo.c,_vn.b,_vm.a,_vm.b,_vm.c,__Z);return {_:0,a:E(_vp.a),b:_vp.b};}));}) : (++C,A3(_v4,0,_vj,new T(function(){var _vm=E(E(_vj).b),_vn=E(_vl),_vo=E(_vn.a),_vp=_6q(_vo.a,_vo.b,_vo.c,_vn.b,_vm.a,_vm.b,_vm.c,__Z);return {_:0,a:E(_vp.a),b:_vp.b};})));};return C > 19 ? new F(function(){return A(_v2,[_vj,new T(function(){var _vq=E(_vi);return _vd;}),_v5,_6L,_vk]);}) : (++C,A(_v2,[_vj,new T(function(){var _vq=E(_vi);return _vd;}),_v5,_6L,_vk]));};return C > 19 ? new F(function(){return A(_v2,[_v3,function(_vr,_vs,_vt){return C > 19 ? new F(function(){return _vh(__Z,_vs);}) : (++C,_vh(__Z,_vs));},_v5,_6L,_v7]);}) : (++C,A(_v2,[_v3,function(_vr,_vs,_vt){return C > 19 ? new F(function(){return _vh(__Z,_vs);}) : (++C,_vh(__Z,_vs));},_v5,_6L,_v7]));},_vu=function(_vv){var _vw=_vv>>>0;if(_vw>887){var _vx=u_iswspace(_vv);return (E(_vx)==0)?false:true;}else{return (_vw==32)?true:(_vw-9>>>0>4)?(_vw==160)?true:false:true;}},_vy=function(_vz){return _vu(E(_vz));},_vA=new T(function(){return unCStr("space");}),_vB=function(_vC,_vD,_vE,_vF,_vG,_vH){return C > 19 ? new F(function(){return _pS(function(_vI,_vJ,_vK,_vL,_vM){var _vN=E(_vI),_vO=E(_vN.b);return C > 19 ? new F(function(){return _rp(_vC,_vy,_vN.a,_vO.a,_vO.b,_vO.c,_vN.c,_vJ,_vM);}) : (++C,_rp(_vC,_vy,_vN.a,_vO.a,_vO.b,_vO.c,_vN.c,_vJ,_vM));},{_:1,a:_vA,b:__Z},_vD,_vE,_vF,_vG,_vH);}) : (++C,_pS(function(_vI,_vJ,_vK,_vL,_vM){var _vN=E(_vI),_vO=E(_vN.b);return C > 19 ? new F(function(){return _rp(_vC,_vy,_vN.a,_vO.a,_vO.b,_vO.c,_vN.c,_vJ,_vM);}) : (++C,_rp(_vC,_vy,_vN.a,_vO.a,_vO.b,_vO.c,_vN.c,_vJ,_vM));},{_:1,a:_vA,b:__Z},_vD,_vE,_vF,_vG,_vH));},_vP=new T(function(){return unCStr("white space");}),_vQ=function(_vR,_vS,_vT,_vU,_vV,_vW){var _vX=function(_vY,_vZ,_w0,_w1,_w2){return C > 19 ? new F(function(){return _v1(function(_w3,_w4,_w5,_w6,_w7){return C > 19 ? new F(function(){return _vB(_vR,_w3,_w4,_w5,_w6,_w7);}) : (++C,_vB(_vR,_w3,_w4,_w5,_w6,_w7));},_vY,_vZ,_w0,_w1);}) : (++C,_v1(function(_w3,_w4,_w5,_w6,_w7){return C > 19 ? new F(function(){return _vB(_vR,_w3,_w4,_w5,_w6,_w7);}) : (++C,_vB(_vR,_w3,_w4,_w5,_w6,_w7));},_vY,_vZ,_w0,_w1));};return C > 19 ? new F(function(){return _pS(_vX,{_:1,a:_vP,b:__Z},_vS,_vT,_vU,_vV,_vW);}) : (++C,_pS(_vX,{_:1,a:_vP,b:__Z},_vS,_vT,_vU,_vV,_vW));},_w8=function(_w9,_wa,_wb,_wc,_wd){var _we=new T(function(){return B(A1(_wc,_h));}),_wf=new T(function(){return B(A1(_wa,_h));});return C > 19 ? new F(function(){return _vQ(_2F,_w9,function(_wg){return E(_wf);},_wb,function(_wh){return E(_we);},_wd);}) : (++C,_vQ(_2F,_w9,function(_wg){return E(_wf);},_wb,function(_wh){return E(_we);},_wd));},_wi=function(_wj,_wk,_wl,_wm,_wn){var _wo=function(_wp){return C > 19 ? new F(function(){return A1(_wm,function(_wq){return E(_wp);});}) : (++C,A1(_wm,function(_wq){return E(_wp);}));},_wr=function(_ws){return C > 19 ? new F(function(){return A1(_wk,function(_wt){return E(_ws);});}) : (++C,A1(_wk,function(_wt){return E(_ws);}));};return C > 19 ? new F(function(){return _7q(_w8,_us,_wj,_wr,_wl,_wo,_wn);}) : (++C,_7q(_w8,_us,_wj,_wr,_wl,_wo,_wn));},_wu=function(_wv,_ww,_wx,_wy,_tg){return C > 19 ? new F(function(){return _vQ(_2F,_wv,_ww,_wx,_wy,_tg);}) : (++C,_vQ(_2F,_wv,_ww,_wx,_wy,_tg));},_wz=function(_wA,_wB,_wC,_wD,_wE){return C > 19 ? new F(function(){return _7q(_wi,_wu,_wA,_wB,_wC,_wD,_wE);}) : (++C,_7q(_wi,_wu,_wA,_wB,_wC,_wD,_wE));},_wF=new T(function(){return _sO(_2F,47);}),_wG=function(_wH,_wI,_wJ,_wK,_wL){var _wM=new T(function(){return B(A1(_wK,_h));}),_wN=new T(function(){return B(A1(_wI,_h));});return C > 19 ? new F(function(){return A(_wF,[_wH,function(_wO){return E(_wN);},_wJ,function(_wP){return E(_wM);},_wL]);}) : (++C,A(_wF,[_wH,function(_wO){return E(_wN);},_wJ,function(_wP){return E(_wM);},_wL]));},_wQ=new T(function(){return _sO(_2F,42);}),_wR=function(_wS,_wT,_wU,_wV,_wW){var _wX=new T(function(){return B(A1(_wV,_h));}),_wY=new T(function(){return B(A1(_wT,_h));});return C > 19 ? new F(function(){return A(_wQ,[_wS,function(_wZ){return E(_wY);},_wU,function(_x0){return E(_wX);},_wW]);}) : (++C,A(_wQ,[_wS,function(_wZ){return E(_wY);},_wU,function(_x0){return E(_wX);},_wW]));},_x1=function(_x2,_x3){return E(_x2)/E(_x3);},_x4=function(_x5,_x6){return E(_x5)*E(_x6);},_x7=function(_x8,_x9,_xa,_xb,_xc){var _xd=function(_xe){return C > 19 ? new F(function(){return A1(_x9,function(_xf){return _x1(_xf,_xe);});}) : (++C,A1(_x9,function(_xf){return _x1(_xf,_xe);}));},_xg=function(_xh){var _xi=function(_xj){return C > 19 ? new F(function(){return A1(_xc,new T(function(){return _7i(_xh,_xj);}));}) : (++C,A1(_xc,new T(function(){return _7i(_xh,_xj);})));},_xk=function(_xl,_xm,_xn){return C > 19 ? new F(function(){return A3(_xb,function(_xo){return _x1(_xo,_xl);},_xm,new T(function(){return _7i(_xh,_xn);}));}) : (++C,A3(_xb,function(_xo){return _x1(_xo,_xl);},_xm,new T(function(){return _7i(_xh,_xn);})));};return C > 19 ? new F(function(){return _7q(_wG,_wz,_x8,_xd,_xa,_xk,_xi);}) : (++C,_7q(_wG,_wz,_x8,_xd,_xa,_xk,_xi));},_xp=function(_xq){return C > 19 ? new F(function(){return A1(_xb,function(_tg){return _x4(_xq,_tg);});}) : (++C,A1(_xb,function(_tg){return _x4(_xq,_tg);}));},_xr=function(_xs){return C > 19 ? new F(function(){return A1(_x9,function(_tg){return _x4(_xs,_tg);});}) : (++C,A1(_x9,function(_tg){return _x4(_xs,_tg);}));};return C > 19 ? new F(function(){return _7q(_wR,_wz,_x8,_xr,_xa,_xp,_xg);}) : (++C,_7q(_wR,_wz,_x8,_xr,_xa,_xp,_xg));},_xt=function(_xu,_xv,_xw,_xx,_xy){var _xz=function(_xA){return C > 19 ? new F(function(){return A1(_xy,new T(function(){return _8f(_xA,E(_xu));}));}) : (++C,A1(_xy,new T(function(){return _8f(_xA,E(_xu));})));},_xB=function(_xC){return C > 19 ? new F(function(){return A1(_xw,new T(function(){return _8k(_xC,E(_xu));}));}) : (++C,A1(_xw,new T(function(){return _8k(_xC,E(_xu));})));};return C > 19 ? new F(function(){return _6M(_x7,_xv,_xB,_xx,_xz);}) : (++C,_6M(_x7,_xv,_xB,_xx,_xz));},_xD=function(_xE,_xF,_xG,_xH,_xI){var _xJ=function(_xK,_xL,_xM){var _xN=function(_xO,_xP,_xQ){return C > 19 ? new F(function(){return A3(_xH,_xO,_xP,new T(function(){return _7i(_xM,_xQ);}));}) : (++C,A3(_xH,_xO,_xP,new T(function(){return _7i(_xM,_xQ);})));};return C > 19 ? new F(function(){return _xt(_xK,_xL,_xF,_xG,_xN);}) : (++C,_xt(_xK,_xL,_xF,_xG,_xN));},_xR=function(_xS,_xT,_xU){var _xV=function(_xW,_xX,_xY){return C > 19 ? new F(function(){return A3(_xF,_xW,_xX,new T(function(){return _7i(_xU,_xY);}));}) : (++C,A3(_xF,_xW,_xX,new T(function(){return _7i(_xU,_xY);})));};return C > 19 ? new F(function(){return _xt(_xS,_xT,_xF,_xG,_xV);}) : (++C,_xt(_xS,_xT,_xF,_xG,_xV));};return C > 19 ? new F(function(){return _7q(_wi,_wu,_xE,_xR,_xG,_xJ,_xI);}) : (++C,_7q(_wi,_wu,_xE,_xR,_xG,_xJ,_xI));},_xZ=function(_y0){return  -E(_y0);},_y1=function(_y2,_y3,_y4,_y5,_y6){var _y7=function(_y8){return C > 19 ? new F(function(){return A1(_y5,new T(function(){return _xZ(_y8);}));}) : (++C,A1(_y5,new T(function(){return _xZ(_y8);})));},_y9=function(_ya){return C > 19 ? new F(function(){return A1(_y3,new T(function(){return _xZ(_ya);}));}) : (++C,A1(_y3,new T(function(){return _xZ(_ya);})));};return C > 19 ? new F(function(){return _xD(_y2,_y9,_y4,_y7,_y6);}) : (++C,_xD(_y2,_y9,_y4,_y7,_y6));},_yb=new T(function(){return _sO(_2F,45);}),_yc=function(_yd,_ye,_yf,_yg,_yh){var _yi=new T(function(){return B(A1(_yg,_h));}),_yj=new T(function(){return B(A1(_ye,_h));});return C > 19 ? new F(function(){return A(_yb,[_yd,function(_yk){return E(_yj);},_yf,function(_yl){return E(_yi);},_yh]);}) : (++C,A(_yb,[_yd,function(_yk){return E(_yj);},_yf,function(_yl){return E(_yi);},_yh]));},_ym=new T(function(){return _sO(_2F,43);}),_yn=function(_yo,_yp,_yq,_yr,_ys){var _yt=new T(function(){return B(A1(_yr,_h));}),_yu=new T(function(){return B(A1(_yp,_h));});return C > 19 ? new F(function(){return A(_ym,[_yo,function(_yv){return E(_yu);},_yq,function(_yw){return E(_yt);},_ys]);}) : (++C,A(_ym,[_yo,function(_yv){return E(_yu);},_yq,function(_yw){return E(_yt);},_ys]));},_yx=function(_yy,_yz,_yA,_yB,_yC){var _yD=function(_yE){var _yF=function(_yG){return C > 19 ? new F(function(){return A1(_yC,new T(function(){return _7i(_yE,_yG);}));}) : (++C,A1(_yC,new T(function(){return _7i(_yE,_yG);})));},_yH=function(_yI,_yJ,_yK){return C > 19 ? new F(function(){return A3(_yB,_yI,_yJ,new T(function(){return _7i(_yE,_yK);}));}) : (++C,A3(_yB,_yI,_yJ,new T(function(){return _7i(_yE,_yK);})));};return C > 19 ? new F(function(){return _7q(_yc,_y1,_yy,_yz,_yA,_yH,_yF);}) : (++C,_7q(_yc,_y1,_yy,_yz,_yA,_yH,_yF));};return C > 19 ? new F(function(){return _7q(_yn,_xD,_yy,_yz,_yA,_yB,_yD);}) : (++C,_7q(_yn,_xD,_yy,_yz,_yA,_yB,_yD));},_yL=function(_yM,_yN){while(1){var _yO=E(_yM);if(!_yO._){return E(_yN);}else{var _yP=_yN+E(_yO.a);_yM=_yO.b;_yN=_yP;continue;}}},_yQ=function(_yR,_yS,_yT){return _yL(_yS,_yT+E(_yR));},_yU=function(_yV,_yW,_yX,_yY,_yZ){var _z0=function(_z1){return C > 19 ? new F(function(){return A1(_yZ,new T(function(){return _yQ(_yV,_z1,0);}));}) : (++C,A1(_yZ,new T(function(){return _yQ(_yV,_z1,0);})));},_z2=function(_z3){return C > 19 ? new F(function(){return A1(_yX,new T(function(){return _yQ(_yV,_z3,0);}));}) : (++C,A1(_yX,new T(function(){return _yQ(_yV,_z3,0);})));};return C > 19 ? new F(function(){return _6M(_yx,_yW,_z2,_yY,_z0);}) : (++C,_6M(_yx,_yW,_z2,_yY,_z0));},_uq=function(_z4,_z5,_z6,_z7,_z8){var _z9=function(_za,_zb,_zc){var _zd=function(_ze,_zf,_zg){return C > 19 ? new F(function(){return A3(_z7,_ze,_zf,new T(function(){return _7i(_zc,_zg);}));}) : (++C,A3(_z7,_ze,_zf,new T(function(){return _7i(_zc,_zg);})));};return C > 19 ? new F(function(){return _yU(_za,_zb,_z5,_z6,_zd);}) : (++C,_yU(_za,_zb,_z5,_z6,_zd));},_zh=function(_zi,_zj,_zk){var _zl=function(_zm,_zn,_zo){return C > 19 ? new F(function(){return A3(_z5,_zm,_zn,new T(function(){return _7i(_zk,_zo);}));}) : (++C,A3(_z5,_zm,_zn,new T(function(){return _7i(_zk,_zo);})));};return C > 19 ? new F(function(){return _yU(_zi,_zj,_z5,_z6,_zl);}) : (++C,_yU(_zi,_zj,_z5,_z6,_zl));};return C > 19 ? new F(function(){return _xD(_z4,_zh,_z6,_z9,_z8);}) : (++C,_xD(_z4,_zh,_z6,_z9,_z8));},_zp=(function(e,p){return e[p].toString();}),_zq=(function(e,p,v){e[p] = v;}),_zr=new T(function(){return unCStr("textContent");}),_zs=new T(function(){return _21({_:0,a:__Z,b:7,c:__Z,d:new T(function(){return unCStr("Pattern match failure in do expression at src/Calc.hs:9:5-14");}),e:__Z,f:__Z});}),_zt=new T(function(){return _21({_:0,a:__Z,b:7,c:__Z,d:new T(function(){return unCStr("Pattern match failure in do expression at src/Calc.hs:10:5-15");}),e:__Z,f:__Z});}),_zu=function(_zv){return E(E(_zv).a);},_zw=function(_zx){return E(E(_zx).a);},_zy=function(_zz){return E(E(_zz).a);},_zA=function(_zB){return E(E(_zB).b);},_zC=function(_zD){return E(E(_zD).a);},_zE=new T(function(){return _67(function(_){return nMV(__Z);});}),_zF=(function(e,name,f){e.addEventListener(name,f,false);return [f];}),_zG=function(_zH){return E(E(_zH).b);},_zI=function(_zJ){return E(E(_zJ).d);},_zK=function(_zL,_zM,_zN,_zO,_zP,_zQ){var _zR=_zu(_zL),_zS=_zw(_zR),_zT=new T(function(){return _6b(_zR);}),_zU=new T(function(){return _zI(_zS);}),_zV=new T(function(){return B(A2(_zy,_zM,_zO));}),_zW=new T(function(){return B(A2(_zC,_zN,_zP));}),_zX=function(_zY){return C > 19 ? new F(function(){return A1(_zU,{_:0,a:_zW,b:_zV,c:_zY});}) : (++C,A1(_zU,{_:0,a:_zW,b:_zV,c:_zY}));},_zZ=function(_A0){var _A1=new T(function(){var _A2=new T(function(){var _A3=__createJSFunc(2,function(_A4,_){var _A5=B(A2(E(_A0),_A4,_));return _6a;}),_A6=_A3;return function(_){return _zF(E(_zV),E(_zW),_A6);};});return B(A1(_zT,_A2));});return C > 19 ? new F(function(){return A3(_2n,_zS,_A1,_zX);}) : (++C,A3(_2n,_zS,_A1,_zX));},_A7=new T(function(){var _A8=new T(function(){return _6b(_zR);}),_A9=function(_Aa){var _Ab=new T(function(){return B(A1(_A8,function(_){var _=wMV(E(_zE),{_:1,a:_Aa});return C > 19 ? new F(function(){return A(_zA,[_zN,_zP,_Aa,_]);}) : (++C,A(_zA,[_zN,_zP,_Aa,_]));}));});return C > 19 ? new F(function(){return A3(_2n,_zS,_Ab,_zQ);}) : (++C,A3(_2n,_zS,_Ab,_zQ));};return B(A2(_zG,_zL,_A9));});return C > 19 ? new F(function(){return A3(_2n,_zS,_A7,_zZ);}) : (++C,A3(_2n,_zS,_A7,_zZ));},_Ac=function(_Ad,_Ae,_Af){return {_:0,a:_Ad,b:E(_Ae),c:_Af};},_Ag=function(_Ah,_Ai,_Aj){var _Ak=new T(function(){return _zI(_Ah);}),_Al=new T(function(){return _zI(_Ah);}),_Am=function(_An){return C > 19 ? new F(function(){return A1(_Al,new T(function(){return {_:1,a:E(B(A1(_Ak,{_:1,a:_An})))};}));}) : (++C,A1(_Al,new T(function(){return {_:1,a:E(B(A1(_Ak,{_:1,a:_An})))};})));},_Ao=function(_Ap,_Aq,_Ar){var _As=new T(function(){return {_:1,a:E(B(A1(_Ak,new T(function(){return _Ac(_Ap,_Aq,_Ar);}))))};});return C > 19 ? new F(function(){return A1(_Al,_As);}) : (++C,A1(_Al,_As));},_At=function(_Au){return C > 19 ? new F(function(){return A1(_Al,{_:0,a:new T(function(){return B(A1(_Ak,{_:1,a:_Au}));})});}) : (++C,A1(_Al,{_:0,a:new T(function(){return B(A1(_Ak,{_:1,a:_Au}));})}));},_Av=function(_Aw,_Ax,_Ay){var _Az=new T(function(){return B(A1(_Ak,new T(function(){return _Ac(_Aw,_Ax,_Ay);})));});return C > 19 ? new F(function(){return A1(_Al,{_:0,a:_Az});}) : (++C,A1(_Al,{_:0,a:_Az}));};return C > 19 ? new F(function(){return A(_Ai,[_Aj,_Av,_At,_Ao,_Am]);}) : (++C,A(_Ai,[_Aj,_Av,_At,_Ao,_Am]));},_AA=function(_AB,_AC,_AD,_AE,_AF){var _AG=_q9(_AB),_AH=function(_AI){var _AJ=E(_AI);if(!_AJ._){return C > 19 ? new F(function(){return A2(_zI,_AG,{_:1,a:_AJ.a});}) : (++C,A2(_zI,_AG,{_:1,a:_AJ.a}));}else{return C > 19 ? new F(function(){return A2(_zI,_AG,{_:0,a:_AJ.a});}) : (++C,A2(_zI,_AG,{_:0,a:_AJ.a}));}},_AK=function(_AL){return C > 19 ? new F(function(){return A3(_2n,_AG,new T(function(){var _AM=E(_AL);if(!_AM._){return E(_AM.a);}else{return E(_AM.a);}}),_AH);}) : (++C,A3(_2n,_AG,new T(function(){var _AM=E(_AL);if(!_AM._){return E(_AM.a);}else{return E(_AM.a);}}),_AH));},_AN=new T(function(){return B(_Ag(_AG,_AC,new T(function(){return {_:0,a:_AF,b:E({_:0,a:_AE,b:1,c:1}),c:E(_AD)};})));});return C > 19 ? new F(function(){return A3(_2n,_AG,_AN,_AK);}) : (++C,A3(_2n,_AG,_AN,_AK));},_AO=function(_){var _AP=B(A3(_6d,_2a,"calcInput",_)),_AQ=E(_AP);if(!_AQ._){return die(_zs);}else{var _AR=_AQ.a,_AS=B(A3(_6d,_2a,"output",_)),_AT=E(_AS);if(!_AT._){return die(_zt);}else{var _AU=_AT.a,_AV=function(_AW,_){var _AX=_zp(E(_AR),"value"),_AY=B(_AA(_2F,_uq,0,__Z,new T(function(){var _AZ=String(_AX);return fromJSStr(_AZ);})));if(!_AY._){var _B0=E(_AY.a),_B1=E(_B0.a),_B2=_zq(E(_AU),toJSStr(E(_zr)),toJSStr(_60(_B1.a,_B1.b,_B1.c,_B0.b)));return _e(_);}else{var _B3=jsShow(E(_AY.a)),_B4=_zq(E(_AU),toJSStr(E(_zr)),toJSStr(fromJSStr(_B3)));return _e(_);}};return C > 19 ? new F(function(){return A(_zK,[{_:0,a:_2a,b:_s},{_:0,a:_h,b:_f},{_:0,a:_c,b:_9},_AR,1,_AV,_]);}) : (++C,A(_zK,[{_:0,a:_2a,b:_s},{_:0,a:_h,b:_f},{_:0,a:_c,b:_9},_AR,1,_AV,_]));}}},_B5=function(_){return C > 19 ? new F(function(){return _AO(_);}) : (++C,_AO(_));};
var hasteMain = function() {B(A(_B5, [0]));};window.onload = hasteMain;