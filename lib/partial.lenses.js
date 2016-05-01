"use strict";

Object.defineProperty(exports, "__esModule", {
  value: true
});
exports.sequence = exports.log = exports.props = exports.identity = exports.pick = exports.augment = exports.filter = exports.append = exports.index = exports.findWith = exports.find = exports.prop = exports.normalize = exports.define = exports.required = exports.defaults = exports.replace = exports.choice = exports.orElse = exports.nothing = exports.choose = exports.just = exports.chain = exports.get = exports.set = exports.modify = exports.lens = exports.removeAll = exports.remove = exports.compose = exports.toRamda = exports.fromRamda = undefined;

var _extends = Object.assign || function (target) { for (var i = 1; i < arguments.length; i++) { var source = arguments[i]; for (var key in source) { if (Object.prototype.hasOwnProperty.call(source, key)) { target[key] = source[key]; } } } return target; };

var _ramda = require("ramda");

var R = _interopRequireWildcard(_ramda);

function _interopRequireWildcard(obj) { if (obj && obj.__esModule) { return obj; } else { var newObj = {}; if (obj != null) { for (var key in obj) { if (Object.prototype.hasOwnProperty.call(obj, key)) newObj[key] = obj[key]; } } newObj.default = obj; return newObj; } }

function _toConsumableArray(arr) { if (Array.isArray(arr)) { for (var i = 0, arr2 = Array(arr.length); i < arr.length; i++) { arr2[i] = arr[i]; } return arr2; } else { return Array.from(arr); } }

function _defineProperty(obj, key, value) { if (key in obj) { Object.defineProperty(obj, key, { value: value, enumerable: true, configurable: true, writable: true }); } else { obj[key] = value; } return obj; }

//

function Identity(value) {
  this.value = value;
}
var Ident = function Ident(x) {
  return new Identity(x);
};
Identity.prototype.map = function (x2y) {
  return new Identity(x2y(this.value));
};
Identity.prototype.of = Ident;
Identity.prototype.ap = function (x) {
  return new Identity(this.value(x.value));
};

//

function Constant(value) {
  this.value = value;
}
var Const = function Const(x) {
  return new Constant(x);
};
Constant.prototype.map = function () {
  return this;
};
Constant.prototype.of = Const;

//

var warned = {};

var warn = function warn(message) {
  if (!(message in warned)) {
    warned[message] = message;
    console.warn("partial.lenses:", message);
  }
};

//

var id = function id(x) {
  return x;
};
var snd = function snd(_, c) {
  return c;
};

//

var check = function check(expected, predicate) {
  return function (x) {
    if (predicate(x)) return x;else throw new Error("Expected " + expected + ", but got " + x + ".");
  };
};

var assert = process.env.NODE_ENV === "production" ? function () {
  return id;
} : check;

//

var empty = {};

var deleteKey = function deleteKey(k, o) {
  if (o === undefined || !(k in o)) return o;
  var r = void 0;
  for (var p in o) {
    if (p !== k) {
      if (undefined === r) r = {};
      r[p] = o[p];
    }
  }
  return r;
};

var setKey = function setKey(k, v, o) {
  if (o === undefined) return _defineProperty({}, k, v);
  if (k in o && R.equals(v, o[k])) return o;
  var r = _defineProperty({}, k, v);
  for (var p in o) {
    if (p !== k) r[p] = o[p];
  }return r;
};

//

var dropped = function dropped(xs) {
  return Object.keys(xs).length === 0 ? undefined : xs;
};

//

var toPartial = function toPartial(transform) {
  return function (x) {
    return undefined === x ? x : transform(x);
  };
};

//

var conserve = function conserve(c1, c0) {
  return R.equals(c1, c0) ? c0 : c1;
};

var toConserve = function toConserve(f) {
  return function (y, c0) {
    return conserve(f(y, c0), c0);
  };
};

//

var seemsLens = function seemsLens(x) {
  return typeof x === "function" && x.length === 1;
};

var fromRamda = exports.fromRamda = assert("a lens", seemsLens);

var toRamda = exports.toRamda = function toRamda(l) {
  if (isProp(l)) return toRamdaProp(l);
  if (isIndex(l)) return toRamdaIndex(l);
  return fromRamda(l);
};

var compose = exports.compose = function compose() {
  for (var _len = arguments.length, ls = Array(_len), _key = 0; _key < _len; _key++) {
    ls[_key] = arguments[_key];
  }

  return ls.length === 0 ? identity : ls.length === 1 ? ls[0] : R.compose.apply(R, _toConsumableArray(ls.map(toRamda)));
};

var remove = exports.remove = R.curry(function (l, s) {
  return setI(toRamda(l), undefined, s);
});

var removeAll = exports.removeAll = R.curry(function (lens, data) {
  warn("`removeAll` is deprecated and will be removed in next major version --- use a different approach.");
  while (get(lens, data) !== undefined) {
    data = remove(lens, data);
  }return data;
});

var setI = function setI(l, x, s) {
  return l(function () {
    return Ident(x);
  })(s).value;
};
var getI = function getI(l, s) {
  return l(Const)(s).value;
};
var modifyI = function modifyI(l, x2x, s) {
  return l(function (y) {
    return Ident(x2x(y));
  })(s).value;
};
var lensI = function lensI(getter, setter) {
  return function (toFn) {
    return function (target) {
      return toFn(getter(target)).map(function (focus) {
        return setter(focus, target);
      });
    };
  };
};

var lens = exports.lens = R.curry(lensI);
var modify = exports.modify = R.curry(function (l, x2x, s) {
  return modifyI(toRamda(l), x2x, s);
});
var set = exports.set = R.curry(function (l, x, s) {
  return setI(toRamda(l), x, s);
});
var get = exports.get = R.curry(function (l, s) {
  return getI(toRamda(l), s);
});

var chain = exports.chain = R.curry(function (x2yL, xL) {
  return compose(xL, choose(function (xO) {
    return xO === undefined ? nothing : x2yL(xO);
  }));
});

var just = exports.just = function just(x) {
  return lensI(R.always(x), snd);
};

var choose = exports.choose = function choose(x2yL) {
  return function (toFunctor) {
    return function (target) {
      var l = toRamda(x2yL(target));
      return R.map(function (focus) {
        return setI(l, focus, target);
      }, toFunctor(getI(l, target)));
    };
  };
};

var nothing = exports.nothing = lensI(snd, snd);

var orElse = exports.orElse = R.curry(function (d, l) {
  return choose(function (x) {
    return getI(toRamda(l), x) !== undefined ? l : d;
  });
});

var choice = exports.choice = function choice() {
  for (var _len2 = arguments.length, ls = Array(_len2), _key2 = 0; _key2 < _len2; _key2++) {
    ls[_key2] = arguments[_key2];
  }

  return choose(function (x) {
    var i = ls.findIndex(function (l) {
      return getI(toRamda(l), x) !== undefined;
    });
    return 0 <= i ? ls[i] : nothing;
  });
};

var replace = exports.replace = R.curry(function (inn, out) {
  return lensI(function (x) {
    return R.equals(x, inn) ? out : x;
  }, toConserve(function (y) {
    return R.equals(y, out) ? inn : y;
  }));
});

var defaults = exports.defaults = replace(undefined);
var required = exports.required = function required(inn) {
  return replace(inn, undefined);
};
var define = exports.define = function define(v) {
  return R.compose(required(v), defaults(v));
};

var normalize = exports.normalize = function normalize(transform) {
  return lensI(toPartial(transform), toConserve(toPartial(transform)));
};

var isProp = function isProp(x) {
  return typeof x === "string";
};

var prop = exports.prop = assert("a string", isProp);

var toRamdaProp = function toRamdaProp(k) {
  return lensI(function (o) {
    return o && o[k];
  }, function (v, o) {
    return v === undefined ? deleteKey(k, o) : setKey(k, v, o);
  });
};

var find = exports.find = function find(predicate) {
  return choose(function (xs) {
    if (xs === undefined) return append;
    var i = xs.findIndex(predicate);
    return i < 0 ? append : i;
  });
};

var findWith = exports.findWith = function findWith() {
  var lls = toRamda(compose.apply(undefined, arguments));
  return compose(find(function (x) {
    return getI(lls, x) !== undefined;
  }), lls);
};

var isIndex = function isIndex(x) {
  return Number.isInteger(x) && 0 <= x;
};

var index = exports.index = assert("a non-negative integer", isIndex);

var toRamdaIndex = function toRamdaIndex(i) {
  return lensI(function (xs) {
    return xs && xs[i];
  }, function (x, xs) {
    if (x === undefined) {
      if (xs === undefined) return undefined;
      if (i < xs.length) return dropped(xs.slice(0, i).concat(xs.slice(i + 1)));
      return xs;
    } else {
      if (xs === undefined) return Array(i).concat([x]);
      if (xs.length <= i) return xs.concat(Array(i - xs.length), [x]);
      if (R.equals(x, xs[i])) return xs;
      return xs.slice(0, i).concat([x], xs.slice(i + 1));
    }
  });
};

var append = exports.append = lensI(snd, function (x, xs) {
  return x === undefined ? xs : xs === undefined ? [x] : xs.concat([x]);
});

var filter = exports.filter = function filter(p) {
  return lensI(function (xs) {
    return xs && xs.filter(p);
  }, function (ys, xs) {
    return conserve(dropped(R.concat(ys || [], (xs || []).filter(R.complement(p)))), xs);
  });
};

var augment = exports.augment = function augment(template) {
  return lensI(toPartial(function (x) {
    var z = _extends({}, x);
    for (var k in template) {
      z[k] = template[k](x);
    }return z;
  }), toConserve(function (y, c) {
    if (y === undefined) return undefined;
    var z = void 0;
    var set = function set(k, v) {
      if (undefined === z) z = {};
      z[k] = v;
    };
    for (var k in y) {
      if (!(k in template)) set(k, y[k]);else if (k in c) set(k, c[k]);
    }
    return z;
  }));
};

var pick = exports.pick = function pick(template) {
  return lensI(function (c) {
    var r = void 0;
    for (var k in template) {
      var v = getI(toRamda(template[k]), c);
      if (v !== undefined) {
        if (r === undefined) r = {};
        r[k] = v;
      }
    }
    return r;
  }, function () {
    var o = arguments.length <= 0 || arguments[0] === undefined ? empty : arguments[0];
    var cIn = arguments[1];

    var c = cIn;
    for (var k in template) {
      c = setI(toRamda(template[k]), o[k], c);
    }return c;
  });
};

var identity = exports.identity = lensI(id, conserve);

var props = exports.props = function props() {
  for (var _len3 = arguments.length, ks = Array(_len3), _key3 = 0; _key3 < _len3; _key3++) {
    ks[_key3] = arguments[_key3];
  }

  return pick(R.zipObj(ks, ks));
};

var show = function show() {
  for (var _len4 = arguments.length, labels = Array(_len4), _key4 = 0; _key4 < _len4; _key4++) {
    labels[_key4] = arguments[_key4];
  }

  return function (x) {
    var _console;

    return (_console = console).log.apply(_console, labels.concat([x])) || x;
  };
};

var log = exports.log = function log() {
  for (var _len5 = arguments.length, labels = Array(_len5), _key5 = 0; _key5 < _len5; _key5++) {
    labels[_key5] = arguments[_key5];
  }

  return lensI(show.apply(undefined, labels.concat(["get"])), show.apply(undefined, labels.concat(["set"])));
};

var sequence = exports.sequence = function sequence(toApplicative) {
  return function (target) {
    return warn("`sequence` is experimental and might be removed, renamed or changed semantically before next major release") || R.sequence(Ident, R.map(toApplicative, target)).map(R.pipe(R.filter(function (x) {
      return x !== undefined;
    }), dropped));
  };
};

exports.default = compose;
//# sourceMappingURL=data:application/json;base64,eyJ2ZXJzaW9uIjozLCJzb3VyY2VzIjpbIi4uL3NyYy9wYXJ0aWFsLmxlbnNlcy5qcyJdLCJuYW1lcyI6W10sIm1hcHBpbmdzIjoiOzs7Ozs7Ozs7QUFBQTs7SUFBWSxDOzs7Ozs7Ozs7O0FBSVosU0FBUyxRQUFULENBQWtCLEtBQWxCLEVBQXlCO0FBQUMsT0FBSyxLQUFMLEdBQWEsS0FBYjtBQUFtQjtBQUM3QyxJQUFNLFFBQVEsU0FBUixLQUFRO0FBQUEsU0FBSyxJQUFJLFFBQUosQ0FBYSxDQUFiLENBQUw7QUFBQSxDQUFkO0FBQ0EsU0FBUyxTQUFULENBQW1CLEdBQW5CLEdBQXlCLFVBQVUsR0FBVixFQUFlO0FBQUMsU0FBTyxJQUFJLFFBQUosQ0FBYSxJQUFJLEtBQUssS0FBVCxDQUFiLENBQVA7QUFBcUMsQ0FBOUU7QUFDQSxTQUFTLFNBQVQsQ0FBbUIsRUFBbkIsR0FBd0IsS0FBeEI7QUFDQSxTQUFTLFNBQVQsQ0FBbUIsRUFBbkIsR0FBd0IsVUFBVSxDQUFWLEVBQWE7QUFBQyxTQUFPLElBQUksUUFBSixDQUFhLEtBQUssS0FBTCxDQUFXLEVBQUUsS0FBYixDQUFiLENBQVA7QUFBeUMsQ0FBL0U7Ozs7QUFJQSxTQUFTLFFBQVQsQ0FBa0IsS0FBbEIsRUFBeUI7QUFBQyxPQUFLLEtBQUwsR0FBYSxLQUFiO0FBQW1CO0FBQzdDLElBQU0sUUFBUSxTQUFSLEtBQVE7QUFBQSxTQUFLLElBQUksUUFBSixDQUFhLENBQWIsQ0FBTDtBQUFBLENBQWQ7QUFDQSxTQUFTLFNBQVQsQ0FBbUIsR0FBbkIsR0FBeUIsWUFBWTtBQUFDLFNBQU8sSUFBUDtBQUFZLENBQWxEO0FBQ0EsU0FBUyxTQUFULENBQW1CLEVBQW5CLEdBQXdCLEtBQXhCOzs7O0FBSUEsSUFBTSxTQUFTLEVBQWY7O0FBRUEsSUFBTSxPQUFPLFNBQVAsSUFBTyxVQUFXO0FBQ3RCLE1BQUksRUFBRSxXQUFXLE1BQWIsQ0FBSixFQUEwQjtBQUN4QixXQUFPLE9BQVAsSUFBa0IsT0FBbEI7QUFDQSxZQUFRLElBQVIsQ0FBYSxpQkFBYixFQUFn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QWpDLENBQUo7QUFERixLQUVBLE9BQU8sQ0FBUDtBQUNELEdBbEI2QixDQUFaO0FBQUEsQ0FBYjs7QUFvQkEsSUFBTSw4QkFBVyxNQUFNLEVBQU4sRUFBVSxRQUFWLENBQWpCOztBQUVBLElBQU0sd0JBQVEsU0FBUixLQUFRO0FBQUEscUNBQUksRUFBSjtBQUFJLE1BQUo7QUFBQTs7QUFBQSxTQUFXLEtBQUssRUFBRSxNQUFGLENBQVMsRUFBVCxFQUFhLEVBQWIsQ0FBTCxDQUFYO0FBQUEsQ0FBZDs7QUFFUCxJQUFNLE9BQU8sU0FBUCxJQUFPO0FBQUEscUNBQUksTUFBSjtBQUFJLFVBQUo7QUFBQTs7QUFBQSxTQUFlO0FBQUE7O0FBQUEsV0FBSyxxQkFBUSxHQUFSLGlCQUFlLE1BQWYsU0FBdUIsQ0FBdkIsT0FBNkIsQ0FBbEM7QUFBQSxHQUFmO0FBQUEsQ0FBYjs7QUFFTyxJQUFNLG9CQUFNLFNBQU4sR0FBTTtBQUFBLHFDQUFJLE1BQUo7QUFBSSxVQUFKO0FBQUE7O0FBQUEsU0FDakIsTUFBTSxzQkFBUSxNQUFSLFNBQWdCLEtBQWhCLEdBQU4sRUFBOEIsc0JBQVEsTUFBUixTQUFnQixLQUFoQixHQUE5QixDQURpQjtBQUFBLENBQVo7O0FBR0EsSUFBTSw4QkFBVyxTQUFYLFFBQVc7QUFBQSxTQUFpQjtBQUFBLFdBQ3ZDLEtBQUssNEdBQUwsS0FDQSxFQUFFLFFBQUYsQ0FBVyxLQUFYLEVBQWtCLEVBQUUsR0FBRixDQUFNLGFBQU4sRUFBcUIsTUFBckIsQ0FBbEIsRUFDQyxHQURELENBQ0ssRUFBRSxJQUFGLENBQU8sRUFBRSxNQUFGLENBQVM7QUFBQSxhQUFLLE1BQU0sU0FBWDtBQUFBLEtBQVQsQ0FBUCxFQUF1QyxPQUF2QyxDQURMLENBRnVDO0FBQUEsR0FBakI7QUFBQSxDQUFqQjs7a0JBS1EsTyIsImZpbGUiOiJwYXJ0aWFsLmxlbnNlcy5qcyIsInNvdXJjZXNDb250ZW50IjpbImltcG9ydCAqIGFzIFIgZnJvbSBcInJhbWRhXCJcblxuLy9cblxuZnVuY3Rpb24gSWRlbnRpdHkodmFsdWUpIHt0aGlzLnZhbHVlID0gdmFsdWV9XG5jb25zdCBJZGVudCA9IHggPT4gbmV3IElkZW50aXR5KHgpXG5JZGVudGl0eS5wcm90b3R5cGUubWFwID0gZnVuY3Rpb24gKHgyeSkge3JldHVybiBuZXcgSWRlbnRpdHkoeDJ5KHRoaXMudmFsdWUpKX1cbklkZW50aXR5LnByb3RvdHlwZS5vZiA9IElkZW50XG5JZGVudGl0eS5wcm90b3R5cGUuYXAgPSBmdW5jdGlvbiAoeCkge3JldHVybiBuZXcgSWRlbnRpdHkodGhpcy52YWx1ZSh4LnZhbHVlKSl9XG5cbi8vXG5cbmZ1bmN0aW9uIENvbnN0YW50KHZhbHVlKSB7dGhpcy52YWx1ZSA9IHZhbHVlfVxuY29uc3QgQ29uc3QgPSB4ID0+IG5ldyBDb25zdGFudCh4KVxuQ29uc3RhbnQucHJvdG90eXBlLm1hcCA9IGZ1bmN0aW9uICgpIHtyZXR1cm4gdGhpc31cbkNvbnN0YW50LnByb3RvdHlwZS5vZiA9IENvbnN0XG5cbi8vXG5cbmNvbnN0IHdhcm5lZCA9IHt9XG5cbmNvbnN0IHdhcm4gPSBtZXNzYWdlID0+IHtcbiAgaWYgKCEobWVzc2FnZSBpbiB3YXJuZWQpKSB7XG4gICAgd2FybmVkW21lc3NhZ2VdID0gbWVzc2FnZVxuICAgIGNvbnNvbGUud2FybihcInBhcnRpYWwubGVuc2VzOlwiLCBtZXNzYWdlKVxuICB9XG59XG5cbi8vXG5cbmNvbnN0IGlkID0geCA9PiB4XG5jb25zdCBzbmQgPSAoXywgYykgPT4gY1xuXG4vL1xuXG5jb25zdCBjaGVjayA9IChleHBlY3RlZCwgcHJlZGljYXRlKSA9PiB4ID0+IHtcbiAgaWYgKHByZWRpY2F0ZSh4KSlcbiAgICByZXR1cm4geFxuICBlbHNlXG4gICAgdGhyb3cgbmV3IEVycm9yKGBFeHBlY3RlZCAke2V4cGVjdGVkfSwgYnV0IGdvdCAke3h9LmApXG59XG5cbmNvbnN0IGFzc2VydCA9IHByb2Nlc3MuZW52Lk5PREVfRU5WID09PSBcInByb2R1Y3Rpb25cIiA/ICgpID0+IGlkIDogY2hlY2tcblxuLy9cblxuY29uc3QgZW1wdHkgPSB7fVxuXG5jb25zdCBkZWxldGVLZXkgPSAoaywgbykgPT4ge1xuICBpZiAobyA9PT0gdW5kZWZpbmVkIHx8ICEoayBpbiBvKSlcbiAgICByZXR1cm4gb1xuICBsZXQgclxuICBmb3IgKGNvbnN0IHAgaW4gbykge1xuICAgIGlmIChwICE9PSBrKSB7XG4gICAgICBpZiAodW5kZWZpbmVkID09PSByKVxuICAgICAgICByID0ge31cbiAgICAgIHJbcF0gPSBvW3BdXG4gICAgfVxuICB9XG4gIHJldHVybiByXG59XG5cbmNvbnN0IHNldEtleSA9IChrLCB2LCBvKSA9PiB7XG4gIGlmIChvID09PSB1bmRlZmluZWQpXG4gICAgcmV0dXJuIHtba106IHZ9XG4gIGlmIChrIGluIG8gJiYgUi5lcXVhbHModiwgb1trXSkpXG4gICAgcmV0dXJuIG9cbiAgY29uc3QgciA9IHtba106IHZ9XG4gIGZvciAoY29uc3QgcCBpbiBvKVxuICAgIGlmIChwICE9PSBrKVxuICAgICAgcltwXSA9IG9bcF1cbiAgcmV0dXJuIHJcbn1cblxuLy9cblxuY29uc3QgZHJvcHBlZCA9IHhzID0+IE9iamVjdC5rZXlzKHhzKS5sZW5ndGggPT09IDAgPyB1bmRlZmluZWQgOiB4c1xuXG4vL1xuXG5jb25zdCB0b1BhcnRpYWwgPSB0cmFuc2Zvcm0gPT4geCA9PiB1bmRlZmluZWQgPT09IHggPyB4IDogdHJhbnNmb3JtKHgpXG5cbi8vXG5cbmNvbnN0IGNvbnNlcnZlID0gKGMxLCBjMCkgPT4gUi5lcXVhbHMoYzEsIGMwKSA/IGMwIDogYzFcblxuY29uc3QgdG9Db25zZXJ2ZSA9IGYgPT4gKHksIGMwKSA9PiBjb25zZXJ2ZShmKHksIGMwKSwgYzApXG5cbi8vXG5cbmNvbnN0IHNlZW1zTGVucyA9IHggPT4gdHlwZW9mIHggPT09IFwiZnVuY3Rpb25cIiAmJiB4Lmxlbmd0aCA9PT0gMVxuXG5leHBvcnQgY29uc3QgZnJvbVJhbWRhID0gYXNzZXJ0KFwiYSBsZW5zXCIsIHNlZW1zTGVucylcblxuZXhwb3J0IGNvbnN0IHRvUmFtZGEgPSBsID0+IHtcbiAgaWYgKGlzUHJvcChsKSkgIHJldHVybiB0b1JhbWRhUHJvcChsKVxuICBpZiAoaXNJbmRleChsKSkgcmV0dXJuIHRvUmFtZGFJbmRleChsKVxuICByZXR1cm4gZnJvbVJhbWRhKGwpXG59XG5cbmV4cG9ydCBjb25zdCBjb21wb3NlID0gKC4uLmxzKSA9PlxuICBscy5sZW5ndGggPT09IDAgPyBpZGVudGl0eSA6XG4gIGxzLmxlbmd0aCA9PT0gMSA/IGxzWzBdIDpcbiAgUi5jb21wb3NlKC4uLmxzLm1hcCh0b1JhbWRhKSlcblxuZXhwb3J0IGNvbnN0IHJlbW92ZSA9IFIuY3VycnkoKGwsIHMpID0+IHNldEkodG9SYW1kYShsKSwgdW5kZWZpbmVkLCBzKSlcblxuZXhwb3J0IGNvbnN0IHJlbW92ZUFsbCA9IFIuY3VycnkoKGxlbnMsIGRhdGEpID0+IHtcbiAgd2FybihcImByZW1vdmVBbGxgIGlzIGRlcHJlY2F0ZWQgYW5kIHdpbGwgYmUgcmVtb3ZlZCBpbiBuZXh0IG1ham9yIHZlcnNpb24gLS0tIHVzZSBhIGRpZmZlcmVudCBhcHByb2FjaC5cIilcbiAgd2hpbGUgKGdldChsZW5zLCBkYXRhKSAhPT0gdW5kZWZpbmVkKVxuICAgIGRhdGEgPSByZW1vdmUobGVucywgZGF0YSlcbiAgcmV0dXJuIGRhdGFcbn0pXG5cbmNvbnN0IHNldEkgPSAobCwgeCwgcykgPT4gbCgoKSA9PiBJZGVudCh4KSkocykudmFsdWVcbmNvbnN0IGdldEkgPSAobCwgcykgPT4gbChDb25zdCkocykudmFsdWVcbmNvbnN0IG1vZGlmeUkgPSAobCwgeDJ4LCBzKSA9PiBsKHkgPT4gSWRlbnQoeDJ4KHkpKSkocykudmFsdWVcbmNvbnN0IGxlbnNJID0gKGdldHRlciwgc2V0dGVyKSA9PiB0b0ZuID0+IHRhcmdldCA9PlxuICB0b0ZuKGdldHRlcih0YXJnZXQpKS5tYXAoZm9jdXMgPT4gc2V0dGVyKGZvY3VzLCB0YXJnZXQpKVxuXG5leHBvcnQgY29uc3QgbGVucyA9IFIuY3VycnkobGVuc0kpXG5leHBvcnQgY29uc3QgbW9kaWZ5ID0gUi5jdXJyeSgobCwgeDJ4LCBzKSA9PiBtb2RpZnlJKHRvUmFtZGEobCksIHgyeCwgcykpXG5leHBvcnQgY29uc3Qgc2V0ID0gUi5jdXJyeSgobCwgeCwgcykgPT4gc2V0SSh0b1JhbWRhKGwpLCB4LCBzKSlcbmV4cG9ydCBjb25zdCBnZXQgPSBSLmN1cnJ5KChsLCBzKSA9PiBnZXRJKHRvUmFtZGEobCksIHMpKVxuXG5leHBvcnQgY29uc3QgY2hhaW4gPSBSLmN1cnJ5KCh4MnlMLCB4TCkgPT5cbiAgY29tcG9zZSh4TCwgY2hvb3NlKHhPID0+IHhPID09PSB1bmRlZmluZWQgPyBub3RoaW5nIDogeDJ5TCh4TykpKSlcblxuZXhwb3J0IGNvbnN0IGp1c3QgPSB4ID0+IGxlbnNJKFIuYWx3YXlzKHgpLCBzbmQpXG5cbmV4cG9ydCBjb25zdCBjaG9vc2UgPSB4MnlMID0+IHRvRnVuY3RvciA9PiB0YXJnZXQgPT4ge1xuICBjb25zdCBsID0gdG9SYW1kYSh4MnlMKHRhcmdldCkpXG4gIHJldHVybiBSLm1hcChmb2N1cyA9PiBzZXRJKGwsIGZvY3VzLCB0YXJnZXQpLCB0b0Z1bmN0b3IoZ2V0SShsLCB0YXJnZXQpKSlcbn1cblxuZXhwb3J0IGNvbnN0IG5vdGhpbmcgPSBsZW5zSShzbmQsIHNuZClcblxuZXhwb3J0IGNvbnN0IG9yRWxzZSA9XG4gIFIuY3VycnkoKGQsIGwpID0+IGNob29zZSh4ID0+IGdldEkodG9SYW1kYShsKSwgeCkgIT09IHVuZGVmaW5lZCA/IGwgOiBkKSlcblxuZXhwb3J0IGNvbnN0IGNob2ljZSA9ICguLi5scykgPT4gY2hvb3NlKHggPT4ge1xuICBjb25zdCBpID0gbHMuZmluZEluZGV4KGwgPT4gZ2V0SSh0b1JhbWRhKGwpLCB4KSAhPT0gdW5kZWZpbmVkKVxuICByZXR1cm4gMCA8PSBpID8gbHNbaV0gOiBub3RoaW5nXG59KVxuXG5leHBvcnQgY29uc3QgcmVwbGFjZSA9IFIuY3VycnkoKGlubiwgb3V0KSA9PlxuICBsZW5zSSh4ID0+IFIuZXF1YWxzKHgsIGlubikgPyBvdXQgOiB4LFxuICAgICAgICB0b0NvbnNlcnZlKHkgPT4gUi5lcXVhbHMoeSwgb3V0KSA/IGlubiA6IHkpKSlcblxuZXhwb3J0IGNvbnN0IGRlZmF1bHRzID0gcmVwbGFjZSh1bmRlZmluZWQpXG5leHBvcnQgY29uc3QgcmVxdWlyZWQgPSBpbm4gPT4gcmVwbGFjZShpbm4sIHVuZGVmaW5lZClcbmV4cG9ydCBjb25zdCBkZWZpbmUgPSB2ID0+IFIuY29tcG9zZShyZXF1aXJlZCh2KSwgZGVmYXVsdHModikpXG5cbmV4cG9ydCBjb25zdCBub3JtYWxpemUgPSB0cmFuc2Zvcm0gPT5cbiAgbGVuc0kodG9QYXJ0aWFsKHRyYW5zZm9ybSksIHRvQ29uc2VydmUodG9QYXJ0aWFsKHRyYW5zZm9ybSkpKVxuXG5jb25zdCBpc1Byb3AgPSB4ID0+IHR5cGVvZiB4ID09PSBcInN0cmluZ1wiXG5cbmV4cG9ydCBjb25zdCBwcm9wID0gYXNzZXJ0KFwiYSBzdHJpbmdcIiwgaXNQcm9wKVxuXG5jb25zdCB0b1JhbWRhUHJvcCA9IGsgPT5cbiAgbGVuc0kobyA9PiBvICYmIG9ba10sXG4gICAgICAgICh2LCBvKSA9PiB2ID09PSB1bmRlZmluZWQgPyBkZWxldGVLZXkoaywgbykgOiBzZXRLZXkoaywgdiwgbykpXG5cbmV4cG9ydCBjb25zdCBmaW5kID0gcHJlZGljYXRlID0+IGNob29zZSh4cyA9PiB7XG4gIGlmICh4cyA9PT0gdW5kZWZpbmVkKVxuICAgIHJldHVybiBhcHBlbmRcbiAgY29uc3QgaSA9IHhzLmZpbmRJbmRleChwcmVkaWNhdGUpXG4gIHJldHVybiBpIDwgMCA/IGFwcGVuZCA6IGlcbn0pXG5cbmV4cG9ydCBjb25zdCBmaW5kV2l0aCA9ICguLi5scykgPT4ge1xuICBjb25zdCBsbHMgPSB0b1JhbWRhKGNvbXBvc2UoLi4ubHMpKVxuICByZXR1cm4gY29tcG9zZShmaW5kKHggPT4gZ2V0SShsbHMsIHgpICE9PSB1bmRlZmluZWQpLCBsbHMpXG59XG5cbmNvbnN0IGlzSW5kZXggPSB4ID0+IE51bWJlci5pc0ludGVnZXIoeCkgJiYgMCA8PSB4XG5cbmV4cG9ydCBjb25zdCBpbmRleCA9IGFzc2VydChcImEgbm9uLW5lZ2F0aXZlIGludGVnZXJcIiwgaXNJbmRleClcblxuY29uc3QgdG9SYW1kYUluZGV4ID0gaSA9PiBsZW5zSSh4cyA9PiB4cyAmJiB4c1tpXSwgKHgsIHhzKSA9PiB7XG4gIGlmICh4ID09PSB1bmRlZmluZWQpIHtcbiAgICBpZiAoeHMgPT09IHVuZGVmaW5lZClcbiAgICAgIHJldHVybiB1bmRlZmluZWRcbiAgICBpZiAoaSA8IHhzLmxlbmd0aClcbiAgICAgIHJldHVybiBkcm9wcGVkKHhzLnNsaWNlKDAsIGkpLmNvbmNhdCh4cy5zbGljZShpKzEpKSlcbiAgICByZXR1cm4geHNcbiAgfSBlbHNlIHtcbiAgICBpZiAoeHMgPT09IHVuZGVmaW5lZClcbiAgICAgIHJldHVybiBBcnJheShpKS5jb25jYXQoW3hdKVxuICAgIGlmICh4cy5sZW5ndGggPD0gaSlcbiAgICAgIHJldHVybiB4cy5jb25jYXQoQXJyYXkoaSAtIHhzLmxlbmd0aCksIFt4XSlcbiAgICBpZiAoUi5lcXVhbHMoeCwgeHNbaV0pKVxuICAgICAgcmV0dXJuIHhzXG4gICAgcmV0dXJuIHhzLnNsaWNlKDAsIGkpLmNvbmNhdChbeF0sIHhzLnNsaWNlKGkrMSkpXG4gIH1cbn0pXG5cbmV4cG9ydCBjb25zdCBhcHBlbmQgPSBsZW5zSShzbmQsICh4LCB4cykgPT5cbiAgeCA9PT0gdW5kZWZpbmVkID8geHMgOiB4cyA9PT0gdW5kZWZpbmVkID8gW3hdIDogeHMuY29uY2F0KFt4XSkpXG5cbmV4cG9ydCBjb25zdCBmaWx0ZXIgPSBwID0+IGxlbnNJKHhzID0+IHhzICYmIHhzLmZpbHRlcihwKSwgKHlzLCB4cykgPT5cbiAgY29uc2VydmUoZHJvcHBlZChSLmNvbmNhdCh5cyB8fCBbXSwgKHhzIHx8IFtdKS5maWx0ZXIoUi5jb21wbGVtZW50KHApKSkpLCB4cykpXG5cbmV4cG9ydCBjb25zdCBhdWdtZW50ID0gdGVtcGxhdGUgPT4gbGVuc0koXG4gIHRvUGFydGlhbCh4ID0+IHtcbiAgICBjb25zdCB6ID0gey4uLnh9XG4gICAgZm9yIChjb25zdCBrIGluIHRlbXBsYXRlKVxuICAgICAgeltrXSA9IHRlbXBsYXRlW2tdKHgpXG4gICAgcmV0dXJuIHpcbiAgfSksXG4gIHRvQ29uc2VydmUoKHksIGMpID0+IHtcbiAgICBpZiAoeSA9PT0gdW5kZWZpbmVkKVxuICAgICAgcmV0dXJuIHVuZGVmaW5lZFxuICAgIGxldCB6XG4gICAgY29uc3Qgc2V0ID0gKGssIHYpID0+IHtcbiAgICAgIGlmICh1bmRlZmluZWQgPT09IHopXG4gICAgICAgIHogPSB7fVxuICAgICAgeltrXSA9IHZcbiAgICB9XG4gICAgZm9yIChjb25zdCBrIGluIHkpIHtcbiAgICAgIGlmICghKGsgaW4gdGVtcGxhdGUpKVxuICAgICAgICBzZXQoaywgeVtrXSlcbiAgICAgIGVsc2VcbiAgICAgICAgaWYgKGsgaW4gYylcbiAgICAgICAgICBzZXQoaywgY1trXSlcbiAgICB9XG4gICAgcmV0dXJuIHpcbiAgfSkpXG5cbmV4cG9ydCBjb25zdCBwaWNrID0gdGVtcGxhdGUgPT4gbGVuc0koXG4gIGMgPT4ge1xuICAgIGxldCByXG4gICAgZm9yIChjb25zdCBrIGluIHRlbXBsYXRlKSB7XG4gICAgICBjb25zdCB2ID0gZ2V0SSh0b1JhbWRhKHRlbXBsYXRlW2tdKSwgYylcbiAgICAgIGlmICh2ICE9PSB1bmRlZmluZWQpIHtcbiAgICAgICAgaWYgKHIgPT09IHVuZGVmaW5lZClcbiAgICAgICAgICByID0ge31cbiAgICAgICAgcltrXSA9IHZcbiAgICAgIH1cbiAgICB9XG4gICAgcmV0dXJuIHJcbiAgfSxcbiAgKG8gPSBlbXB0eSwgY0luKSA9PiB7XG4gICAgbGV0IGMgPSBjSW5cbiAgICBmb3IgKGNvbnN0IGsgaW4gdGVtcGxhdGUpXG4gICAgICBjID0gc2V0SSh0b1JhbWRhKHRlbXBsYXRlW2tdKSwgb1trXSwgYylcbiAgICByZXR1cm4gY1xuICB9KVxuXG5leHBvcnQgY29uc3QgaWRlbnRpdHkgPSBsZW5zSShpZCwgY29uc2VydmUpXG5cbmV4cG9ydCBjb25zdCBwcm9wcyA9ICguLi5rcykgPT4gcGljayhSLnppcE9iaihrcywga3MpKVxuXG5jb25zdCBzaG93ID0gKC4uLmxhYmVscykgPT4geCA9PiBjb25zb2xlLmxvZyguLi5sYWJlbHMsIHgpIHx8IHhcblxuZXhwb3J0IGNvbnN0IGxvZyA9ICguLi5sYWJlbHMpID0+XG4gIGxlbnNJKHNob3coLi4ubGFiZWxzLCBcImdldFwiKSwgc2hvdyguLi5sYWJlbHMsIFwic2V0XCIpKVxuXG5leHBvcnQgY29uc3Qgc2VxdWVuY2UgPSB0b0FwcGxpY2F0aXZlID0+IHRhcmdldCA9PlxuICB3YXJuKFwiYHNlcXVlbmNlYCBpcyBleHBlcmltZW50YWwgYW5kIG1pZ2h0IGJlIHJlbW92ZWQsIHJlbmFtZWQgb3IgY2hhbmdlZCBzZW1hbnRpY2FsbHkgYmVmb3JlIG5leHQgbWFqb3IgcmVsZWFzZVwiKSB8fFxuICBSLnNlcXVlbmNlKElkZW50LCBSLm1hcCh0b0FwcGxpY2F0aXZlLCB0YXJnZXQpKVxuICAubWFwKFIucGlwZShSLmZpbHRlcih4ID0+IHggIT09IHVuZGVmaW5lZCksIGRyb3BwZWQpKVxuXG5leHBvcnQgZGVmYXVsdCBjb21wb3NlXG4iXX0=