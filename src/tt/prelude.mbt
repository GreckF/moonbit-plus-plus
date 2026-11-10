///|
/// Prelude functions on `Nat` that run as native operations in the
/// interpreter and in compiled code, where a `Nat` is a `BigInt`: name ->
/// (primitive, number of parameters). The checker computes with their
/// definitions (`Nat` is unary there).
pub let nat_natives : Map[String, (String, Int32)] = {
  "int_to_nat": ("%nat_of_int", 1),
  "Nat::to_int": ("%nat_to_int", 1),
  "Nat::op_add": ("%nat_add", 2),
  "Nat::op_mul": ("%nat_mul", 2),
  "Nat::op_equal": ("%nat_eq", 2),
  "Nat::compare": ("%nat_compare", 2),
  "Nat::to_string": ("%nat_to_string", 1),
  "Nat::op_lt": ("%nat_lt", 2),
  "Nat::op_le": ("%nat_le", 2),
  "Nat::op_gt": ("%nat_gt", 2),
  "Nat::op_ge": ("%nat_ge", 2),
  "Nat::op_sub": ("%nat_sub", 2),
  "Nat::op_div": ("%nat_div", 2),
  "Nat::op_mod": ("%nat_mod", 2),
  "Nat::gcd": ("%nat_gcd", 2),
  "Nat::pow": ("%nat_pow", 2),
  "Nat::op_shl": ("%nat_shl", 2),
  "Nat::op_shr": ("%nat_shr", 2),
  "Nat::log2": ("%nat_log2", 1),
  "Nat::op_land": ("%nat_land", 2),
  "Nat::op_lor": ("%nat_lor", 2),
  "Nat::op_lxor": ("%nat_lxor", 2),
  "Nat::to_bigint": ("%nat_to_bigint", 1),
  "Nat::of_bigint": ("%nat_of_bigint", 1),
  "Nat::deq": ("%nat_deq", 2),
}

///|
/// The MoonBit++ prelude. `Int`, `String`, `Char`, `Bool`, `Unit`,
/// `Array` and `Error` are built in.
pub let prelude_src : String =
  #|enum Nat {
  #|  Z
  #|  S(Nat)
  #|}
  #|
  #|enum Id[T](x : T) : (y : T) -> Prop {
  #|  Refl : Id[T](x)(x)
  #|}
  #|
  #|#mbt("Option")
  #|enum Option[T] {
  #|  None
  #|  Some(T)
  #|}
  #|
  #|#mbt("Result")
  #|enum Result[T, E] {
  #|  Ok(T)
  #|  Err(E)
  #|}
  #|
  #|enum List[T] {
  #|  Nil
  #|  Cons(T, List[T])
  #|}
  #|
  #|struct Tuple2[A, B] {
  #|  _0 : A
  #|  _1 : B
  #|}
  #|
  #|struct Tuple3[A, B, C] {
  #|  _0 : A
  #|  _1 : B
  #|  _2 : C
  #|}
  #|
  #|suberror Failure {
  #|  Failure(String)
  #|}
  #|
  #|// ---- primitives -------------------------------------------------------
  #|
  #|fn Int::op_add(self : Int, other : Int) -> Int = "%int_add"
  #|fn Int::op_sub(self : Int, other : Int) -> Int = "%int_sub"
  #|fn Int::op_mul(self : Int, other : Int) -> Int = "%int_mul"
  #|fn Int::op_div(self : Int, other : Int) -> Int = "%int_div"
  #|fn Int::op_mod(self : Int, other : Int) -> Int = "%int_mod"
  #|fn Int::op_neg(self : Int) -> Int = "%int_neg"
  #|fn Int::op_land(self : Int, other : Int) -> Int = "%int_land"
  #|fn Int::op_lor(self : Int, other : Int) -> Int = "%int_lor"
  #|fn Int::op_lxor(self : Int, other : Int) -> Int = "%int_lxor"
  #|fn Int::op_shl(self : Int, n : Int) -> Int = "%int_shl"
  #|fn Int::op_shr(self : Int, n : Int) -> Int = "%int_shr"
  #|fn Int::op_equal(self : Int, other : Int) -> Bool = "%int_eq"
  #|fn Int::op_lt(self : Int, other : Int) -> Bool = "%int_lt"
  #|fn Int::op_le(self : Int, other : Int) -> Bool = "%int_le"
  #|fn Int::op_gt(self : Int, other : Int) -> Bool = "%int_gt"
  #|fn Int::op_ge(self : Int, other : Int) -> Bool = "%int_ge"
  #|fn Int::compare(self : Int, other : Int) -> Int = "%int_compare"
  #|fn Int::to_string(self : Int) -> String = "%int_to_string"
  #|fn Int::unsafe_to_char(self : Int) -> Char = "%int_to_char"
  #|fn Int::to_double(self : Int) -> Double = "%int_to_double"
  #|
  #|fn Double::op_add(self : Double, other : Double) -> Double = "%double_add"
  #|fn Double::op_sub(self : Double, other : Double) -> Double = "%double_sub"
  #|fn Double::op_mul(self : Double, other : Double) -> Double = "%double_mul"
  #|fn Double::op_div(self : Double, other : Double) -> Double = "%double_div"
  #|fn Double::op_neg(self : Double) -> Double = "%double_neg"
  #|fn Double::op_equal(self : Double, other : Double) -> Bool = "%double_eq"
  #|fn Double::op_lt(self : Double, other : Double) -> Bool = "%double_lt"
  #|fn Double::op_le(self : Double, other : Double) -> Bool = "%double_le"
  #|fn Double::op_gt(self : Double, other : Double) -> Bool = "%double_gt"
  #|fn Double::op_ge(self : Double, other : Double) -> Bool = "%double_ge"
  #|fn Double::compare(self : Double, other : Double) -> Int = "%double_compare"
  #|fn Double::to_string(self : Double) -> String = "%double_to_string"
  #|fn Double::to_int(self : Double) -> Int = "%double_to_int"
  #|
  #|fn String::op_add(self : String, other : String) -> String = "%str_add"
  #|fn String::op_equal(self : String, other : String) -> Bool = "%str_eq"
  #|fn String::compare(self : String, other : String) -> Int = "%str_compare"
  #|fn String::length(self : String) -> Int = "%str_length"
  #|fn String::op_get(self : String, i : Int) -> Char = "%str_get"
  #|fn String::substring(self : String, start : Int, end : Int) -> String = "%str_substring"
  #|fn String::slice(self : String, start : Int, end : Int) -> String { self.substring(start, end) }
  #|fn String::to_string(self : String) -> String { self }
  #|
  #|fn Bool::op_equal(self : Bool, other : Bool) -> Bool = "%bool_eq"
  #|fn Bool::not(self : Bool) -> Bool = "%bool_not"
  #|fn Bool::to_string(self : Bool) -> String = "%bool_to_string"
  #|fn not(b : Bool) -> Bool = "%bool_not"
  #|
  #|fn Char::op_equal(self : Char, other : Char) -> Bool = "%char_eq"
  #|fn Char::compare(self : Char, other : Char) -> Int = "%char_compare"
  #|fn Char::to_int(self : Char) -> Int = "%char_to_int"
  #|fn Char::to_string(self : Char) -> String = "%char_to_string"
  #|
  #|fn Unit::to_string(self : Unit) -> String = "%unit_to_string"
  #|
  #|fn[T] Array::make(n : Int, x : T) -> Array[T] = "%array_make"
  #|fn[T] Array::new() -> Array[T] = "%array_new"
  #|fn[T] Array::length(self : Array[T]) -> Int = "%array_length"
  #|fn[T] Array::op_get(self : Array[T], i : Int) -> T = "%array_get"
  #|fn[T] Array::op_set(self : Array[T], i : Int, x : T) -> Unit = "%array_set"
  #|fn[T] Array::push(self : Array[T], x : T) -> Unit = "%array_push"
  #|
  #|// the elements from `start` to `end` (excluded), e.g. for `[x, ..rest]`
  #|fn[T] Array::slice(self : Array[T], start : Int, end : Int) -> Array[T] {
  #|  let out : Array[T] = Array::new()
  #|  for i = start; i < end; i = i + 1 {
  #|    out.push(self[i])
  #|  }
  #|  out
  #|}
  #|
  #|fn print_string(s : String) -> Unit = "%print"
  #|fn[T] panic() -> T = "%panic"
  #|fn[T] abort(msg : String) -> T = "%abort"
  #|
  #|// ---- BigInt -----------------------------------------------------------
  #|// MoonBit's arbitrary-precision integers (also `@bigint.BigInt` when
  #|// `moonbitlang/core/bigint` is imported). They are not computed during
  #|// checking.
  #|
  #|fn BigInt::from_int(i : Int) -> BigInt = "%bigint_of_int"
  #|fn BigInt::from_int64(i : Int64) -> BigInt = "%bigint_of_int64"
  #|fn BigInt::to_int(self : BigInt) -> Int = "%bigint_to_int"
  #|fn BigInt::to_int64(self : BigInt) -> Int64 = "%bigint_to_int64"
  #|fn BigInt::op_add(self : BigInt, other : BigInt) -> BigInt = "%bigint_add"
  #|fn BigInt::op_sub(self : BigInt, other : BigInt) -> BigInt = "%bigint_sub"
  #|fn BigInt::op_mul(self : BigInt, other : BigInt) -> BigInt = "%bigint_mul"
  #|fn BigInt::op_div(self : BigInt, other : BigInt) -> BigInt = "%bigint_div"
  #|fn BigInt::op_mod(self : BigInt, other : BigInt) -> BigInt = "%bigint_mod"
  #|fn BigInt::op_neg(self : BigInt) -> BigInt = "%bigint_neg"
  #|fn BigInt::op_land(self : BigInt, other : BigInt) -> BigInt = "%bigint_land"
  #|fn BigInt::op_lor(self : BigInt, other : BigInt) -> BigInt = "%bigint_lor"
  #|fn BigInt::op_lxor(self : BigInt, other : BigInt) -> BigInt = "%bigint_lxor"
  #|fn BigInt::op_shl(self : BigInt, n : Int) -> BigInt = "%bigint_shl"
  #|fn BigInt::op_shr(self : BigInt, n : Int) -> BigInt = "%bigint_shr"
  #|fn BigInt::op_equal(self : BigInt, other : BigInt) -> Bool = "%bigint_eq"
  #|fn BigInt::op_lt(self : BigInt, other : BigInt) -> Bool = "%bigint_lt"
  #|fn BigInt::op_le(self : BigInt, other : BigInt) -> Bool = "%bigint_le"
  #|fn BigInt::op_gt(self : BigInt, other : BigInt) -> Bool = "%bigint_gt"
  #|fn BigInt::op_ge(self : BigInt, other : BigInt) -> Bool = "%bigint_ge"
  #|fn BigInt::compare(self : BigInt, other : BigInt) -> Int = "%bigint_compare"
  #|fn BigInt::pow(self : BigInt, n : BigInt) -> BigInt = "%bigint_pow"
  #|fn BigInt::to_string(self : BigInt) -> String = "%bigint_to_string"
  #|fn BigInt::hash(self : BigInt) -> Int = "%bigint_hash"
  #|
  #|// ---- Nat --------------------------------------------------------------
  #|
  #|fn int_to_nat(n : Int) -> Nat {
  #|  if n <= 0 { Z } else { S(int_to_nat(n - 1)) }
  #|}
  #|
  #|fn Nat::to_int(self : Nat) -> Int {
  #|  match self {
  #|    Z => 0
  #|    S(n) => n.to_int() + 1
  #|  }
  #|}
  #|
  #|fn Nat::op_add(self : Nat, other : Nat) -> Nat {
  #|  match self {
  #|    Z => other
  #|    S(n) => S(n + other)
  #|  }
  #|}
  #|
  #|fn Nat::op_mul(self : Nat, other : Nat) -> Nat {
  #|  match self {
  #|    Z => Z
  #|    S(n) => other + n * other
  #|  }
  #|}
  #|
  #|fn Nat::op_equal(self : Nat, other : Nat) -> Bool {
  #|  match (self, other) {
  #|    (Z, Z) => true
  #|    (S(a), S(b)) => a == b
  #|    _ => false
  #|  }
  #|}
  #|
  #|fn Nat::compare(self : Nat, other : Nat) -> Int {
  #|  match (self, other) {
  #|    (Z, Z) => 0
  #|    (Z, S(_)) => -1
  #|    (S(_), Z) => 1
  #|    (S(a), S(b)) => a.compare(b)
  #|  }
  #|}
  #|
  #|fn Nat::to_string(self : Nat) -> String {
  #|  self.to_int().to_string()
  #|}
  #|
  #|fn Nat::op_lt(self : Nat, other : Nat) -> Bool {
  #|  self.compare(other) < 0
  #|}
  #|
  #|fn Nat::op_le(self : Nat, other : Nat) -> Bool {
  #|  self.compare(other) <= 0
  #|}
  #|
  #|fn Nat::op_gt(self : Nat, other : Nat) -> Bool {
  #|  self.compare(other) > 0
  #|}
  #|
  #|fn Nat::op_ge(self : Nat, other : Nat) -> Bool {
  #|  self.compare(other) >= 0
  #|}
  #|
  #|// truncated: `a - b` is 0 when `b > a`
  #|fn Nat::op_sub(self : Nat, other : Nat) -> Nat {
  #|  match (self, other) {
  #|    (_, Z) => self
  #|    (Z, S(_)) => Z
  #|    (S(a), S(b)) => a - b
  #|  }
  #|}
  #|
  #|// The definitions below are for checking (they run natively): their
  #|// recursive calls get variables of patterns or constructed values, not
  #|// calls, which would be computed again at each use.
  #|
  #|// `(q, r)` with `a = q * b + r` (`b > 0`): counts `a` down, `r` up to `b`
  #|fn nat_divmod(a : Nat, b : Nat, q : Nat, r : Nat) -> (Nat, Nat) {
  #|  match a {
  #|    Z => (q, r)
  #|    S(k) => if S(r) == b { nat_divmod(k, b, S(q), Z) } else { nat_divmod(k, b, q, S(r)) }
  #|  }
  #|}
  #|
  #|// `a / 0` is 0 and `a % 0` is `a`, as in Lean
  #|fn Nat::op_div(self : Nat, other : Nat) -> Nat {
  #|  match other {
  #|    Z => Z
  #|    S(_) =>
  #|      match nat_divmod(self, other, Z, Z) {
  #|        (q, _) => q
  #|      }
  #|  }
  #|}
  #|
  #|fn Nat::op_mod(self : Nat, other : Nat) -> Nat {
  #|  match other {
  #|    Z => self
  #|    S(_) =>
  #|      match nat_divmod(self, other, Z, Z) {
  #|        (_, r) => r
  #|      }
  #|  }
  #|}
  #|
  #|fn Nat::gcd(self : Nat, other : Nat) -> Nat {
  #|  match other {
  #|    Z => self
  #|    S(o) =>
  #|      match self % S(o) {
  #|        Z => S(o)
  #|        S(r) => S(o).gcd(S(r))
  #|      }
  #|  }
  #|}
  #|
  #|fn Nat::pow(self : Nat, n : Nat) -> Nat {
  #|  match n {
  #|    Z => S(Z)
  #|    S(k) => self * self.pow(k)
  #|  }
  #|}
  #|
  #|fn Nat::op_shl(self : Nat, n : Nat) -> Nat {
  #|  self * (2 : Nat).pow(n)
  #|}
  #|
  #|fn Nat::op_shr(self : Nat, n : Nat) -> Nat {
  #|  self / (2 : Nat).pow(n)
  #|}
  #|
  #|// `(n / 2, n % 2 == 1)`
  #|fn nat_half(n : Nat) -> (Nat, Bool) {
  #|  match n {
  #|    Z => (Z, false)
  #|    S(Z) => (Z, true)
  #|    S(S(k)) =>
  #|      match nat_half(k) {
  #|        (h, b) => (S(h), b)
  #|      }
  #|  }
  #|}
  #|
  #|// `log2(0)` is 0
  #|fn Nat::log2(self : Nat) -> Nat {
  #|  match nat_half(self) {
  #|    (Z, _) => Z
  #|    (S(h), _) => S(S(h).log2())
  #|  }
  #|}
  #|
  #|// the bits of `a` and `b` combined by `f` (`f(false, false)` is false)
  #|fn nat_bitwise(f : (Bool, Bool) -> Bool, a : Nat, b : Nat) -> Nat {
  #|  match (nat_half(a), nat_half(b)) {
  #|    ((Z, false), (Z, false)) => Z
  #|    ((ha, ba), (hb, bb)) => {
  #|      let low : Nat = if f(ba, bb) { 1 } else { 0 }
  #|      low + nat_bitwise(f, ha, hb) * 2
  #|    }
  #|  }
  #|}
  #|
  #|fn Nat::op_land(self : Nat, other : Nat) -> Nat {
  #|  nat_bitwise((x, y) => x && y, self, other)
  #|}
  #|
  #|fn Nat::op_lor(self : Nat, other : Nat) -> Nat {
  #|  nat_bitwise((x, y) => x || y, self, other)
  #|}
  #|
  #|fn Nat::op_lxor(self : Nat, other : Nat) -> Nat {
  #|  nat_bitwise((x, y) => x != y, self, other)
  #|}
  #|
  #|fn Nat::to_bigint(self : Nat) -> BigInt {
  #|  match self {
  #|    Z => BigInt::from_int(0)
  #|    S(n) => n.to_bigint() + BigInt::from_int(1)
  #|  }
  #|}
  #|
  #|// a negative number is 0
  #|fn Nat::of_bigint(b : BigInt) -> Nat {
  #|  if b <= BigInt::from_int(0) { Z } else { S(Nat::of_bigint(b - BigInt::from_int(1))) }
  #|}
  #|
  #|fn plus(n : Nat, m : Nat) -> Nat {
  #|  n + m
  #|}
  #|
  #|fn[T] Array::size(self : Array[T]) -> Nat {
  #|  int_to_nat(self.length())
  #|}
  #|
  #|// ---- propositional equality -----------------------------------------
  #|
  #|fn[T, x : T, y : T] Id::sym(p : x === y) -> y === x {
  #|  match p {
  #|    Refl => Refl
  #|  }
  #|}
  #|
  #|fn[T, x : T, y : T, z : T] Id::trans(p : x === y, q : y === z) -> x === z {
  #|  match q {
  #|    Refl => p
  #|  }
  #|}
  #|
  #|fn[T, U, x : T, y : T] Id::cong(f : (T) -> U, p : x === y) -> f(x) === f(y) {
  #|  match p {
  #|    Refl => Refl
  #|  }
  #|}
  #|
  #|fn[T, x : T, y : T] Id::subst(p : x === y, motive : (T) -> Type, px : motive(x)) -> motive(y) {
  #|  match p {
  #|    Refl => px
  #|  }
  #|}
  #|
  #|// `subst` for a motive that is a proposition (`NatLe(a, b)` to `NatLe(a, c)`)
  #|fn[T, x : T, y : T] Id::subst_prop(p : x === y, motive : (T) -> Prop, px : motive(x)) -> motive(y) {
  #|  match p {
  #|    Refl => px
  #|  }
  #|}
  #|
  #|// ---- decidable equality --------------------------------------------
  #|
  #|// the false proposition (no proof), and negation
  #|enum False : Prop {}
  #|
  #|fn Not(P : Prop) -> Prop {
  #|  (P) -> False
  #|}
  #|
  #|fn[T] absurd(f : False) -> T {
  #|  match f {}
  #|}
  #|
  #|// a decision: a proof of `P`, or of its negation (Lean's `Decidable`)
  #|enum Dec[P : Prop] {
  #|  Yes(P)
  #|  No(Not(P))
  #|}
  #|
  #|// a proof found, or nothing known (`ptr_deq`: different objects may still
  #|// be equal)
  #|enum Known[P : Prop] {
  #|  Proved(P)
  #|  Unknown
  #|}
  #|
  #|// a `Bool` with a proof of its value
  #|enum Reflect(b : Bool) {
  #|  IsTrue(b === true)
  #|  IsFalse(b === false)
  #|}
  #|
  #|fn reflect(b : Bool) -> Reflect(b) {
  #|  match b {
  #|    true => IsTrue(Refl)
  #|    false => IsFalse(Refl)
  #|  }
  #|}
  #|
  #|// `==` of these types is structural equality (not of `Double`: `0.0 ==
  #|// -0.0`), so a comparison proves the equality or its negation (axioms, not
  #|// computed during checking, erased when compiling)
  #|fn[a : Int, b : Int] Int::eq_sound(h : (a == b) === true) -> a === b = "%axiom"
  #|fn[a : Int, b : Int] Int::ne_sound(h : (a == b) === false) -> Not(a === b) = "%axiom"
  #|fn[a : Int64, b : Int64] Int64::eq_sound(h : (a == b) === true) -> a === b = "%axiom"
  #|fn[a : Int64, b : Int64] Int64::ne_sound(h : (a == b) === false) -> Not(a === b) = "%axiom"
  #|fn[a : UInt, b : UInt] UInt::eq_sound(h : (a == b) === true) -> a === b = "%axiom"
  #|fn[a : UInt, b : UInt] UInt::ne_sound(h : (a == b) === false) -> Not(a === b) = "%axiom"
  #|fn[a : UInt64, b : UInt64] UInt64::eq_sound(h : (a == b) === true) -> a === b = "%axiom"
  #|fn[a : UInt64, b : UInt64] UInt64::ne_sound(h : (a == b) === false) -> Not(a === b) = "%axiom"
  #|fn[a : Byte, b : Byte] Byte::eq_sound(h : (a == b) === true) -> a === b = "%axiom"
  #|fn[a : Byte, b : Byte] Byte::ne_sound(h : (a == b) === false) -> Not(a === b) = "%axiom"
  #|fn[a : Char, b : Char] Char::eq_sound(h : (a == b) === true) -> a === b = "%axiom"
  #|fn[a : Char, b : Char] Char::ne_sound(h : (a == b) === false) -> Not(a === b) = "%axiom"
  #|fn[a : String, b : String] String::eq_sound(h : (a == b) === true) -> a === b = "%axiom"
  #|fn[a : String, b : String] String::ne_sound(h : (a == b) === false) -> Not(a === b) = "%axiom"
  #|fn[a : BigInt, b : BigInt] BigInt::eq_sound(h : (a == b) === true) -> a === b = "%axiom"
  #|fn[a : BigInt, b : BigInt] BigInt::ne_sound(h : (a == b) === false) -> Not(a === b) = "%axiom"
  #|
  #|fn Int::deq(a : Int, b : Int) -> Dec[a === b] {
  #|  match reflect(a == b) {
  #|    IsTrue(h) => Yes(Int::eq_sound(h))
  #|    IsFalse(h) => No(Int::ne_sound(h))
  #|  }
  #|}
  #|fn Int64::deq(a : Int64, b : Int64) -> Dec[a === b] {
  #|  match reflect(a == b) {
  #|    IsTrue(h) => Yes(Int64::eq_sound(h))
  #|    IsFalse(h) => No(Int64::ne_sound(h))
  #|  }
  #|}
  #|fn UInt::deq(a : UInt, b : UInt) -> Dec[a === b] {
  #|  match reflect(a == b) {
  #|    IsTrue(h) => Yes(UInt::eq_sound(h))
  #|    IsFalse(h) => No(UInt::ne_sound(h))
  #|  }
  #|}
  #|fn UInt64::deq(a : UInt64, b : UInt64) -> Dec[a === b] {
  #|  match reflect(a == b) {
  #|    IsTrue(h) => Yes(UInt64::eq_sound(h))
  #|    IsFalse(h) => No(UInt64::ne_sound(h))
  #|  }
  #|}
  #|fn Byte::deq(a : Byte, b : Byte) -> Dec[a === b] {
  #|  match reflect(a == b) {
  #|    IsTrue(h) => Yes(Byte::eq_sound(h))
  #|    IsFalse(h) => No(Byte::ne_sound(h))
  #|  }
  #|}
  #|fn Char::deq(a : Char, b : Char) -> Dec[a === b] {
  #|  match reflect(a == b) {
  #|    IsTrue(h) => Yes(Char::eq_sound(h))
  #|    IsFalse(h) => No(Char::ne_sound(h))
  #|  }
  #|}
  #|fn String::deq(a : String, b : String) -> Dec[a === b] {
  #|  match reflect(a == b) {
  #|    IsTrue(h) => Yes(String::eq_sound(h))
  #|    IsFalse(h) => No(String::ne_sound(h))
  #|  }
  #|}
  #|fn BigInt::deq(a : BigInt, b : BigInt) -> Dec[a === b] {
  #|  match reflect(a == b) {
  #|    IsTrue(h) => Yes(BigInt::eq_sound(h))
  #|    IsFalse(h) => No(BigInt::ne_sound(h))
  #|  }
  #|}
  #|
  #|fn Bool::deq(a : Bool, b : Bool) -> Dec[a === b] {
  #|  match (a, b) {
  #|    (true, true) => Yes(Refl)
  #|    (false, false) => Yes(Refl)
  #|    (true, false) => No(h => match h {})
  #|    (false, true) => No(h => match h {})
  #|  }
  #|}
  #|
  #|fn Unit::deq(a : Unit, b : Unit) -> Dec[a === b] {
  #|  match (a, b) {
  #|    ((), ()) => Yes(Refl)
  #|  }
  #|}
  #|
  #|fn Nat::deq(a : Nat, b : Nat) -> Dec[a === b] {
  #|  match (a, b) {
  #|    (Z, Z) => Yes(Refl)
  #|    (S(x), S(y)) =>
  #|      match x.deq(y) {
  #|        Yes(p) =>
  #|          match p {
  #|            Refl => Yes(Refl)
  #|          }
  #|        No(n) => No(h => match h { Refl => n(Refl) })
  #|      }
  #|    (Z, S(_)) => No(h => match h {})
  #|    (S(_), Z) => No(h => match h {})
  #|  }
  #|}
  #|
  #|// the same object (MoonBit's `physical_equal`); not computed during
  #|// checking
  #|fn[T] physical_equal(a : T, b : T) -> Bool = "%physical_equal"
  #|
  #|// run code made at run time (`code { e }`, see doc/mbtpp/staging.md)
  #|fn[T] Code::run(self : Code[T]) -> T = "%run"
  #|fn[T, a : T, b : T] physical_equal_sound(h : physical_equal(a, b) === true) -> a === b = "%axiom"
  #|
  #|fn[T] ptr_deq(a : T, b : T) -> Known[a === b] {
  #|  match reflect(physical_equal(a, b)) {
  #|    IsTrue(h) => Proved(physical_equal_sound(h))
  #|    IsFalse(_) => Unknown
  #|  }
  #|}
  #|
  #|// ---- lists ------------------------------------------------------------
  #|
  #|fn[T] List::length(self : List[T]) -> Int {
  #|  match self {
  #|    Nil => 0
  #|    Cons(_, xs) => xs.length() + 1
  #|  }
  #|}
  #|
  #|fn[T] List::append(self : List[T], ys : List[T]) -> List[T] {
  #|  match self {
  #|    Nil => ys
  #|    Cons(x, xs) => Cons(x, xs.append(ys))
  #|  }
  #|}
  #|
  #|fn[T] List::reverse(self : List[T]) -> List[T] {
  #|  match self {
  #|    Nil => Nil
  #|    Cons(x, xs) => xs.reverse().append(Cons(x, Nil))
  #|  }
  #|}
  #|
  #|fn[T, U] List::map(self : List[T], f : (T) -> U) -> List[U] {
  #|  match self {
  #|    Nil => Nil
  #|    Cons(x, xs) => Cons(f(x), xs.map(f))
  #|  }
  #|}
  #|
  #|// ---- other numeric types ----------------------------------------------
  #|fn Int64::op_add(self : Int64, other : Int64) -> Int64 = "%int64_add"
  #|fn Int64::op_sub(self : Int64, other : Int64) -> Int64 = "%int64_sub"
  #|fn Int64::op_mul(self : Int64, other : Int64) -> Int64 = "%int64_mul"
  #|fn Int64::op_div(self : Int64, other : Int64) -> Int64 = "%int64_div"
  #|fn Int64::op_mod(self : Int64, other : Int64) -> Int64 = "%int64_mod"
  #|fn Int64::op_neg(self : Int64) -> Int64 = "%int64_neg"
  #|fn Int64::op_land(self : Int64, other : Int64) -> Int64 = "%int64_land"
  #|fn Int64::op_lor(self : Int64, other : Int64) -> Int64 = "%int64_lor"
  #|fn Int64::op_lxor(self : Int64, other : Int64) -> Int64 = "%int64_lxor"
  #|fn Int64::op_shl(self : Int64, n : Int) -> Int64 = "%int64_shl"
  #|fn Int64::op_shr(self : Int64, n : Int) -> Int64 = "%int64_shr"
  #|fn Int64::op_equal(self : Int64, other : Int64) -> Bool = "%int64_eq"
  #|fn Int64::op_lt(self : Int64, other : Int64) -> Bool = "%int64_lt"
  #|fn Int64::op_le(self : Int64, other : Int64) -> Bool = "%int64_le"
  #|fn Int64::op_gt(self : Int64, other : Int64) -> Bool = "%int64_gt"
  #|fn Int64::op_ge(self : Int64, other : Int64) -> Bool = "%int64_ge"
  #|fn Int64::compare(self : Int64, other : Int64) -> Int = "%int64_compare"
  #|fn Int64::to_string(self : Int64) -> String = "%int64_to_string"
  #|fn Int64::hash(self : Int64) -> Int = "%int64_hash"
  #|fn UInt::op_add(self : UInt, other : UInt) -> UInt = "%uint_add"
  #|fn UInt::op_sub(self : UInt, other : UInt) -> UInt = "%uint_sub"
  #|fn UInt::op_mul(self : UInt, other : UInt) -> UInt = "%uint_mul"
  #|fn UInt::op_div(self : UInt, other : UInt) -> UInt = "%uint_div"
  #|fn UInt::op_mod(self : UInt, other : UInt) -> UInt = "%uint_mod"
  #|fn UInt::op_land(self : UInt, other : UInt) -> UInt = "%uint_land"
  #|fn UInt::op_lor(self : UInt, other : UInt) -> UInt = "%uint_lor"
  #|fn UInt::op_lxor(self : UInt, other : UInt) -> UInt = "%uint_lxor"
  #|fn UInt::op_shl(self : UInt, n : Int) -> UInt = "%uint_shl"
  #|fn UInt::op_shr(self : UInt, n : Int) -> UInt = "%uint_shr"
  #|fn UInt::op_equal(self : UInt, other : UInt) -> Bool = "%uint_eq"
  #|fn UInt::op_lt(self : UInt, other : UInt) -> Bool = "%uint_lt"
  #|fn UInt::op_le(self : UInt, other : UInt) -> Bool = "%uint_le"
  #|fn UInt::op_gt(self : UInt, other : UInt) -> Bool = "%uint_gt"
  #|fn UInt::op_ge(self : UInt, other : UInt) -> Bool = "%uint_ge"
  #|fn UInt::compare(self : UInt, other : UInt) -> Int = "%uint_compare"
  #|fn UInt::to_string(self : UInt) -> String = "%uint_to_string"
  #|fn UInt::hash(self : UInt) -> Int = "%uint_hash"
  #|fn UInt64::op_add(self : UInt64, other : UInt64) -> UInt64 = "%uint64_add"
  #|fn UInt64::op_sub(self : UInt64, other : UInt64) -> UInt64 = "%uint64_sub"
  #|fn UInt64::op_mul(self : UInt64, other : UInt64) -> UInt64 = "%uint64_mul"
  #|fn UInt64::op_div(self : UInt64, other : UInt64) -> UInt64 = "%uint64_div"
  #|fn UInt64::op_mod(self : UInt64, other : UInt64) -> UInt64 = "%uint64_mod"
  #|fn UInt64::op_land(self : UInt64, other : UInt64) -> UInt64 = "%uint64_land"
  #|fn UInt64::op_lor(self : UInt64, other : UInt64) -> UInt64 = "%uint64_lor"
  #|fn UInt64::op_lxor(self : UInt64, other : UInt64) -> UInt64 = "%uint64_lxor"
  #|fn UInt64::op_shl(self : UInt64, n : Int) -> UInt64 = "%uint64_shl"
  #|fn UInt64::op_shr(self : UInt64, n : Int) -> UInt64 = "%uint64_shr"
  #|fn UInt64::op_equal(self : UInt64, other : UInt64) -> Bool = "%uint64_eq"
  #|fn UInt64::op_lt(self : UInt64, other : UInt64) -> Bool = "%uint64_lt"
  #|fn UInt64::op_le(self : UInt64, other : UInt64) -> Bool = "%uint64_le"
  #|fn UInt64::op_gt(self : UInt64, other : UInt64) -> Bool = "%uint64_gt"
  #|fn UInt64::op_ge(self : UInt64, other : UInt64) -> Bool = "%uint64_ge"
  #|fn UInt64::compare(self : UInt64, other : UInt64) -> Int = "%uint64_compare"
  #|fn UInt64::to_string(self : UInt64) -> String = "%uint64_to_string"
  #|fn UInt64::hash(self : UInt64) -> Int = "%uint64_hash"
  #|fn Byte::op_add(self : Byte, other : Byte) -> Byte = "%byte_add"
  #|fn Byte::op_sub(self : Byte, other : Byte) -> Byte = "%byte_sub"
  #|fn Byte::op_mul(self : Byte, other : Byte) -> Byte = "%byte_mul"
  #|fn Byte::op_div(self : Byte, other : Byte) -> Byte = "%byte_div"
  #|fn Byte::op_mod(self : Byte, other : Byte) -> Byte = "%byte_mod"
  #|fn Byte::op_land(self : Byte, other : Byte) -> Byte = "%byte_land"
  #|fn Byte::op_lor(self : Byte, other : Byte) -> Byte = "%byte_lor"
  #|fn Byte::op_lxor(self : Byte, other : Byte) -> Byte = "%byte_lxor"
  #|fn Byte::op_shl(self : Byte, n : Int) -> Byte = "%byte_shl"
  #|fn Byte::op_shr(self : Byte, n : Int) -> Byte = "%byte_shr"
  #|fn Byte::op_equal(self : Byte, other : Byte) -> Bool = "%byte_eq"
  #|fn Byte::op_lt(self : Byte, other : Byte) -> Bool = "%byte_lt"
  #|fn Byte::op_le(self : Byte, other : Byte) -> Bool = "%byte_le"
  #|fn Byte::op_gt(self : Byte, other : Byte) -> Bool = "%byte_gt"
  #|fn Byte::op_ge(self : Byte, other : Byte) -> Bool = "%byte_ge"
  #|fn Byte::compare(self : Byte, other : Byte) -> Int = "%byte_compare"
  #|fn Byte::to_string(self : Byte) -> String = "%byte_to_string"
  #|fn Byte::hash(self : Byte) -> Int = "%byte_hash"
  #|fn Float::op_add(self : Float, other : Float) -> Float = "%float_add"
  #|fn Float::op_sub(self : Float, other : Float) -> Float = "%float_sub"
  #|fn Float::op_mul(self : Float, other : Float) -> Float = "%float_mul"
  #|fn Float::op_div(self : Float, other : Float) -> Float = "%float_div"
  #|fn Float::op_neg(self : Float) -> Float = "%float_neg"
  #|fn Float::op_equal(self : Float, other : Float) -> Bool = "%float_eq"
  #|fn Float::op_lt(self : Float, other : Float) -> Bool = "%float_lt"
  #|fn Float::op_le(self : Float, other : Float) -> Bool = "%float_le"
  #|fn Float::op_gt(self : Float, other : Float) -> Bool = "%float_gt"
  #|fn Float::op_ge(self : Float, other : Float) -> Bool = "%float_ge"
  #|fn Float::compare(self : Float, other : Float) -> Int = "%float_compare"
  #|fn Float::to_string(self : Float) -> String = "%float_to_string"
  #|fn Float::hash(self : Float) -> Int = "%float_hash"
  #|fn Int64::to_int(self : Int64) -> Int = "%int64_to_int"
  #|fn Int64::to_double(self : Int64) -> Double = "%int64_to_double"
  #|fn Int::to_int64(self : Int) -> Int64 = "%int_to_int64"
  #|fn UInt::to_int(self : UInt) -> Int = "%uint_to_int"
  #|fn UInt::to_double(self : UInt) -> Double = "%uint_to_double"
  #|fn Int::to_uint(self : Int) -> UInt = "%int_to_uint"
  #|fn UInt64::to_int(self : UInt64) -> Int = "%uint64_to_int"
  #|fn UInt64::to_double(self : UInt64) -> Double = "%uint64_to_double"
  #|fn Int::to_uint64(self : Int) -> UInt64 = "%int_to_uint64"
  #|fn Byte::to_int(self : Byte) -> Int = "%byte_to_int"
  #|fn Byte::to_double(self : Byte) -> Double = "%byte_to_double"
  #|fn Int::to_byte(self : Int) -> Byte = "%int_to_byte"
  #|fn Float::to_int(self : Float) -> Int = "%float_to_int"
  #|fn Float::to_double(self : Float) -> Double = "%float_to_double"
  #|fn Int::to_float(self : Int) -> Float = "%int_to_float"
  #|fn Double::to_float(self : Double) -> Float = "%double_to_float"
  #|fn Int64::to_uint64(self : Int64) -> UInt64 = "%int64_to_uint64"
  #|fn UInt64::to_int64(self : UInt64) -> Int64 = "%uint64_to_int64"
  #|fn UInt::to_uint64(self : UInt) -> UInt64 = "%uint_to_uint64"
  #|fn UInt64::to_uint(self : UInt64) -> UInt = "%uint64_to_uint"
  #|fn UInt::to_int64(self : UInt) -> Int64 = "%uint_to_int64"
  #|fn Byte::to_int64(self : Byte) -> Int64 = "%byte_to_int64"
  #|fn Byte::to_uint(self : Byte) -> UInt = "%byte_to_uint"
  #|fn Byte::to_uint64(self : Byte) -> UInt64 = "%byte_to_uint64"
  #|fn Int64::to_byte(self : Int64) -> Byte = "%int64_to_byte"
  #|impl Show for Int64 with to_string(self) { self.to_string() }
  #|impl Eq for Int64 with op_equal(a, b) { a == b }
  #|impl Compare for Int64 with compare(a, b) { a.compare(b) }
  #|impl Hash for Int64 with hash(self) { self.hash() }
  #|impl Default for Int64 with default() { 0L }
  #|impl Add for Int64 with op_add(a, b) { a + b }
  #|impl Sub for Int64 with op_sub(a, b) { a - b }
  #|impl Mul for Int64 with op_mul(a, b) { a * b }
  #|impl Div for Int64 with op_div(a, b) { a / b }
  #|impl Mod for Int64 with op_mod(a, b) { a % b }
  #|impl Neg for Int64 with op_neg(a) { -a }
  #|impl BitAnd for Int64 with op_land(a, b) { a & b }
  #|impl BitOr for Int64 with op_lor(a, b) { a | b }
  #|impl BitXOr for Int64 with op_lxor(a, b) { a ^ b }
  #|impl Shl for Int64 with op_shl(a, n) { a << n }
  #|impl Shr for Int64 with op_shr(a, n) { a >> n }
  #|impl Show for UInt with to_string(self) { self.to_string() }
  #|impl Eq for UInt with op_equal(a, b) { a == b }
  #|impl Compare for UInt with compare(a, b) { a.compare(b) }
  #|impl Hash for UInt with hash(self) { self.hash() }
  #|impl Default for UInt with default() { 0U }
  #|impl Add for UInt with op_add(a, b) { a + b }
  #|impl Sub for UInt with op_sub(a, b) { a - b }
  #|impl Mul for UInt with op_mul(a, b) { a * b }
  #|impl Div for UInt with op_div(a, b) { a / b }
  #|impl Mod for UInt with op_mod(a, b) { a % b }
  #|impl BitAnd for UInt with op_land(a, b) { a & b }
  #|impl BitOr for UInt with op_lor(a, b) { a | b }
  #|impl BitXOr for UInt with op_lxor(a, b) { a ^ b }
  #|impl Shl for UInt with op_shl(a, n) { a << n }
  #|impl Shr for UInt with op_shr(a, n) { a >> n }
  #|impl Show for UInt64 with to_string(self) { self.to_string() }
  #|impl Eq for UInt64 with op_equal(a, b) { a == b }
  #|impl Compare for UInt64 with compare(a, b) { a.compare(b) }
  #|impl Hash for UInt64 with hash(self) { self.hash() }
  #|impl Default for UInt64 with default() { 0UL }
  #|impl Add for UInt64 with op_add(a, b) { a + b }
  #|impl Sub for UInt64 with op_sub(a, b) { a - b }
  #|impl Mul for UInt64 with op_mul(a, b) { a * b }
  #|impl Div for UInt64 with op_div(a, b) { a / b }
  #|impl Mod for UInt64 with op_mod(a, b) { a % b }
  #|impl BitAnd for UInt64 with op_land(a, b) { a & b }
  #|impl BitOr for UInt64 with op_lor(a, b) { a | b }
  #|impl BitXOr for UInt64 with op_lxor(a, b) { a ^ b }
  #|impl Shl for UInt64 with op_shl(a, n) { a << n }
  #|impl Shr for UInt64 with op_shr(a, n) { a >> n }
  #|impl Show for Byte with to_string(self) { self.to_string() }
  #|impl Eq for Byte with op_equal(a, b) { a == b }
  #|impl Compare for Byte with compare(a, b) { a.compare(b) }
  #|impl Hash for Byte with hash(self) { self.hash() }
  #|impl Default for Byte with default() { b'\x00' }
  #|impl Add for Byte with op_add(a, b) { a + b }
  #|impl Sub for Byte with op_sub(a, b) { a - b }
  #|impl Mul for Byte with op_mul(a, b) { a * b }
  #|impl Div for Byte with op_div(a, b) { a / b }
  #|impl Mod for Byte with op_mod(a, b) { a % b }
  #|impl BitAnd for Byte with op_land(a, b) { a & b }
  #|impl BitOr for Byte with op_lor(a, b) { a | b }
  #|impl BitXOr for Byte with op_lxor(a, b) { a ^ b }
  #|impl Shl for Byte with op_shl(a, n) { a << n }
  #|impl Shr for Byte with op_shr(a, n) { a >> n }
  #|impl Show for Float with to_string(self) { self.to_string() }
  #|impl Eq for Float with op_equal(a, b) { a == b }
  #|impl Compare for Float with compare(a, b) { a.compare(b) }
  #|impl Hash for Float with hash(self) { self.hash() }
  #|impl Default for Float with default() { 0.0F }
  #|impl Add for Float with op_add(a, b) { a + b }
  #|impl Sub for Float with op_sub(a, b) { a - b }
  #|impl Mul for Float with op_mul(a, b) { a * b }
  #|impl Div for Float with op_div(a, b) { a / b }
  #|impl Neg for Float with op_neg(a) { -a }
  #|
  #|// ---- Map ------------------------------------------------------------------
  #|
  #|// A map from keys to values, in insertion order: `{ "a": 1 }`, `m[k]`,
  #|// `m[k] = v`, `for k, v in m`. (It is not MoonBit's `Map`: imported MoonBit
  #|// functions taking or returning a `Map` cannot be called.)
  #|struct Map[K, V] {
  #|  mut map_keys : Array[K]
  #|  mut map_values : Array[V]
  #|}
  #|
  #|fn[K, V] Map::new() -> Map[K, V] {
  #|  { map_keys: [], map_values: [] }
  #|}
  #|
  #|fn[K : Eq, V] Map::index_of(self : Map[K, V], key : K) -> Int {
  #|  let ks = self.map_keys
  #|  for i = 0; i < ks.length(); i = i + 1 {
  #|    if ks[i] == key {
  #|      return i
  #|    }
  #|  }
  #|  -1
  #|}
  #|
  #|fn[K : Eq, V] Map::set(self : Map[K, V], key : K, value : V) -> Unit {
  #|  let i = self.index_of(key)
  #|  if i < 0 {
  #|    self.map_keys.push(key)
  #|    self.map_values.push(value)
  #|  } else {
  #|    self.map_values[i] = value
  #|  }
  #|}
  #|
  #|fn[K : Eq, V] Map::get(self : Map[K, V], key : K) -> V? {
  #|  let i = self.index_of(key)
  #|  if i < 0 { None } else { Some(self.map_values[i]) }
  #|}
  #|
  #|fn[K : Eq, V] Map::op_get(self : Map[K, V], key : K) -> V? {
  #|  self.get(key)
  #|}
  #|
  #|fn[K : Eq, V] Map::op_set(self : Map[K, V], key : K, value : V) -> Unit {
  #|  self.set(key, value)
  #|}
  #|
  #|fn[K : Eq, V] Map::contains(self : Map[K, V], key : K) -> Bool {
  #|  self.index_of(key) >= 0
  #|}
  #|
  #|fn[K : Eq, V] Map::remove(self : Map[K, V], key : K) -> Unit {
  #|  let i = self.index_of(key)
  #|  if i >= 0 {
  #|    let ks : Array[K] = Array::new()
  #|    let vs : Array[V] = Array::new()
  #|    for j = 0; j < self.map_keys.length(); j = j + 1 {
  #|      if j != i {
  #|        ks.push(self.map_keys[j])
  #|        vs.push(self.map_values[j])
  #|      }
  #|    }
  #|    self.map_keys = ks
  #|    self.map_values = vs
  #|  }
  #|}
  #|
  #|fn[K, V] Map::length(self : Map[K, V]) -> Int {
  #|  self.map_keys.length()
  #|}
  #|
  #|fn[K, V] Map::size(self : Map[K, V]) -> Int {
  #|  self.map_keys.length()
  #|}
  #|
  #|fn[K, V] Map::is_empty(self : Map[K, V]) -> Bool {
  #|  self.map_keys.length() == 0
  #|}
  #|
  #|fn[K, V] Map::keys(self : Map[K, V]) -> Array[K] {
  #|  self.map_keys.slice(0, self.map_keys.length())
  #|}
  #|
  #|fn[K, V] Map::values(self : Map[K, V]) -> Array[V] {
  #|  self.map_values.slice(0, self.map_values.length())
  #|}
  #|
  #|fn[K, V] Map::to_array(self : Map[K, V]) -> Array[(K, V)] {
  #|  let out : Array[(K, V)] = Array::new()
  #|  for i = 0; i < self.map_keys.length(); i = i + 1 {
  #|    out.push((self.map_keys[i], self.map_values[i]))
  #|  }
  #|  out
  #|}
  #|
  #|fn[K : Eq, V] Map::from_array(xs : Array[(K, V)]) -> Map[K, V] {
  #|  let m : Map[K, V] = Map::new()
  #|  for i = 0; i < xs.length(); i = i + 1 {
  #|    m.set(xs[i].0, xs[i].1)
  #|  }
  #|  m
  #|}
  #|
  #|impl[K : Show, V : Show] Show for Map[K, V] with to_string(self) {
  #|  let mut s = "{"
  #|  for i = 0; i < self.map_keys.length(); i = i + 1 {
  #|    if i > 0 { s = s + ", " }
  #|    s = s + self.map_keys[i].to_string() + ": " + self.map_values[i].to_string()
  #|  }
  #|  s + "}"
  #|}
  #|
  #|// ---- HashMap ----------------------------------------------------------
  #|
  #|// A hash table (keys with `Hash + Eq`), in insertion order: `m[k]`,
  #|// `m[k] = v`, `for k, v in m`, `{}` and `{ k: v }` where a `HashMap` is
  #|// expected. The entries are in arrays; `hm_table` (open addressing, a size
  #|// that is a power of 2) has their positions + 1, or 0 for a free slot.
  #|// Removed entries stay (dead) until the table grows.
  #|struct HashMap[K, V] {
  #|  mut hm_keys : Array[K]
  #|  mut hm_values : Array[V]
  #|  mut hm_alive : Array[Bool]
  #|  mut hm_table : Array[Int]
  #|  mut hm_count : Int
  #|}
  #|
  #|fn[K, V] HashMap::new() -> HashMap[K, V] {
  #|  {
  #|    hm_keys: [],
  #|    hm_values: [],
  #|    hm_alive: [],
  #|    hm_table: Array::make(8, 0),
  #|    hm_count: 0,
  #|  }
  #|}
  #|
  #|// the slot of `key`: where it is, or the free slot that ends its probe
  #|fn[K : Hash + Eq, V] HashMap::slot(self : HashMap[K, V], key : K) -> Int {
  #|  let mask = self.hm_table.length() - 1
  #|  let mut i = key.hash() & mask
  #|  while true {
  #|    let e = self.hm_table[i]
  #|    if e == 0 {
  #|      return i
  #|    }
  #|    if self.hm_alive[e - 1] && self.hm_keys[e - 1] == key {
  #|      return i
  #|    }
  #|    i = (i + 1) & mask
  #|  }
  #|  i
  #|}
  #|
  #|// the position of `key` in the entries, or -1
  #|fn[K : Hash + Eq, V] HashMap::index_of(self : HashMap[K, V], key : K) -> Int {
  #|  self.hm_table[self.slot(key)] - 1
  #|}
  #|
  #|// a table twice as large (when needed), without the dead entries
  #|fn[K : Hash + Eq, V] HashMap::grow(self : HashMap[K, V]) -> Unit {
  #|  let ks : Array[K] = Array::new()
  #|  let vs : Array[V] = Array::new()
  #|  let alive : Array[Bool] = Array::new()
  #|  for i = 0; i < self.hm_keys.length(); i = i + 1 {
  #|    if self.hm_alive[i] {
  #|      ks.push(self.hm_keys[i])
  #|      vs.push(self.hm_values[i])
  #|      alive.push(true)
  #|    }
  #|  }
  #|  let mut size = self.hm_table.length()
  #|  while ks.length() * 2 >= size {
  #|    size = size * 2
  #|  }
  #|  self.hm_keys = ks
  #|  self.hm_values = vs
  #|  self.hm_alive = alive
  #|  self.hm_table = Array::make(size, 0)
  #|  for i = 0; i < ks.length(); i = i + 1 {
  #|    self.hm_table[self.slot(ks[i])] = i + 1
  #|  }
  #|}
  #|
  #|fn[K : Hash + Eq, V] HashMap::set(self : HashMap[K, V], key : K, value : V) -> Unit {
  #|  let s = self.slot(key)
  #|  let e = self.hm_table[s]
  #|  if e > 0 {
  #|    self.hm_values[e - 1] = value
  #|  } else {
  #|    self.hm_keys.push(key)
  #|    self.hm_values.push(value)
  #|    self.hm_alive.push(true)
  #|    self.hm_table[s] = self.hm_keys.length()
  #|    self.hm_count = self.hm_count + 1
  #|    if self.hm_keys.length() * 2 >= self.hm_table.length() {
  #|      self.grow()
  #|    }
  #|  }
  #|}
  #|
  #|fn[K : Hash + Eq, V] HashMap::get(self : HashMap[K, V], key : K) -> V? {
  #|  let i = self.index_of(key)
  #|  if i < 0 { None } else { Some(self.hm_values[i]) }
  #|}
  #|
  #|fn[K : Hash + Eq, V] HashMap::op_get(self : HashMap[K, V], key : K) -> V? {
  #|  self.get(key)
  #|}
  #|
  #|fn[K : Hash + Eq, V] HashMap::op_set(self : HashMap[K, V], key : K, value : V) -> Unit {
  #|  self.set(key, value)
  #|}
  #|
  #|fn[K : Hash + Eq, V] HashMap::contains(self : HashMap[K, V], key : K) -> Bool {
  #|  self.index_of(key) >= 0
  #|}
  #|
  #|fn[K : Hash + Eq, V] HashMap::remove(self : HashMap[K, V], key : K) -> Unit {
  #|  let i = self.index_of(key)
  #|  if i >= 0 {
  #|    self.hm_alive[i] = false
  #|    self.hm_count = self.hm_count - 1
  #|  }
  #|}
  #|
  #|fn[K, V] HashMap::length(self : HashMap[K, V]) -> Int {
  #|  self.hm_count
  #|}
  #|
  #|fn[K, V] HashMap::size(self : HashMap[K, V]) -> Int {
  #|  self.hm_count
  #|}
  #|
  #|fn[K, V] HashMap::is_empty(self : HashMap[K, V]) -> Bool {
  #|  self.hm_count == 0
  #|}
  #|
  #|fn[K, V] HashMap::keys(self : HashMap[K, V]) -> Array[K] {
  #|  let out : Array[K] = Array::new()
  #|  for i = 0; i < self.hm_keys.length(); i = i + 1 {
  #|    if self.hm_alive[i] { out.push(self.hm_keys[i]) }
  #|  }
  #|  out
  #|}
  #|
  #|fn[K, V] HashMap::values(self : HashMap[K, V]) -> Array[V] {
  #|  let out : Array[V] = Array::new()
  #|  for i = 0; i < self.hm_keys.length(); i = i + 1 {
  #|    if self.hm_alive[i] { out.push(self.hm_values[i]) }
  #|  }
  #|  out
  #|}
  #|
  #|fn[K, V] HashMap::to_array(self : HashMap[K, V]) -> Array[(K, V)] {
  #|  let out : Array[(K, V)] = Array::new()
  #|  for i = 0; i < self.hm_keys.length(); i = i + 1 {
  #|    if self.hm_alive[i] { out.push((self.hm_keys[i], self.hm_values[i])) }
  #|  }
  #|  out
  #|}
  #|
  #|fn[K : Hash + Eq, V] HashMap::from_array(xs : Array[(K, V)]) -> HashMap[K, V] {
  #|  let m : HashMap[K, V] = HashMap::new()
  #|  for i = 0; i < xs.length(); i = i + 1 {
  #|    m.set(xs[i].0, xs[i].1)
  #|  }
  #|  m
  #|}
  #|
  #|impl[K : Show, V : Show] Show for HashMap[K, V] with to_string(self) {
  #|  let mut s = "{"
  #|  let mut first = true
  #|  for i = 0; i < self.hm_keys.length(); i = i + 1 {
  #|    if self.hm_alive[i] {
  #|      if !first { s = s + ", " }
  #|      first = false
  #|      s = s + self.hm_keys[i].to_string() + ": " + self.hm_values[i].to_string()
  #|    }
  #|  }
  #|  s + "}"
  #|}
  #|
  #|// ---- traits -----------------------------------------------------------
  #|
  #|#mbt("Show")
  #|trait Show {
  #|  to_string(Self) -> String
  #|}
  #|
  #|impl Show for Int with to_string(self) { self.to_string() }
  #|impl Show for String with to_string(self) { self }
  #|impl Show for Bool with to_string(self) { self.to_string() }
  #|impl Show for Char with to_string(self) { self.to_string() }
  #|impl Show for Unit with to_string(self) { self.to_string() }
  #|impl Show for Nat with to_string(self) { self.to_string() }
  #|impl Show for Double with to_string(self) { self.to_string() }
  #|impl Show for BigInt with to_string(self) { self.to_string() }
  #|
  #|impl[T : Show] Show for Array[T] with to_string(self) {
  #|  let mut s = "["
  #|  for i = 0; i < self.length(); i = i + 1 {
  #|    if i > 0 { s = s + ", " }
  #|    s = s + self[i].to_string()
  #|  }
  #|  s + "]"
  #|}
  #|
  #|impl[T : Show] Show for List[T] with to_string(self) {
  #|  match self {
  #|    Nil => "Nil"
  #|    Cons(x, xs) => "Cons(" + x.to_string() + ", " + xs.to_string() + ")"
  #|  }
  #|}
  #|
  #|impl[T : Show] Show for Option[T] with to_string(self) {
  #|  match self {
  #|    None => "None"
  #|    Some(x) => "Some(" + x.to_string() + ")"
  #|  }
  #|}
  #|
  #|#mbt("Eq")
  #|trait Eq {
  #|  op_equal(Self, Self) -> Bool
  #|}
  #|
  #|impl Eq for Int with op_equal(a, b) { a == b }
  #|impl Eq for String with op_equal(a, b) { a == b }
  #|impl Eq for Bool with op_equal(a, b) { a == b }
  #|impl Eq for Char with op_equal(a, b) { a == b }
  #|impl Eq for Nat with op_equal(a, b) { a == b }
  #|impl Eq for Double with op_equal(a, b) { a == b }
  #|impl Eq for Unit with op_equal(_, _) { true }
  #|impl Eq for BigInt with op_equal(a, b) { a == b }
  #|
  #|impl[T : Eq] Eq for Option[T] with op_equal(a, b) {
  #|  match (a, b) {
  #|    (None, None) => true
  #|    (Some(x), Some(y)) => x == y
  #|    _ => false
  #|  }
  #|}
  #|
  #|impl[T : Eq] Eq for List[T] with op_equal(a, b) {
  #|  match (a, b) {
  #|    (Nil, Nil) => true
  #|    (Cons(x, xs), Cons(y, ys)) => x == y && xs == ys
  #|    _ => false
  #|  }
  #|}
  #|
  #|// decidable equality: `deq` proves that the values are equal, or that they
  #|// are not (`derive(DecEq)` also derives `Eq`)
  #|trait DecEq : Eq {
  #|  deq(a : Self, b : Self) -> Dec[a === b]
  #|}
  #|
  #|impl DecEq for Int with deq(a, b) { Int::deq(a, b) }
  #|impl DecEq for Int64 with deq(a, b) { Int64::deq(a, b) }
  #|impl DecEq for UInt with deq(a, b) { UInt::deq(a, b) }
  #|impl DecEq for UInt64 with deq(a, b) { UInt64::deq(a, b) }
  #|impl DecEq for Byte with deq(a, b) { Byte::deq(a, b) }
  #|impl DecEq for Char with deq(a, b) { Char::deq(a, b) }
  #|impl DecEq for String with deq(a, b) { String::deq(a, b) }
  #|impl DecEq for BigInt with deq(a, b) { BigInt::deq(a, b) }
  #|impl DecEq for Bool with deq(a, b) { Bool::deq(a, b) }
  #|impl DecEq for Unit with deq(a, b) { Unit::deq(a, b) }
  #|impl DecEq for Nat with deq(a, b) { Nat::deq(a, b) }
  #|
  #|impl[T : DecEq] DecEq for Option[T] with deq(a, b) {
  #|  match (a, b) {
  #|    (None, None) => Yes(Refl)
  #|    (Some(x), Some(y)) =>
  #|      match DecEq::deq(x, y) {
  #|        Yes(p) =>
  #|          match p {
  #|            Refl => Yes(Refl)
  #|          }
  #|        No(n) => No(h => match h { Refl => n(Refl) })
  #|      }
  #|    (None, Some(_)) => No(h => match h {})
  #|    (Some(_), None) => No(h => match h {})
  #|  }
  #|}
  #|
  #|impl[T : DecEq] DecEq for List[T] with deq(a, b) {
  #|  match (a, b) {
  #|    (Nil, Nil) => Yes(Refl)
  #|    (Cons(x, xs), Cons(y, ys)) =>
  #|      match DecEq::deq(x, y) {
  #|        Yes(p) =>
  #|          match p {
  #|            Refl =>
  #|              match DecEq::deq(xs, ys) {
  #|                Yes(q) =>
  #|                  match q {
  #|                    Refl => Yes(Refl)
  #|                  }
  #|                No(n) => No(h => match h { Refl => n(Refl) })
  #|              }
  #|          }
  #|        No(n) => No(h => match h { Refl => n(Refl) })
  #|      }
  #|    (Nil, Cons(_, _)) => No(h => match h {})
  #|    (Cons(_, _), Nil) => No(h => match h {})
  #|  }
  #|}
  #|
  #|impl[A : DecEq, B : DecEq] DecEq for Tuple2[A, B] with deq(x, y) {
  #|  match (x, y) {
  #|    ((a1, b1), (a2, b2)) =>
  #|      match DecEq::deq(a1, a2) {
  #|        Yes(p) =>
  #|          match p {
  #|            Refl =>
  #|              match DecEq::deq(b1, b2) {
  #|                Yes(q) =>
  #|                  match q {
  #|                    Refl => Yes(Refl)
  #|                  }
  #|                No(n) => No(h => match h { Refl => n(Refl) })
  #|              }
  #|          }
  #|        No(n) => No(h => match h { Refl => n(Refl) })
  #|      }
  #|  }
  #|}
  #|
  #|impl[A : DecEq, B : DecEq, C : DecEq] DecEq for Tuple3[A, B, C] with deq(x, y) {
  #|  match (x, y) {
  #|    ((a1, b1, c1), (a2, b2, c2)) =>
  #|      match DecEq::deq(a1, a2) {
  #|        Yes(p) =>
  #|          match p {
  #|            Refl =>
  #|              match DecEq::deq(b1, b2) {
  #|                Yes(q) =>
  #|                  match q {
  #|                    Refl =>
  #|                      match DecEq::deq(c1, c2) {
  #|                        Yes(r) =>
  #|                          match r {
  #|                            Refl => Yes(Refl)
  #|                          }
  #|                        No(n) => No(h => match h { Refl => n(Refl) })
  #|                      }
  #|                  }
  #|                No(n) => No(h => match h { Refl => n(Refl) })
  #|              }
  #|          }
  #|        No(n) => No(h => match h { Refl => n(Refl) })
  #|      }
  #|  }
  #|}
  #|
  #|#mbt("Compare")
  #|trait Compare : Eq {
  #|  compare(Self, Self) -> Int
  #|}
  #|
  #|impl Compare for Int with compare(a, b) { a.compare(b) }
  #|impl Compare for String with compare(a, b) { a.compare(b) }
  #|impl Compare for Char with compare(a, b) { a.compare(b) }
  #|impl Compare for Double with compare(a, b) { a.compare(b) }
  #|impl Compare for Bool with compare(a, b) {
  #|  if a == b { 0 } else if a { 1 } else { -1 }
  #|}
  #|impl Compare for Nat with compare(a, b) { a.compare(b) }
  #|impl Compare for Unit with compare(_, _) { 0 }
  #|impl Compare for BigInt with compare(a, b) { a.compare(b) }
  #|
  #|impl[T : Compare] Compare for Option[T] with compare(a, b) {
  #|  match (a, b) {
  #|    (None, None) => 0
  #|    (None, Some(_)) => -1
  #|    (Some(_), None) => 1
  #|    (Some(x), Some(y)) => x.compare(y)
  #|  }
  #|}
  #|
  #|impl[T : Compare] Compare for List[T] with compare(a, b) {
  #|  match (a, b) {
  #|    (Nil, Nil) => 0
  #|    (Nil, Cons(_, _)) => -1
  #|    (Cons(_, _), Nil) => 1
  #|    (Cons(x, xs), Cons(y, ys)) => {
  #|      let c = x.compare(y)
  #|      if c == 0 { xs.compare(ys) } else { c }
  #|    }
  #|  }
  #|}
  #|
  #|#mbt("Add")
  #|trait Add {
  #|  op_add(Self, Self) -> Self
  #|}
  #|
  #|impl Add for Int with op_add(a, b) { a + b }
  #|impl Add for String with op_add(a, b) { a + b }
  #|impl Add for Nat with op_add(a, b) { a + b }
  #|impl Add for Double with op_add(a, b) { a + b }
  #|impl Add for BigInt with op_add(a, b) { a + b }
  #|
  #|#mbt("Sub")
  #|trait Sub {
  #|  op_sub(Self, Self) -> Self
  #|}
  #|
  #|impl Sub for Int with op_sub(a, b) { a - b }
  #|impl Sub for Double with op_sub(a, b) { a - b }
  #|impl Sub for Nat with op_sub(a, b) { a - b }
  #|impl Sub for BigInt with op_sub(a, b) { a - b }
  #|
  #|#mbt("Mul")
  #|trait Mul {
  #|  op_mul(Self, Self) -> Self
  #|}
  #|
  #|impl Mul for Int with op_mul(a, b) { a * b }
  #|impl Mul for Double with op_mul(a, b) { a * b }
  #|impl Mul for Nat with op_mul(a, b) { a * b }
  #|impl Mul for BigInt with op_mul(a, b) { a * b }
  #|
  #|#mbt("Div")
  #|trait Div {
  #|  op_div(Self, Self) -> Self
  #|}
  #|
  #|impl Div for Int with op_div(a, b) { a / b }
  #|impl Div for Double with op_div(a, b) { a / b }
  #|impl Div for Nat with op_div(a, b) { a / b }
  #|impl Div for BigInt with op_div(a, b) { a / b }
  #|
  #|#mbt("Mod")
  #|trait Mod {
  #|  op_mod(Self, Self) -> Self
  #|}
  #|
  #|impl Mod for Int with op_mod(a, b) { a % b }
  #|impl Mod for Nat with op_mod(a, b) { a % b }
  #|impl Mod for BigInt with op_mod(a, b) { a % b }
  #|
  #|#mbt("Neg")
  #|trait Neg {
  #|  op_neg(Self) -> Self
  #|}
  #|
  #|impl Neg for Int with op_neg(a) { -a }
  #|impl Neg for Double with op_neg(a) { -a }
  #|impl Neg for BigInt with op_neg(a) { -a }
  #|
  #|#mbt("Default")
  #|trait Default {
  #|  default() -> Self
  #|}
  #|
  #|impl Default for Int with default() { 0 }
  #|impl Default for Double with default() { 0.0 }
  #|impl Default for String with default() { "" }
  #|impl Default for Bool with default() { false }
  #|impl Default for Unit with default() { () }
  #|impl Default for Nat with default() { Z }
  #|impl Default for BigInt with default() { BigInt::from_int(0) }
  #|impl[T] Default for Option[T] with default() { None }
  #|impl[T] Default for List[T] with default() { Nil }
  #|
  #|#mbt("BitAnd")
  #|trait BitAnd {
  #|  op_land(Self, Self) -> Self
  #|}
  #|
  #|impl BitAnd for Int with op_land(a, b) { a & b }
  #|impl BitAnd for Nat with op_land(a, b) { a & b }
  #|impl BitAnd for BigInt with op_land(a, b) { a & b }
  #|
  #|#mbt("BitOr")
  #|trait BitOr {
  #|  op_lor(Self, Self) -> Self
  #|}
  #|
  #|impl BitOr for Int with op_lor(a, b) { a | b }
  #|impl BitOr for Nat with op_lor(a, b) { a | b }
  #|impl BitOr for BigInt with op_lor(a, b) { a | b }
  #|
  #|#mbt("BitXOr")
  #|trait BitXOr {
  #|  op_lxor(Self, Self) -> Self
  #|}
  #|
  #|impl BitXOr for Int with op_lxor(a, b) { a ^ b }
  #|impl BitXOr for Nat with op_lxor(a, b) { a ^ b }
  #|impl BitXOr for BigInt with op_lxor(a, b) { a ^ b }
  #|
  #|#mbt("Shl")
  #|trait Shl {
  #|  op_shl(Self, Int) -> Self
  #|}
  #|
  #|impl Shl for Int with op_shl(a, n) { a << n }
  #|impl Shl for BigInt with op_shl(a, n) { a << n }
  #|
  #|#mbt("Shr")
  #|trait Shr {
  #|  op_shr(Self, Int) -> Self
  #|}
  #|
  #|impl Shr for Int with op_shr(a, n) { a >> n }
  #|impl Shr for BigInt with op_shr(a, n) { a >> n }
  #|
  #|// `hash` is MoonBit's `Hash::hash`; the impls of `#mbt` types are MoonBit
  #|// impls whose `hash_combine` combines this hash. The interpreter's hashes
  #|// differ from those of compiled programs.
  #|#mbt("Hash")
  #|trait Hash {
  #|  hash(Self) -> Int
  #|}
  #|
  #|impl Hash for Int with hash(self) { self }
  #|impl Hash for Bool with hash(self) { if self { 1 } else { 0 } }
  #|impl Hash for Char with hash(self) { self.to_int() }
  #|impl Hash for Unit with hash(_) { 0 }
  #|impl Hash for Nat with hash(self) { self.to_int() }
  #|impl Hash for BigInt with hash(self) { self.hash() }
  #|impl Hash for String with hash(self) {
  #|  let mut h = 0
  #|  for i = 0; i < self.length(); i = i + 1 {
  #|    h = h * 31 + self[i].to_int()
  #|  }
  #|  h
  #|}
  #|impl Hash for Double with hash(self) { self.to_string().hash() }
  #|impl[T : Hash] Hash for Option[T] with hash(self) {
  #|  match self {
  #|    None => 0
  #|    Some(x) => x.hash() * 31 + 1
  #|  }
  #|}
  #|impl[T : Hash] Hash for List[T] with hash(self) {
  #|  match self {
  #|    Nil => 0
  #|    Cons(x, xs) => x.hash() * 31 + xs.hash()
  #|  }
  #|}
  #|
  #|// `Json` is MoonBit's: its values are made and used by MoonBit code
  #|// (compiled programs), e.g. `@json` functions or `derive(ToJson)` of `#mbt`
  #|// types.
  #|#mbt("ToJson")
  #|trait ToJson {
  #|  to_json(Self) -> Json
  #|}
  #|
  #|fn int_to_json(x : Int) -> Json = "@mbt:trait:ToJson::to_json"
  #|fn double_to_json(x : Double) -> Json = "@mbt:trait:ToJson::to_json"
  #|fn string_to_json(x : String) -> Json = "@mbt:trait:ToJson::to_json"
  #|fn bool_to_json(x : Bool) -> Json = "@mbt:trait:ToJson::to_json"
  #|fn char_to_json(x : Char) -> Json = "@mbt:trait:ToJson::to_json"
  #|fn unit_to_json(x : Unit) -> Json = "@mbt:trait:ToJson::to_json"
  #|fn json_to_string(x : Json) -> String = "@mbt:trait:Show::to_string"
  #|fn json_equal(x : Json, y : Json) -> Bool = "@mbt:trait:Eq::equal"
  #|fn Json::stringify(self : Json) -> String = "@mbt:Json::stringify"
  #|
  #|impl ToJson for Int with to_json(self) { int_to_json(self) }
  #|impl ToJson for Double with to_json(self) { double_to_json(self) }
  #|impl ToJson for String with to_json(self) { string_to_json(self) }
  #|impl ToJson for Bool with to_json(self) { bool_to_json(self) }
  #|impl ToJson for Char with to_json(self) { char_to_json(self) }
  #|impl ToJson for Unit with to_json(self) { unit_to_json(self) }
  #|impl ToJson for Json with to_json(self) { self }
  #|impl Show for Json with to_string(self) { json_to_string(self) }
  #|impl Eq for Json with op_equal(a, b) { json_equal(a, b) }
  #|
  #|trait Monad(Self : [T] -> Type) {
  #|  fn[T] pure(T) -> Self[T]
  #|  fn[T, U] bind(Self[T], (T) -> Self[U]) -> Self[U]
  #|}
  #|
  #|impl Monad for Option with pure(x) { Some(x) }
  #|impl Monad for Option with bind(m, f) {
  #|  match m {
  #|    None => None
  #|    Some(x) => f(x)
  #|  }
  #|}
  #|
  #|fn[T, U] List::flat_map(self : List[T], f : (T) -> List[U]) -> List[U] {
  #|  match self {
  #|    Nil => Nil
  #|    Cons(x, xs) => f(x).append(xs.flat_map(f))
  #|  }
  #|}
  #|
  #|impl Monad for List with pure(x) { Cons(x, Nil) }
  #|impl Monad for List with bind(m, f) { m.flat_map(f) }
  #|
  #|// ---- IO and errors ----------------------------------------------------
  #|
  #|fn Error::to_string(self : Error) -> String = "%error_to_string"
  #|impl Show for Error with to_string(self) { self.to_string() }
  #|
  #|impl[T : Show, E : Show] Show for Result[T, E] with to_string(self) {
  #|  match self {
  #|    Ok(x) => "Ok(" + x.to_string() + ")"
  #|    Err(e) => "Err(" + e.to_string() + ")"
  #|  }
  #|}
  #|
  #|impl[A : Show, B : Show] Show for Tuple2[A, B] with to_string(self) {
  #|  match self {
  #|    (a, b) => "(" + a.to_string() + ", " + b.to_string() + ")"
  #|  }
  #|}
  #|impl[A : Show, B : Show, C : Show] Show for Tuple3[A, B, C] with to_string(self) {
  #|  match self {
  #|    (a, b, c) =>
  #|      "(" + a.to_string() + ", " + b.to_string() + ", " + c.to_string() + ")"
  #|  }
  #|}
  #|impl[A : Eq, B : Eq] Eq for Tuple2[A, B] with op_equal(x, y) {
  #|  match (x, y) {
  #|    ((a1, b1), (a2, b2)) => a1 == a2 && b1 == b2
  #|  }
  #|}
  #|impl[A : Eq, B : Eq, C : Eq] Eq for Tuple3[A, B, C] with op_equal(x, y) {
  #|  match (x, y) {
  #|    ((a1, b1, c1), (a2, b2, c2)) => a1 == a2 && b1 == b2 && c1 == c2
  #|  }
  #|}
  #|impl[A : Compare, B : Compare] Compare for Tuple2[A, B] with compare(x, y) {
  #|  match (x, y) {
  #|    ((a1, b1), (a2, b2)) => {
  #|      let c = a1.compare(a2)
  #|      if c == 0 { b1.compare(b2) } else { c }
  #|    }
  #|  }
  #|}
  #|impl[A : Compare, B : Compare, C : Compare] Compare for Tuple3[A, B, C] with compare(x, y) {
  #|  match (x, y) {
  #|    ((a1, b1, c1), (a2, b2, c2)) => {
  #|      let c = a1.compare(a2)
  #|      if c != 0 {
  #|        c
  #|      } else {
  #|        let d = b1.compare(b2)
  #|        if d == 0 { c1.compare(c2) } else { d }
  #|      }
  #|    }
  #|  }
  #|}
  #|impl[A : Hash, B : Hash] Hash for Tuple2[A, B] with hash(self) {
  #|  match self {
  #|    (a, b) => a.hash() * 31 + b.hash()
  #|  }
  #|}
  #|impl[A : Hash, B : Hash, C : Hash] Hash for Tuple3[A, B, C] with hash(self) {
  #|  match self {
  #|    (a, b, c) => (a.hash() * 31 + b.hash()) * 31 + c.hash()
  #|  }
  #|}
  #|
  #|fn[T] ignore(x : T) -> Unit {
  #|  let _ = x
  #|  ()
  #|}
  #|
  #|fn[T : Show] println(x : T) -> Unit {
  #|  print_string(x.to_string() + "\n")
  #|}
  #|
  #|fn[T : Show] print(x : T) -> Unit {
  #|  print_string(x.to_string())
  #|}
  #|
  #|fn[T : Eq + Show] assert_eq(a : T, b : T) -> Unit raise Failure {
  #|  if !(a == b) {
  #|    raise Failure("`" + a.to_string() + " == " + b.to_string() + "`")
  #|  }
  #|}
  #|
  #|fn[T : Eq + Show] assert_not_eq(a : T, b : T) -> Unit raise Failure {
  #|  if a == b {
  #|    raise Failure("`" + a.to_string() + " != " + b.to_string() + "`")
  #|  }
  #|}
  #|
  #|fn assert_true(b : Bool) -> Unit raise Failure {
  #|  if !b {
  #|    raise Failure("`true` expected")
  #|  }
  #|}
  #|
  #|fn assert_false(b : Bool) -> Unit raise Failure {
  #|  if b {
  #|    raise Failure("`false` expected")
  #|  }
  #|}
  #|
  #|fn[T] fail(msg : String) -> T raise Failure {
  #|  raise Failure(msg)
  #|}
  #|
