///|
/// The runtime support of compiled MoonBit++ programs, emitted at the top of
/// every generated `main.mbt`. Values are represented uniformly by `Value`
/// (like the interpreter's `RVal`).
let runtime_src : String =
  #|// ---- MoonBit++ runtime -------------------------------------------------
  #|
  #|/// Values. Each generated file adds the constructors of its datatypes
  #|/// (`extenum Value += { K_Exp_Add(Value, Value) }`) and registers a
  #|/// decoder for them in `con_decoders`.
  #|extenum Value {
  #|  VInt(Int)
  #|  VDouble(Double)
  #|  VInt64(Int64)
  #|  VUInt(UInt)
  #|  VUInt64(UInt64)
  #|  VByte(Byte)
  #|  VFloat(Float)
  #|  VStr(String)
  #|  VChar(Char)
  #|  VBool(Bool)
  #|  VUnit
  #|  VFun((Value) -> Value raise)
  #|  VArr(Array[Value])
  #|  /// A `Nat` (`Z` is 0, `S(n)` is n + 1).
  #|  VNat(BigInt)
  #|  VType
  #|  VForeign(Foreign)
  #|  /// A constructor that is not of the program (e.g. a MoonBit error).
  #|  VDyn(String, Array[Value])
  #|}
  #|
  #|/// Values of foreign MoonBit types (extended by mbtpp_imports.mbt).
  #|extenum Foreign {
  #|  FNone
  #|}
  #|
  #|/// The name and fields of a constructor value, by generated file.
  #|let con_decoders : Array[(Value) -> (String, Array[Value])?] = []
  #|
  #|/// The constructors by name: the value of a constructor and its fields,
  #|/// if the program has it (used by the driver of the splices).
  #|let con_makers : Array[(String, Array[Value]) -> Value?] = []
  #|
  #|fn con_decode(v : Value) -> (String, Array[Value])? {
  #|  match v {
  #|    VDyn(c, xs) => return Some((c, xs))
  #|    _ => ()
  #|  }
  #|  for d in con_decoders {
  #|    match d(v) {
  #|      Some(x) => return Some(x)
  #|      None => ()
  #|    }
  #|  }
  #|  None
  #|}
  #|
  #|/// The constructor of a value, if it is one.
  #|fn con_name(v : Value) -> String? {
  #|  con_decode(v).map(x => x.0)
  #|}
  #|
  #|/// The fields of a constructor value.
  #|fn con_fields(v : Value) -> Array[Value] {
  #|  match con_decode(v) {
  #|    Some((_, xs)) => xs
  #|    None => []
  #|  }
  #|}
  #|
  #|suberror Ctl {
  #|  CRaise(Value)
  #|  CReturn(Value)
  #|  CBreak
  #|  CContinue
  #|  CAbort(String)
  #|}
  #|
  #|enum Pat {
  #|  PAny
  #|  PCon(String, Array[Pat])
  #|  PLit(Value)
  #|  /// An erased field: matches without a value.
  #|  PErased
  #|  /// `S(…S(p))` of a Nat-like datatype: `n >= k` (`n == k` when exact);
  #|  /// its slots are `n - j`, or erased (-1).
  #|  PNat(Int, Bool, Array[Int])
  #|}
  #|
  #|///|
  #|/// Indexing of native arrays, with the errors of the uniform code.
  #|/// A runtime error in native code that does not raise: reported as
  #|/// `run_main` reports one, then the program stops.
  #|fn[T] rt_stop(msg : String) -> T {
  #|  rt_flush()
  #|  println("runtime error: " + msg)
  #|  panic()
  #|}
  #|
  #|///|
  #|/// Indexing in native code (no `raise`: no error to propagate).
  #|fn[T] rt_index(xs : Array[T], i : Int) -> T {
  #|  if i >= 0 && i < xs.length() {
  #|    xs[i]
  #|  } else {
  #|    rt_stop("index out of bounds: " + i.to_string())
  #|  }
  #|}
  #|
  #|///|
  #|fn[T] rt_index_set(xs : Array[T], i : Int, x : T) -> Unit {
  #|  if i >= 0 && i < xs.length() {
  #|    xs[i] = x
  #|  } else {
  #|    rt_stop("index out of bounds: " + i.to_string())
  #|  }
  #|}
  #|
  #|///|
  #|fn[T] rt_arr_get(xs : Array[T], i : Int) -> T raise {
  #|  if i >= 0 && i < xs.length() {
  #|    xs[i]
  #|  } else {
  #|    rt_fail("index out of bounds: " + i.to_string())
  #|  }
  #|}
  #|
  #|///|
  #|fn[T] rt_arr_set(xs : Array[T], i : Int, x : T) -> Unit raise {
  #|  if i >= 0 && i < xs.length() {
  #|    xs[i] = x
  #|  } else {
  #|    rt_fail("index out of bounds: " + i.to_string())
  #|  }
  #|}
  #|
  #|///|
  #|fn[T] rt_fail(msg : String) -> T raise {
  #|  raise CAbort(msg)
  #|}
  #|
  #|fn rt_break() -> Value raise {
  #|  raise CBreak
  #|}
  #|
  #|fn rt_continue() -> Value raise {
  #|  raise CContinue
  #|}
  #|
  #|fn rt_return(v : Value) -> Value raise {
  #|  raise CReturn(v)
  #|}
  #|
  #|fn rt_raise(v : Value) -> Value raise {
  #|  raise CRaise(v)
  #|}
  #|
  #|fn int_div(a : Int, b : Int) -> Int {
  #|  if b == 0 {
  #|    rt_stop("division by zero")
  #|  } else {
  #|    a / b
  #|  }
  #|}
  #|
  #|fn int_mod(a : Int, b : Int) -> Int {
  #|  if b == 0 {
  #|    rt_stop("division by zero")
  #|  } else {
  #|    a % b
  #|  }
  #|}
  #|
  #|fn apply(f : Value, a : Value) -> Value raise {
  #|  match f {
  #|    VFun(g) => g(a)
  #|    VType => VType
  #|    _ => rt_fail("cannot apply " + show_value(f))
  #|  }
  #|}
  #|
  #|fn truthy(v : Value) -> Bool raise {
  #|  match v {
  #|    VBool(b) => b
  #|    _ => rt_fail("expected a boolean")
  #|  }
  #|}
  #|
  #|fn value_eq(a : Value, b : Value) -> Bool {
  #|  match (a, b) {
  #|    (VInt(x), VInt(y)) => x == y
  #|    (VDouble(x), VDouble(y)) => x == y
  #|    (VInt64(x), VInt64(y)) => x == y
  #|    (VUInt(x), VUInt(y)) => x == y
  #|    (VUInt64(x), VUInt64(y)) => x == y
  #|    (VByte(x), VByte(y)) => x == y
  #|    (VFloat(x), VFloat(y)) => x == y
  #|    (VStr(x), VStr(y)) => x == y
  #|    (VChar(x), VChar(y)) => x == y
  #|    (VBool(x), VBool(y)) => x == y
  #|    (VUnit, VUnit) => true
  #|    (VNat(x), VNat(y)) => x == y
  #|    (VArr(xs), VArr(ys)) => {
  #|      if xs.length() != ys.length() {
  #|        return false
  #|      }
  #|      for k = 0; k < xs.length(); k = k + 1 {
  #|        if !value_eq(xs[k], ys[k]) {
  #|          return false
  #|        }
  #|      }
  #|      true
  #|    }
  #|    _ =>
  #|      match (con_name(a), con_name(b)) {
  #|        (Some(c), Some(d)) if c == d => {
  #|          let xs = con_fields(a)
  #|          let ys = con_fields(b)
  #|          if xs.length() != ys.length() {
  #|            return false
  #|          }
  #|          for k = 0; k < xs.length(); k = k + 1 {
  #|            if !value_eq(xs[k], ys[k]) {
  #|              return false
  #|            }
  #|          }
  #|          true
  #|        }
  #|        _ => false
  #|      }
  #|  }
  #|}
  #|
  #|fn match_pat(p : Pat, v : Value, out : Array[Value]) -> Bool {
  #|  match p {
  #|    PNat(k, exact, slots) =>
  #|      match v {
  #|        VNat(n) => {
  #|          let k = BigInt::from_int(k)
  #|          if (exact && n != k) || n < k {
  #|            return false
  #|          }
  #|          for j in slots {
  #|            out.push(if j < 0 { VType } else { VNat(n - BigInt::from_int(j)) })
  #|          }
  #|          return true
  #|        }
  #|        _ => return false
  #|      }
  #|    _ => ()
  #|  }
  #|  out.push(v)
  #|  match p {
  #|    PAny | PErased | PNat(_, _, _) => true
  #|    PCon(c, ps) =>
  #|      match con_name(v) {
  #|        Some(c2) if c2 == c => {
  #|          let args = con_fields(v)
  #|          let mut i = 0
  #|          for q in ps {
  #|            if q is PErased {
  #|              out.push(VType)
  #|              continue
  #|            }
  #|            if i >= args.length() || !match_pat(q, args[i], out) {
  #|              return false
  #|            }
  #|            i = i + 1
  #|          }
  #|          i == args.length()
  #|        }
  #|        _ => false
  #|      }
  #|    PLit(l) => value_eq(l, v)
  #|  }
  #|}
  #|
  #|fn match_pats(ps : Array[Pat], vs : Array[Value], out : Array[Value]) -> Bool {
  #|  out.clear()
  #|  for k = 0; k < ps.length(); k = k + 1 {
  #|    if !match_pat(ps[k], vs[k], out) {
  #|      return false
  #|    }
  #|  }
  #|  true
  #|}
  #|
  #|fn short_name(c : String) -> String {
  #|  match c.rev_find("::") {
  #|    Some(i) => c.unsafe_substring(start=i + 2, end=c.length())
  #|    None => c
  #|  }
  #|}
  #|
  #|fn value_id(v : Value) -> Value {
  #|  v
  #|}
  #|
  #|fn value_id_raise(v : Value) -> Value raise {
  #|  v
  #|}
  #|
  #|fn show_value(v : Value) -> String {
  #|  match v {
  #|    VInt(n) => n.to_string()
  #|    VDouble(d) => d.to_string()
  #|    VInt64(n) => n.to_string()
  #|    VUInt(n) => n.to_string()
  #|    VUInt64(n) => n.to_string()
  #|    VByte(n) => n.to_string()
  #|    VFloat(n) => n.to_string()
  #|    VStr(s) => s.escape()
  #|    VChar(c) => c.to_string().escape()
  #|    VBool(b) => b.to_string()
  #|    VUnit => "()"
  #|    VNat(n) => n.to_string()
  #|    VArr(xs) => "[" + xs.map(show_value).join(", ") + "]"
  #|    VFun(_) => "<function>"
  #|    VType => "<type>"
  #|    VForeign(_) => "<foreign>"
  #|    _ =>
  #|      match (con_name(v), con_fields(v)) {
  #|        (Some(c), []) => short_name(c)
  #|        (Some(c), args) =>
  #|          short_name(c) + "(" + args.map(show_value).join(", ") + ")"
  #|        (None, _) => "<value>"
  #|      }
  #|  }
  #|}
  #|
  #|impl Show for Value with output(self, logger) {
  #|  logger.write_string(show_value(self))
  #|}
  #|
  #|impl Eq for Value with equal(self, other) {
  #|  value_eq(self, other)
  #|}
  #|
  #|impl Compare for Value with compare(self, other) {
  #|  match (self, other) {
  #|    (VInt(x), VInt(y)) => x.compare(y)
  #|    (VDouble(x), VDouble(y)) => x.compare(y)
  #|    (VInt64(x), VInt64(y)) => x.compare(y)
  #|    (VUInt(x), VUInt(y)) => x.compare(y)
  #|    (VUInt64(x), VUInt64(y)) => x.compare(y)
  #|    (VByte(x), VByte(y)) => x.compare(y)
  #|    (VFloat(x), VFloat(y)) => x.compare(y)
  #|    (VStr(x), VStr(y)) => x.compare(y)
  #|    (VChar(x), VChar(y)) => x.compare(y)
  #|    (VBool(x), VBool(y)) => x.compare(y)
  #|    (VNat(x), VNat(y)) => x.compare(y)
  #|    _ => show_value(self).compare(show_value(other))
  #|  }
  #|}
  #|
  #|impl Hash for Value with hash_combine(self, hasher) {
  #|  hasher.combine_string(show_value(self))
  #|}
  #|
  #|let out_buf : StringBuilder = StringBuilder::new()
  #|
  #|// the markers of effect handlers (tt/ctl.mbt)
  #|let rt_marker : Ref[Int] = Ref::new(0)
  #|
  #|fn rt_write(s : String) -> Unit {
  #|  for c in s {
  #|    if c == '\n' {
  #|      println(out_buf.to_string())
  #|      out_buf.reset()
  #|    } else {
  #|      out_buf.write_char(c)
  #|    }
  #|  }
  #|}
  #|
  #|fn rt_flush() -> Unit {
  #|  if out_buf.to_string() != "" {
  #|    println(out_buf.to_string())
  #|    out_buf.reset()
  #|  }
  #|}
  #|
  #|fn as_int(v : Value) -> Int raise {
  #|  match v {
  #|    VInt(n) => n
  #|    _ => rt_fail("expected an Int, got " + show_value(v))
  #|  }
  #|}
  #|
  #|fn as_double(v : Value) -> Double raise {
  #|  match v {
  #|    VDouble(d) => d
  #|    _ => rt_fail("expected a Double, got " + show_value(v))
  #|  }
  #|}
  #|
  #|fn as_int64(v : Value) -> Int64 raise {
  #|  match v {
  #|    VInt64(x) => x
  #|    _ => rt_fail("expected a Int64, got " + show_value(v))
  #|  }
  #|}
  #|
  #|fn as_uint(v : Value) -> UInt raise {
  #|  match v {
  #|    VUInt(x) => x
  #|    _ => rt_fail("expected a UInt, got " + show_value(v))
  #|  }
  #|}
  #|
  #|fn as_uint64(v : Value) -> UInt64 raise {
  #|  match v {
  #|    VUInt64(x) => x
  #|    _ => rt_fail("expected a UInt64, got " + show_value(v))
  #|  }
  #|}
  #|
  #|fn as_byte(v : Value) -> Byte raise {
  #|  match v {
  #|    VByte(x) => x
  #|    _ => rt_fail("expected a Byte, got " + show_value(v))
  #|  }
  #|}
  #|
  #|fn as_float(v : Value) -> Float raise {
  #|  match v {
  #|    VFloat(x) => x
  #|    _ => rt_fail("expected a Float, got " + show_value(v))
  #|  }
  #|}
  #|
  #|fn as_str(v : Value) -> String raise {
  #|  match v {
  #|    VStr(s) => s
  #|    _ => rt_fail("expected a String, got " + show_value(v))
  #|  }
  #|}
  #|
  #|fn as_char(v : Value) -> Char raise {
  #|  match v {
  #|    VChar(c) => c
  #|    _ => rt_fail("expected a Char, got " + show_value(v))
  #|  }
  #|}
  #|
  #|fn as_bool(v : Value) -> Bool raise {
  #|  match v {
  #|    VBool(b) => b
  #|    _ => rt_fail("expected a Bool, got " + show_value(v))
  #|  }
  #|}
  #|
  #|fn as_arr(v : Value) -> Array[Value] raise {
  #|  match v {
  #|    VArr(xs) => xs
  #|    _ => rt_fail("expected an Array, got " + show_value(v))
  #|  }
  #|}
  #|
  #|fn as_nat(v : Value) -> BigInt raise {
  #|  match v {
  #|    VNat(n) => n
  #|    _ => rt_fail("expected a Nat, got " + show_value(v))
  #|  }
  #|}
  #|
  #|fn nat_of_int(i : Int) -> BigInt {
  #|  if i <= 0 {
  #|    0N
  #|  } else {
  #|    BigInt::from_int(i)
  #|  }
  #|}
  #|
  #|fn str_get(a : String, i : Int) -> Char {
  #|  match a.get_char(i) {
  #|    Some(c) => c
  #|    None => rt_stop("index out of bounds")
  #|  }
  #|}
  #|
  #|fn str_substring(a : String, i : Int, j : Int) -> String {
  #|  if i >= 0 && i <= j && j <= a.length() {
  #|    a.unsafe_substring(start=i, end=j)
  #|  } else {
  #|    rt_stop("index out of bounds")
  #|  }
  #|}
  #|
  #|fn int_to_char(a : Int) -> Char {
  #|  match a.to_char() {
  #|    Some(c) => c
  #|    None => rt_stop("invalid character code")
  #|  }
  #|}
  #|
  #|fn nat_sub(a : BigInt, b : BigInt) -> BigInt {
  #|  if a > b { a - b } else { 0N }
  #|}
  #|
  #|fn nat_div(a : BigInt, b : BigInt) -> BigInt {
  #|  if b == 0N { 0N } else { a / b }
  #|}
  #|
  #|fn nat_mod(a : BigInt, b : BigInt) -> BigInt {
  #|  if b == 0N { a } else { a % b }
  #|}
  #|
  #|fn nat_gcd(a : BigInt, b : BigInt) -> BigInt {
  #|  let mut x = a
  #|  let mut y = b
  #|  while y != 0N {
  #|    let t = x % y
  #|    x = y
  #|    y = t
  #|  }
  #|  x
  #|}
  #|
  #|fn nat_shr(a : BigInt, n : BigInt) -> BigInt {
  #|  if n.bit_length() > 31 { 0N } else { a >> n.to_int() }
  #|}
  #|
  #|fn nat_log2(a : BigInt) -> BigInt {
  #|  if a <= 1N { 0N } else { BigInt::from_int(a.bit_length() - 1) }
  #|}
  #|
  #|fn nat_of_bigint(a : BigInt) -> BigInt {
  #|  if a < 0N { 0N } else { a }
  #|}
  #|
  #|fn bigint_div(a : BigInt, b : BigInt) -> BigInt {
  #|  if b == 0N { rt_stop("division by zero") } else { a / b }
  #|}
  #|
  #|fn bigint_mod(a : BigInt, b : BigInt) -> BigInt {
  #|  if b == 0N { rt_stop("division by zero") } else { a % b }
  #|}
  #|
  #|fn as_unit(v : Value) -> Unit raise {
  #|  match v {
  #|    VUnit => ()
  #|    _ => rt_fail("expected (), got " + show_value(v))
  #|  }
  #|}
  #|
  #|fn prim(name : String, args : Array[Value]) -> Value raise {
  #|  match (name, args) {
  #|    ("%int_add", [VInt(a), VInt(b)]) => VInt(a + b)
  #|    ("%int_sub", [VInt(a), VInt(b)]) => VInt(a - b)
  #|    ("%int_mul", [VInt(a), VInt(b)]) => VInt(a * b)
  #|    ("%int_land", [VInt(a), VInt(b)]) => VInt(a & b)
  #|    ("%int_lor", [VInt(a), VInt(b)]) => VInt(a | b)
  #|    ("%int_lxor", [VInt(a), VInt(b)]) => VInt(a ^ b)
  #|    ("%int_shl", [VInt(a), VInt(b)]) => VInt(a << b)
  #|    ("%int_shr", [VInt(a), VInt(b)]) => VInt(a >> b)
  #|    ("%int_div", [VInt(_), VInt(0)]) | ("%int_mod", [VInt(_), VInt(0)]) =>
  #|      rt_fail("division by zero")
  #|    ("%int_div", [VInt(a), VInt(b)]) => VInt(a / b)
  #|    ("%int_mod", [VInt(a), VInt(b)]) => VInt(a % b)
  #|    ("%int_neg", [VInt(a)]) => VInt(-a)
  #|    ("%int_eq", [VInt(a), VInt(b)]) => VBool(a == b)
  #|    ("%int_lt", [VInt(a), VInt(b)]) => VBool(a < b)
  #|    ("%int_le", [VInt(a), VInt(b)]) => VBool(a <= b)
  #|    ("%int_gt", [VInt(a), VInt(b)]) => VBool(a > b)
  #|    ("%int_ge", [VInt(a), VInt(b)]) => VBool(a >= b)
  #|    ("%int_compare", [VInt(a), VInt(b)]) => VInt(a.compare(b))
  #|    ("%int_to_string", [VInt(a)]) => VStr(a.to_string())
  #|    ("%int_to_char", [VInt(a)]) =>
  #|      match a.to_char() {
  #|        Some(c) => VChar(c)
  #|        None => rt_fail("invalid character code")
  #|      }
  #|    ("%int_to_double", [VInt(a)]) => VDouble(a.to_double())
  #|    ("%str_add", [VStr(a), VStr(b)]) => VStr(a + b)
  #|    ("%str_eq", [VStr(a), VStr(b)]) => VBool(a == b)
  #|    ("%str_compare", [VStr(a), VStr(b)]) => VInt(a.compare(b))
  #|    ("%str_length", [VStr(a)]) => VInt(a.length())
  #|    ("%str_get", [VStr(a), VInt(i)]) =>
  #|      match a.get_char(i) {
  #|        Some(c) => VChar(c)
  #|        None => rt_fail("index out of bounds")
  #|      }
  #|    ("%str_substring", [VStr(a), VInt(i), VInt(j)]) =>
  #|      if i >= 0 && i <= j && j <= a.length() {
  #|        VStr(a.unsafe_substring(start=i, end=j))
  #|      } else {
  #|        rt_fail("index out of bounds")
  #|      }
  #|    ("%bool_eq", [VBool(a), VBool(b)]) => VBool(a == b)
  #|    ("%bool_not", [VBool(a)]) => VBool(!a)
  #|    ("%bool_to_string", [VBool(a)]) => VStr(a.to_string())
  #|    ("%char_eq", [VChar(a), VChar(b)]) => VBool(a == b)
  #|    ("%char_compare", [VChar(a), VChar(b)]) => VInt(a.compare(b))
  #|    ("%char_to_int", [VChar(a)]) => VInt(a.to_int())
  #|    ("%char_to_string", [VChar(a)]) => VStr(a.to_string())
  #|    ("%unit_to_string", [VUnit]) => VStr("()")
  #|    ("%double_add", [VDouble(a), VDouble(b)]) => VDouble(a + b)
  #|    ("%double_sub", [VDouble(a), VDouble(b)]) => VDouble(a - b)
  #|    ("%double_mul", [VDouble(a), VDouble(b)]) => VDouble(a * b)
  #|    ("%double_div", [VDouble(a), VDouble(b)]) => VDouble(a / b)
  #|    ("%double_neg", [VDouble(a)]) => VDouble(-a)
  #|    ("%double_eq", [VDouble(a), VDouble(b)]) => VBool(a == b)
  #|    ("%double_lt", [VDouble(a), VDouble(b)]) => VBool(a < b)
  #|    ("%double_le", [VDouble(a), VDouble(b)]) => VBool(a <= b)
  #|    ("%double_gt", [VDouble(a), VDouble(b)]) => VBool(a > b)
  #|    ("%double_ge", [VDouble(a), VDouble(b)]) => VBool(a >= b)
  #|    ("%double_compare", [VDouble(a), VDouble(b)]) => VInt(a.compare(b))
  #|    ("%double_to_string", [VDouble(a)]) => VStr(a.to_string())
  #|    ("%double_to_int", [VDouble(a)]) => VInt(a.to_int())
  #|    ("%int64_add", [VInt64(a), VInt64(b)]) => VInt64(a + b)
  #|    ("%int64_sub", [VInt64(a), VInt64(b)]) => VInt64(a - b)
  #|    ("%int64_mul", [VInt64(a), VInt64(b)]) => VInt64(a * b)
  #|    ("%int64_div", [VInt64(_), VInt64(b)]) if b == 0L => rt_fail("division by zero")
  #|    ("%int64_div", [VInt64(a), VInt64(b)]) => VInt64(a / b)
  #|    ("%int64_mod", [VInt64(_), VInt64(b)]) if b == 0L => rt_fail("division by zero")
  #|    ("%int64_mod", [VInt64(a), VInt64(b)]) => VInt64(a % b)
  #|    ("%int64_neg", [VInt64(a)]) => VInt64(-a)
  #|    ("%int64_land", [VInt64(a), VInt64(b)]) => VInt64(a & b)
  #|    ("%int64_lor", [VInt64(a), VInt64(b)]) => VInt64(a | b)
  #|    ("%int64_lxor", [VInt64(a), VInt64(b)]) => VInt64(a ^ b)
  #|    ("%int64_shl", [VInt64(a), VInt(b)]) => VInt64(a << b)
  #|    ("%int64_shr", [VInt64(a), VInt(b)]) => VInt64(a >> b)
  #|    ("%int64_eq", [VInt64(a), VInt64(b)]) => VBool(a == b)
  #|    ("%int64_lt", [VInt64(a), VInt64(b)]) => VBool(a < b)
  #|    ("%int64_le", [VInt64(a), VInt64(b)]) => VBool(a <= b)
  #|    ("%int64_gt", [VInt64(a), VInt64(b)]) => VBool(a > b)
  #|    ("%int64_ge", [VInt64(a), VInt64(b)]) => VBool(a >= b)
  #|    ("%int64_compare", [VInt64(a), VInt64(b)]) => VInt(a.compare(b))
  #|    ("%int64_to_string", [VInt64(a)]) => VStr(a.to_string())
  #|    ("%int64_hash", [VInt64(a)]) => VInt(a.hash())
  #|    ("%uint_add", [VUInt(a), VUInt(b)]) => VUInt(a + b)
  #|    ("%uint_sub", [VUInt(a), VUInt(b)]) => VUInt(a - b)
  #|    ("%uint_mul", [VUInt(a), VUInt(b)]) => VUInt(a * b)
  #|    ("%uint_div", [VUInt(_), VUInt(b)]) if b == 0U => rt_fail("division by zero")
  #|    ("%uint_div", [VUInt(a), VUInt(b)]) => VUInt(a / b)
  #|    ("%uint_mod", [VUInt(_), VUInt(b)]) if b == 0U => rt_fail("division by zero")
  #|    ("%uint_mod", [VUInt(a), VUInt(b)]) => VUInt(a % b)
  #|    ("%uint_land", [VUInt(a), VUInt(b)]) => VUInt(a & b)
  #|    ("%uint_lor", [VUInt(a), VUInt(b)]) => VUInt(a | b)
  #|    ("%uint_lxor", [VUInt(a), VUInt(b)]) => VUInt(a ^ b)
  #|    ("%uint_shl", [VUInt(a), VInt(b)]) => VUInt(a << b)
  #|    ("%uint_shr", [VUInt(a), VInt(b)]) => VUInt(a >> b)
  #|    ("%uint_eq", [VUInt(a), VUInt(b)]) => VBool(a == b)
  #|    ("%uint_lt", [VUInt(a), VUInt(b)]) => VBool(a < b)
  #|    ("%uint_le", [VUInt(a), VUInt(b)]) => VBool(a <= b)
  #|    ("%uint_gt", [VUInt(a), VUInt(b)]) => VBool(a > b)
  #|    ("%uint_ge", [VUInt(a), VUInt(b)]) => VBool(a >= b)
  #|    ("%uint_compare", [VUInt(a), VUInt(b)]) => VInt(a.compare(b))
  #|    ("%uint_to_string", [VUInt(a)]) => VStr(a.to_string())
  #|    ("%uint_hash", [VUInt(a)]) => VInt(a.hash())
  #|    ("%uint64_add", [VUInt64(a), VUInt64(b)]) => VUInt64(a + b)
  #|    ("%uint64_sub", [VUInt64(a), VUInt64(b)]) => VUInt64(a - b)
  #|    ("%uint64_mul", [VUInt64(a), VUInt64(b)]) => VUInt64(a * b)
  #|    ("%uint64_div", [VUInt64(_), VUInt64(b)]) if b == 0UL => rt_fail("division by zero")
  #|    ("%uint64_div", [VUInt64(a), VUInt64(b)]) => VUInt64(a / b)
  #|    ("%uint64_mod", [VUInt64(_), VUInt64(b)]) if b == 0UL => rt_fail("division by zero")
  #|    ("%uint64_mod", [VUInt64(a), VUInt64(b)]) => VUInt64(a % b)
  #|    ("%uint64_land", [VUInt64(a), VUInt64(b)]) => VUInt64(a & b)
  #|    ("%uint64_lor", [VUInt64(a), VUInt64(b)]) => VUInt64(a | b)
  #|    ("%uint64_lxor", [VUInt64(a), VUInt64(b)]) => VUInt64(a ^ b)
  #|    ("%uint64_shl", [VUInt64(a), VInt(b)]) => VUInt64(a << b)
  #|    ("%uint64_shr", [VUInt64(a), VInt(b)]) => VUInt64(a >> b)
  #|    ("%uint64_eq", [VUInt64(a), VUInt64(b)]) => VBool(a == b)
  #|    ("%uint64_lt", [VUInt64(a), VUInt64(b)]) => VBool(a < b)
  #|    ("%uint64_le", [VUInt64(a), VUInt64(b)]) => VBool(a <= b)
  #|    ("%uint64_gt", [VUInt64(a), VUInt64(b)]) => VBool(a > b)
  #|    ("%uint64_ge", [VUInt64(a), VUInt64(b)]) => VBool(a >= b)
  #|    ("%uint64_compare", [VUInt64(a), VUInt64(b)]) => VInt(a.compare(b))
  #|    ("%uint64_to_string", [VUInt64(a)]) => VStr(a.to_string())
  #|    ("%uint64_hash", [VUInt64(a)]) => VInt(a.hash())
  #|    ("%byte_add", [VByte(a), VByte(b)]) => VByte(a + b)
  #|    ("%byte_sub", [VByte(a), VByte(b)]) => VByte(a - b)
  #|    ("%byte_mul", [VByte(a), VByte(b)]) => VByte(a * b)
  #|    ("%byte_div", [VByte(_), VByte(b)]) if b == b'\x00' => rt_fail("division by zero")
  #|    ("%byte_div", [VByte(a), VByte(b)]) => VByte(a / b)
  #|    ("%byte_mod", [VByte(_), VByte(b)]) if b == b'\x00' => rt_fail("division by zero")
  #|    ("%byte_mod", [VByte(a), VByte(b)]) => VByte(a % b)
  #|    ("%byte_land", [VByte(a), VByte(b)]) => VByte(a & b)
  #|    ("%byte_lor", [VByte(a), VByte(b)]) => VByte(a | b)
  #|    ("%byte_lxor", [VByte(a), VByte(b)]) => VByte(a ^ b)
  #|    ("%byte_shl", [VByte(a), VInt(b)]) => VByte(a << b)
  #|    ("%byte_shr", [VByte(a), VInt(b)]) => VByte(a >> b)
  #|    ("%byte_eq", [VByte(a), VByte(b)]) => VBool(a == b)
  #|    ("%byte_lt", [VByte(a), VByte(b)]) => VBool(a < b)
  #|    ("%byte_le", [VByte(a), VByte(b)]) => VBool(a <= b)
  #|    ("%byte_gt", [VByte(a), VByte(b)]) => VBool(a > b)
  #|    ("%byte_ge", [VByte(a), VByte(b)]) => VBool(a >= b)
  #|    ("%byte_compare", [VByte(a), VByte(b)]) => VInt(a.compare(b))
  #|    ("%byte_to_string", [VByte(a)]) => VStr(a.to_string())
  #|    ("%byte_hash", [VByte(a)]) => VInt(a.hash())
  #|    ("%float_add", [VFloat(a), VFloat(b)]) => VFloat(a + b)
  #|    ("%float_sub", [VFloat(a), VFloat(b)]) => VFloat(a - b)
  #|    ("%float_mul", [VFloat(a), VFloat(b)]) => VFloat(a * b)
  #|    ("%float_div", [VFloat(a), VFloat(b)]) => VFloat(a / b)
  #|    ("%float_neg", [VFloat(a)]) => VFloat(-a)
  #|    ("%float_eq", [VFloat(a), VFloat(b)]) => VBool(a == b)
  #|    ("%float_lt", [VFloat(a), VFloat(b)]) => VBool(a < b)
  #|    ("%float_le", [VFloat(a), VFloat(b)]) => VBool(a <= b)
  #|    ("%float_gt", [VFloat(a), VFloat(b)]) => VBool(a > b)
  #|    ("%float_ge", [VFloat(a), VFloat(b)]) => VBool(a >= b)
  #|    ("%float_compare", [VFloat(a), VFloat(b)]) => VInt(a.compare(b))
  #|    ("%float_to_string", [VFloat(a)]) => VStr(a.to_string())
  #|    ("%float_hash", [VFloat(a)]) => VInt(a.hash())
  #|    ("%int64_to_int", [VInt64(a)]) => VInt(a.to_int())
  #|    ("%int64_to_double", [VInt64(a)]) => VDouble(a.to_double())
  #|    ("%int_to_int64", [VInt(a)]) => VInt64(a.to_int64())
  #|    ("%uint_to_int", [VUInt(a)]) => VInt(a.to_int())
  #|    ("%uint_to_double", [VUInt(a)]) => VDouble(a.to_double())
  #|    ("%int_to_uint", [VInt(a)]) => VUInt(a.to_uint())
  #|    ("%uint64_to_int", [VUInt64(a)]) => VInt(a.to_int())
  #|    ("%uint64_to_double", [VUInt64(a)]) => VDouble(a.to_double())
  #|    ("%int_to_uint64", [VInt(a)]) => VUInt64(a.to_uint64())
  #|    ("%byte_to_int", [VByte(a)]) => VInt(a.to_int())
  #|    ("%byte_to_double", [VByte(a)]) => VDouble(a.to_double())
  #|    ("%int_to_byte", [VInt(a)]) => VByte(a.to_byte())
  #|    ("%float_to_int", [VFloat(a)]) => VInt(a.to_int())
  #|    ("%float_to_double", [VFloat(a)]) => VDouble(a.to_double())
  #|    ("%int_to_float", [VInt(a)]) => VFloat(Float::from_int(a))
  #|    ("%double_to_float", [VDouble(a)]) => VFloat(Float::from_double(a))
  #|    ("%int64_to_uint64", [VInt64(a)]) => VUInt64(a.to_uint64())
  #|    ("%uint64_to_int64", [VUInt64(a)]) => VInt64(a.to_int64())
  #|    ("%uint_to_uint64", [VUInt(a)]) => VUInt64(a.to_uint64())
  #|    ("%uint64_to_uint", [VUInt64(a)]) => VUInt(a.to_uint())
  #|    ("%uint_to_int64", [VUInt(a)]) => VInt64(a.to_int64())
  #|    ("%byte_to_int64", [VByte(a)]) => VInt64(a.to_int64())
  #|    ("%byte_to_uint", [VByte(a)]) => VUInt(a.to_uint())
  #|    ("%byte_to_uint64", [VByte(a)]) => VUInt64(a.to_uint64())
  #|    ("%int64_to_byte", [VInt64(a)]) => VByte(a.to_byte())
  #|    ("%print", [VStr(s)]) => {
  #|      rt_write(s)
  #|      VUnit
  #|    }
  #|    ("%effect_marker", _) => {
  #|      rt_marker.val = rt_marker.val + 1
  #|      VInt(rt_marker.val)
  #|    }
  #|    ("%nat_succ", [VNat(n)]) => VNat(n + 1N)
  #|    ("%nat_of_int", [VInt(i)]) => VNat(nat_of_int(i))
  #|    ("%nat_to_int", [VNat(n)]) => VInt(n.to_int())
  #|    ("%nat_add", [VNat(a), VNat(b)]) => VNat(a + b)
  #|    ("%nat_mul", [VNat(a), VNat(b)]) => VNat(a * b)
  #|    ("%nat_eq", [VNat(a), VNat(b)]) => VBool(a == b)
  #|    ("%nat_compare", [VNat(a), VNat(b)]) => VInt(a.compare(b))
  #|    ("%nat_to_string", [VNat(n)]) => VStr(n.to_string())
  #|    ("%axiom", _) => VType
  #|    ("%quote", [s, f]) => make_code(s, f)
  #|    ("%splice", [c, _, _]) | ("%run", [c]) => apply(c, VUnit)
  #|    ("%physical_equal", [a, b]) => VBool(physical_equal(a, b))
  #|    ("%panic", _) => rt_fail("panic")
  #|    ("%abort", [VStr(s)]) => rt_fail(s)
  #|    ("%error_to_string", [e]) => VStr(show_value(e))
  #|    ("%array_make", [VInt(n), x]) => VArr(Array::make(n, x))
  #|    ("%array_new", _) => VArr([])
  #|    ("%array_length", [VArr(xs)]) => VInt(xs.length())
  #|    ("%array_get", [VArr(xs), VInt(i)]) =>
  #|      if i >= 0 && i < xs.length() {
  #|        xs[i]
  #|      } else {
  #|        rt_fail("index out of bounds: " + i.to_string())
  #|      }
  #|    ("%array_set", [VArr(xs), VInt(i), x]) =>
  #|      if i >= 0 && i < xs.length() {
  #|        xs[i] = x
  #|        VUnit
  #|      } else {
  #|        rt_fail("index out of bounds: " + i.to_string())
  #|      }
  #|    ("%array_push", [VArr(xs), x]) => {
  #|      xs.push(x)
  #|      VUnit
  #|    }
  #|    _ => rt_fail("primitive " + name + " failed")
  #|  }
  #|}
  #|
  #|/// Code (`code { e }`): its body `f`, to be run on the code `s` of its
  #|/// splices.
  #|fn make_code(s : Value, f : Value) -> Value {
  #|  VFun(_ => apply(f, s))
  #|}
  #|
  #|/// A foreign MoonBit error, as a MoonBit++ value.
  #|fn foreign_error(e : Error) -> Value {
  #|  VDyn("MoonBitError", [VStr(e.to_string())])
  #|}
  #|
  #|fn run_main(f : () -> Value raise) -> Unit {
  #|  try {
  #|    ignore(f())
  #|  } catch {
  #|    e => report_error(e)
  #|  }
  #|  rt_flush()
  #|}
  #|
  #|/// Report an error that escaped `main`.
  #|fn report_error(e : Error) -> Unit {
  #|  match e {
  #|    CReturn(_) => ()
  #|    CRaise(e) => {
  #|      rt_flush()
  #|      println("uncaught error: " + show_value(e))
  #|    }
  #|    CAbort(m) => {
  #|      rt_flush()
  #|      println("runtime error: " + m)
  #|    }
  #|    e => {
  #|      rt_flush()
  #|      println("runtime error: " + e.to_string())
  #|    }
  #|  }
  #|  rt_flush()
  #|}
  #|
