///|
/// MoonBit++ → MoonBit: elaborated core terms are translated to MoonBit
/// code over the uniform representation `Value` of the runtime
/// (`runtime.mbt`). Only the globals reachable from `main` are emitted.
///
/// - A function of n parameters becomes a MoonBit function; a saturated
///   call is a direct call, and `<id>_v()` is the function as a value
///   (curried closure) for other uses.
/// - Implicit parameters whose type is a sort (type parameters) are erased.
/// - Data are native: every constructor used by the program is a variant
///   of the generated `Value` enum (`K_Exp_Add(Value, Value)`), without
///   indices and erased fields, so `match` is a native MoonBit `match`.
///   Constructors and primitive operations of saturated applications are
///   inlined.
/// - Calls of imported MoonBit functions go through generated glue that
///   converts between `Value` and MoonBit types (see `ffi.mbt`).
pub suberror CodegenError {
  CodegenError(String)
}

///|
priv struct Gen {
  ids : Map[String, String]
  todo : Array[String]
  /// The generated code, by output file (see files.mbt).
  files : Map[String, StringBuilder]
  /// The file of the global being emitted.
  mut cur_file : String
  /// MoonBit type of a foreign value -> its `Foreign` constructor.
  foreign : Map[String, String]
  foreign_order : Array[String]
  /// MoonBit wrappers of trait objects (`&Tr` passed to MoonBit), by trait.
  dyn_wrappers : Map[String, String]
  /// Package path -> alias, for imported packages.
  aliases : Map[String, String]
  er : Erasure
  mut fresh : Int32
  /// Datatypes that can be native enums (see typed.mbt).
  enums_ok : Map[String, Bool]
  enums_done : Array[String]
  /// Functions with a native translation.
  typed_set : Array[String]
  /// Translating the async version of an effect polymorphic function: the
  /// function types whose effects end with a variable are async.
  mut async_vars : Bool
  /// The async versions (`f_ta`) made so far, and those being made.
  async_fns : Map[String, String]
  async_busy : Array[String]
  /// The native result type of the function being translated.
  mut cur_result : NTy?
  /// The step of the innermost native `for` loop, run by `continue`.
  mut cur_step : String?
  /// While deciding the typed functions nothing is emitted.
  mut dry : Bool
  scheduled : Map[String, Bool]
  /// Bounds `(type parameter, trait)` of the function being translated.
  mut cur_bounds : Array[(Int32, String)]
  /// Instances of `#mbt` traits that become MoonBit `impl`s.
  mbt_impls : Array[String]
  impls_done : Array[String]
  traits_done : Array[String]
  /// While explaining why a `#mbt` function is not native: the first term
  /// that is not in the fragment.
  mut diagnose : Bool
  mut culprit : String?
  /// Constructors used, as variants of `Value`: name -> (variant, arity).
  ctors : Map[String, (String, Int32)]
  ctor_order : Array[String]
  /// Datatypes that are `Nat` after erasure (see natlike.mbt).
  nat_likes : Map[String, NatLike?]
  /// Global constants (`let`) with a native version `<id>_n()` (see
  /// `compute_typed`).
  native_consts : Array[String]
  /// Whether the native version of a function or constant may raise (see
  /// `compute_typed`); not raising, it is a MoonBit function without
  /// `raise`, whose calls need no error propagation.
  raising : Map[String, Bool]
  /// While translating native code: whether it may raise.
  mut may_raise : Bool
  /// The global being emitted.
  mut cur_global : String
  /// Uses of async functions outside of native code (which are errors):
  /// (async function, global using it).
  async_misuse : Array[(String, String)]
}

///|
/// A fresh local name based on a source name.
fn Gen::name(self : Gen, base : String) -> String {
  self.fresh = self.fresh + 1
  let buf = StringBuilder()
  for c in base {
    if (c >= 'a' && c <= 'z') || (c >= '0' && c <= '9') || c == '_' {
      buf.write_char(c)
    } else if c >= 'A' && c <= 'Z' {
      buf.write_char(Int32::unsafe_to_char(c.to_int() + 32))
    }
  }
  let b = buf.to_string()
  let b = if b == "" ||
    b == "_" ||
    (b.get_char(0).unwrap() >= '0' && b.get_char(0).unwrap() <= '9') {
    "v"
  } else if b.has_prefix("_") {
    "v" + b
  } else {
    b
  }
  b + "_" + self.fresh.to_string()
}

///|
/// The MoonBit identifier of a global (scheduling it for emission).
fn Gen::gid(self : Gen, name : String) -> String {
  match self.ids.get(name) {
    Some(id) => {
      self.schedule(name)
      id
    }
    None => {
      let buf = StringBuilder()
      let short = match name.rev_find("::") {
        Some(_) => name
        None => name
      }
      for c in short {
        if (c >= 'a' && c <= 'z') || (c >= '0' && c <= '9') {
          buf.write_char(c)
        } else if c >= 'A' && c <= 'Z' {
          buf.write_char(Int32::unsafe_to_char(c.to_int() + 32))
        } else if c == ':' || c == '.' || c == '$' || c == '_' {
          if !buf.to_string().has_suffix("_") {
            buf.write_char('_')
          }
        }
      }
      let id = "f" + self.ids.length().to_string() + "_" + buf.to_string()
      self.ids.set(name, id)
      self.schedule(name)
      id
    }
  }
}

///|
fn Gen::schedule(self : Gen, name : String) -> Unit {
  if !self.dry && !self.scheduled.contains(name) {
    self.scheduled.set(name, true)
    self.todo.push(name)
  }
}

// ---------------------------------------------------------------------------
// Globals

///|
/// Number of leading lambdas of a term.
fn lam_count(t : @tt.Tm) -> Int32 {
  match t {
    Lam(_, _, _, b) => 1 + lam_count(b)
    _ => 0
  }
}

///|
/// The parameters of a global function (its arity), if it is one.
fn func_arity(name : String) -> Int32? {
  match @tt.globals.get(name) {
    Some({ kind: GFunc(Some(body), _, n), .. }) if n > 0 && lam_count(body) >= n =>
      Some(n)
    _ => None
  }
}

///|
fn is_sort_like(t : @tt.Tm) -> Bool {
  match t {
    U | PropU => true
    Pi(_, _, _, _, b) => is_sort_like(b)
    _ => false
  }
}

///|
/// Which of the first `n` parameters of a global are erased: implicit
/// parameters whose type is a sort (type parameters).
fn erased_params(name : String, n : Int32) -> Array[Bool] {
  let out : Array[Bool] = []
  let proofs = @tt.proof_params(name, n)
  let mut t = match @tt.globals.get(name) {
    Some(g) => g.ty
    None => @tt.Tm::U
  }
  for k = 0; k < n; k = k + 1 {
    match t {
      Pi(_, i, _, a, b) => {
        out.push((i == Impl && is_sort_like(a)) || proofs[k])
        t = b
      }
      _ => out.push(proofs[k])
    }
  }
  out
}

///|
/// Does `t` contain a `return` of the function it is the body of?
fn has_return(t : @tt.Tm) -> Bool {
  match t {
    Return(_) => true
    Lam(_, _, _, _) => false
    App(f, a, _) => has_return(f) || has_return(a)
    Let(_, _, v, b) | LetMut(_, _, v, b) => has_return(v) || has_return(b)
    Match(ss, cls) =>
      ss.iter().any(has_return) || cls.iter().any(cl => has_return(cl.body))
    Try(b, cls) => has_return(b) || cls.iter().any(cl => has_return(cl.body))
    Assign(_, v) | Raise(v) => has_return(v)
    While(c, b, s) => has_return(c) || has_return(b) || has_return(s)
    Seq(a, b) | Defer(a, b) => has_return(a) || has_return(b)
    ArrayLit(es) => es.iter().any(has_return)
    _ => false
  }
}

///|
fn catch_return(has_ret : Bool, body : String) -> String {
  if has_ret {
    "try {\n(" + body + ")\n} catch {\nCReturn(r) => r\ne => raise e\n}"
  } else {
    body
  }
}

// ---------------------------------------------------------------------------
// Terms

///|
priv enum Local {
  LVar(String)
  LMut(String)
  LErased
}

///|
fn local_code(l : Local) -> String {
  match l {
    LVar(n) => n
    LMut(n) => n + ".val"
    LErased => "VType"
  }
}

///|
fn push_local(env : Array[Local], l : Local) -> Array[Local] {
  let e = env.copy()
  e.push(l)
  e
}

///|
fn double_lit(d : Double) -> String {
  let s = d.to_string()
  if s == "Infinity" {
    "(1.0 / 0.0)"
  } else if s == "-Infinity" {
    "(-1.0 / 0.0)"
  } else if s == "NaN" {
    "(0.0 / 0.0)"
  } else if s.contains(".") || s.contains("e") {
    s
  } else {
    s + ".0"
  }
}

///|
fn char_lit(c : Char) -> String {
  let digits = "0123456789abcdef"
  let mut n = c.to_int()
  let mut hex = ""
  while true {
    hex = digits.get_char(n % 16).unwrap().to_string() + hex
    n = n / 16
    if n == 0 {
      break
    }
  }
  "'\\u{" + hex + "}'"
}

///|
fn lit_code(l : @tt.Lit) -> String {
  match l {
    LInt(n) => "VInt(" + n.to_string() + ")"
    LStr(s) => "VStr(" + s.escape() + ")"
    LChar(c) => "VChar(" + char_lit(c) + ")"
    LBool(b) => "VBool(" + b.to_string() + ")"
    LUnit => "VUnit"
    LDouble(d) => "VDouble(" + double_lit(d) + ")"
    LInt64(n) => "VInt64(" + n.to_string() + "L)"
    LUInt(n) => "VUInt(" + n.to_string() + "U)"
    LUInt64(n) => "VUInt64(" + n.to_string() + "UL)"
    LByte(b) => "VByte(" + byte_lit(b) + ")"
    LFloat(f) => "VFloat((" + double_lit(f.to_double()) + " : Float))"
  }
}

///|
/// A MoonBit byte literal.
fn byte_lit(b : Byte) -> String {
  let n = b.to_int()
  let hex = "0123456789abcdef"
  "b'\\x" +
  hex[n / 16:n / 16 + 1].to_string() +
  hex[n % 16:n % 16 + 1].to_string() +
  "'"
}

///|
/// A pattern of the runtime matcher (see `clauses_dynamic`).
fn Gen::pat_code(self : Gen, p : @tt.CPat) -> String {
  match p {
    CPVar(_) | CPWild => "PAny"
    CPCon(c, _) if self.nat_con(c) is Some(_) => {
      // the slots: `n - j`, or erased (-1)
      let slots : Array[String] = []
      let (k, exact) = self.nat_pat(p, j => {
        slots.push(j.unwrap_or(-1).to_string())
      })
      "PNat(\{k}, \{exact}, [" + slots.join(", ") + "])"
    }
    CPCon(c, ps) => {
      let subs = ps.mapi((j, q) => {
        if self.er.con_erased(c, j) {
          "PErased"
        } else {
          self.pat_code(q)
        }
      })
      "PCon(" + c.escape() + ", [" + subs.join(", ") + "])"
    }
    CPLit(l) => "PLit(" + lit_code(l) + ")"
  }
}

///|
fn has_double_pat(p : @tt.CPat) -> Bool {
  match p {
    CPLit(LDouble(_) | LFloat(_)) => true
    CPCon(_, ps) => ps.iter().any(has_double_pat)
    _ => false
  }
}

///|
fn short_con(c : String) -> String {
  match c.rev_find("::") {
    Some(i) => c.unsafe_substring(start=i + 2, end=c.length())
    None => c
  }
}

///|
/// A MoonBit pattern for a core pattern; `names` receives the variables of
/// its slots (in slot order), `conds` the tests it needs besides the pattern.
fn Gen::native_pat(
  self : Gen,
  p : @tt.CPat,
  names : Array[Local],
  conds : Array[String],
) -> String {
  match p {
    CPCon(c, _) if self.nat_con(c) is Some(_) => {
      let n = self.name("n")
      let (k, exact) = self.nat_pat(p, j => {
        names.push(
          match j {
            Some(0) => LVar(n)
            Some(j) => LVar("VNat(as_nat(\{n}) - \{j}N)")
            None => LErased
          },
        )
      })
      conds.push("as_nat(\{n}) " + (if exact { "==" } else { ">=" }) + " \{k}N")
      var_marker + n + end_marker
    }
    CPVar(x) => {
      let n = self.name(x)
      names.push(LVar(n))
      var_marker + n + end_marker
    }
    CPWild => {
      let n = self.name("w")
      names.push(LVar(n))
      var_marker + n + end_marker
    }
    CPCon(c, ps) => {
      let n = self.name(short_con(c))
      names.push(LVar(n))
      let subs : Array[String] = []
      for j = 0; j < ps.length(); j = j + 1 {
        if self.er.con_erased(c, j) {
          // an erased field (only variables bind it, see erase.mbt)
          names.push(LErased)
        } else {
          subs.push(self.native_pat(ps[j], names, conds))
        }
      }
      "(" + self.con_code(c, subs) + as_marker + n + end_marker + ")"
    }
    CPLit(l) => {
      let n = self.name("lit")
      names.push(LVar(n))
      let lp = match l {
        LInt(k) => "VInt(" + k.to_string() + ")"
        LStr(s) => "VStr(" + s.escape() + ")"
        LChar(c) => "VChar(" + char_lit(c) + ")"
        LBool(b) => "VBool(" + b.to_string() + ")"
        LUnit => "VUnit"
        LDouble(_) | LFloat(_) => "_"
        LInt64(n) => "VInt64(" + n.to_string() + "L)"
        LUInt(n) => "VUInt(" + n.to_string() + "U)"
        LUInt64(n) => "VUInt64(" + n.to_string() + "UL)"
        LByte(b) => "VByte(" + byte_lit(b) + ")"
      }
      "(" + lp + as_marker + n + end_marker + ")"
    }
  }
}

///|
/// Markers around the names bound by a generated pattern: they are turned
/// into bindings, or dropped when unused, by `resolve_bindings`.
let var_marker : String = Int32::unsafe_to_char(1).to_string()

///|
let as_marker : String = Int32::unsafe_to_char(3).to_string()

///|
let end_marker : String = Int32::unsafe_to_char(2).to_string()

///|
fn is_ident(s : String) -> Bool {
  s != "" &&
  s
  .iter()
  .all(c => (c >= 'a' && c <= 'z') || (c >= '0' && c <= '9') || c == '_')
}

///|
fn is_ident_char(c : Char) -> Bool {
  (c >= 'a' && c <= 'z') ||
  (c >= 'A' && c <= 'Z') ||
  (c >= '0' && c <= '9') ||
  c == '_'
}

///|
/// Does `name` occur in `code` as a whole identifier?
fn uses(code : String, name : String) -> Bool {
  let cs : Array[Char] = code.iter().collect()
  let ns : Array[Char] = name.iter().collect()
  let n = ns.length()
  for i = 0; i + n <= cs.length(); i = i + 1 {
    let mut same = true
    for k = 0; k < n; k = k + 1 {
      if cs[i + k] != ns[k] {
        same = false
        break
      }
    }
    if same &&
      (i == 0 || !is_ident_char(cs[i - 1])) &&
      (i + n == cs.length() || !is_ident_char(cs[i + n])) {
      return true
    }
  }
  false
}

///|
/// Turn the binding markers of a pattern into bindings, dropping the unused
/// ones (an unused variable becomes `_`).
fn resolve_bindings(pat : String, body : String) -> String {
  let out = StringBuilder()
  let cs : Array[Char] = pat.iter().collect()
  let v = var_marker.get_char(0).unwrap()
  let a = as_marker.get_char(0).unwrap()
  let e = end_marker.get_char(0).unwrap()
  let mut i = 0
  while i < cs.length() {
    let c = cs[i]
    if c == v || c == a {
      let mut j = i + 1
      let name = StringBuilder()
      while cs[j] != e {
        name.write_char(cs[j])
        j = j + 1
      }
      let n = name.to_string()
      if uses(body, n) {
        out.write_string(if c == v { n } else { " as " + n })
      } else if c == v {
        out.write_char('_')
      }
      i = j + 1
    } else {
      out.write_char(c)
      i = i + 1
    }
  }
  out.to_string()
}

///|
/// Clauses as an `if` chain over the runtime matcher (used for patterns
/// MoonBit cannot express, like Double literals).
fn Gen::clauses_dynamic(
  self : Gen,
  env : Array[Local],
  scruts : String,
  cls : Array[@tt.Clause],
  fallback : String,
) -> String {
  let out = self.name("o")
  let buf = StringBuilder()
  buf.write_string("{\nlet " + out + " : Array[Value] = []\n")
  for cl in cls {
    let mut env2 = env
    let binds = StringBuilder()
    for k = 0; k < @tt.pats_slots(cl.pats); k = k + 1 {
      let x = self.name("v")
      binds.write_string("let " + x + " = " + out + "[" + k.to_string() + "]\n")
      env2 = push_local(env2, LVar(x))
    }
    // a guard is tested with the slots bound in its own block
    let when = match cl.cond {
      Some(g) =>
        " && truthy({\n" + binds.to_string() + self.tm(env2, g) + "\n})"
      None => ""
    }
    buf.write_string(
      "if match_pats([" +
      cl.pats.map(p => self.pat_code(p)).join(", ") +
      "], " +
      scruts +
      ", " +
      out +
      ")" +
      when +
      " {\n",
    )
    buf.write_string(binds.to_string())
    buf.write_string("(" + self.tm(env2, cl.body) + ")")
    buf.write_string("\n} else ")
  }
  buf.write_string("{\n" + fallback + "\n}\n}")
  buf.to_string()
}

///|
/// Is `t` a proof (an erased local, or a use of a lemma or of a constructor
/// of a proposition)? It is not computed.
fn Gen::is_erased_tm(self : Gen, env : Array[Local], t : @tt.Tm) -> Bool {
  match t {
    Var(ix) => env[env.length() - 1 - ix] is LErased
    _ => {
      let (h, _) = flatten_app(t)
      h is Global(n) && @tt.is_proof_global(n)
    }
  }
}

///|
/// A match on already evaluated scrutinees (given as MoonBit expressions).
fn Gen::match_code(
  self : Gen,
  env : Array[Local],
  scruts : Array[String],
  cls : Array[@tt.Clause],
  fallback : String,
  proofs? : Array[Bool],
) -> String {
  // the columns of proofs: proofs are erased, and a match on a proof does
  // not choose (a proposition is matched into a proposition, or is a
  // subsingleton), so its patterns match anything and bind erased slots
  let proofs = proofs.unwrap_or(scruts.map(_ => false))
  if proofs.iter().any(p => p) {
    if proofs.iter().all(p => p) {
      // the clauses up to the first one without a guard, as an `if` chain
      let buf = StringBuilder()
      for cl in cls {
        let mut env2 = env
        for _ in 0..<@tt.pats_slots(cl.pats) {
          env2 = push_local(env2, LErased)
        }
        match cl.cond {
          Some(g) =>
            buf.write_string(
              "if truthy(" +
              self.tm(env2, g) +
              ") {\n" +
              self.tm(env2, cl.body) +
              "\n} else ",
            )
          None => {
            let body = self.tm(env2, cl.body)
            // (a lone `{ x }` would be a record)
            if buf.is_empty() {
              return body
            }
            buf.write_string("{\n" + body + "\n}")
            return buf.to_string()
          }
        }
      }
      if cls.length() == 0 {
        return "abort(\"unreachable: a proof of an empty proposition\")"
      }
      buf.write_string("{\n" + fallback + "\n}")
      return buf.to_string()
    }
    if cls.iter().any(cl => cl.pats.iter().any(has_double_pat)) {
      return "abort(\"unsupported: a match on a proof and a Double literal\")"
    }
  }
  if cls.iter().any(cl => cl.pats.iter().any(has_double_pat)) {
    return self.clauses_dynamic(
      env,
      "[" + scruts.join(", ") + "]",
      cls,
      fallback,
    )
  }
  let subject = if scruts.length() == 1 {
    scruts[0]
  } else {
    "(" + scruts.join(", ") + ")"
  }
  let buf = StringBuilder()
  buf.write_string("match " + subject + " {\n")
  for cl in cls {
    let names : Array[Local] = []
    let conds : Array[String] = []
    let ps = cl.pats.mapi((k, p) => {
      if proofs[k] {
        for _ in 0..<@tt.pats_slots([p]) {
          names.push(LErased)
        }
        "_"
      } else {
        self.native_pat(p, names, conds)
      }
    })
    let mut env2 = env
    for n in names {
      env2 = push_local(env2, n)
    }
    let lhs = if ps.length() == 1 { ps[0] } else { "(" + ps.join(", ") + ")" }
    let body = self.tm(env2, cl.body)
    match cl.cond {
      Some(g) => conds.push("truthy(" + self.tm(env2, g) + ")")
      None => ()
    }
    let when = if conds.is_empty() { "" } else { " if " + conds.join(" && ") }
    buf.write_string(
      resolve_bindings(lhs, body + when) + when + " => (" + body + ")\n",
    )
  }
  buf.write_string("_ => " + fallback + "\n}")
  buf.to_string()
}

///|
/// Primitive operations that are inlined (`$0`, `$1` are the arguments).
let inline_prims : Map[String, String] = {
  "%int_add": "VInt(as_int($0) + as_int($1))",
  "%int_sub": "VInt(as_int($0) - as_int($1))",
  "%int_mul": "VInt(as_int($0) * as_int($1))",
  "%int_neg": "VInt(-as_int($0))",
  "%int_land": "VInt(as_int($0) & as_int($1))",
  "%int_lor": "VInt(as_int($0) | as_int($1))",
  "%int_lxor": "VInt(as_int($0) ^ as_int($1))",
  "%int_shl": "VInt(as_int($0) << as_int($1))",
  "%int_shr": "VInt(as_int($0) >> as_int($1))",
  "%int_eq": "VBool(as_int($0) == as_int($1))",
  "%int_lt": "VBool(as_int($0) < as_int($1))",
  "%int_le": "VBool(as_int($0) <= as_int($1))",
  "%int_gt": "VBool(as_int($0) > as_int($1))",
  "%int_ge": "VBool(as_int($0) >= as_int($1))",
  "%int_compare": "VInt(as_int($0).compare(as_int($1)))",
  "%int_to_string": "VStr(as_int($0).to_string())",
  "%int_to_double": "VDouble(as_int($0).to_double())",
  "%double_add": "VDouble(as_double($0) + as_double($1))",
  "%double_sub": "VDouble(as_double($0) - as_double($1))",
  "%double_mul": "VDouble(as_double($0) * as_double($1))",
  "%double_div": "VDouble(as_double($0) / as_double($1))",
  "%double_neg": "VDouble(-as_double($0))",
  "%double_lt": "VBool(as_double($0) < as_double($1))",
  "%double_le": "VBool(as_double($0) <= as_double($1))",
  "%double_gt": "VBool(as_double($0) > as_double($1))",
  "%double_ge": "VBool(as_double($0) >= as_double($1))",
  "%double_eq": "VBool(as_double($0) == as_double($1))",
  "%double_to_string": "VStr(as_double($0).to_string())",
  "%str_add": "VStr(as_str($0) + as_str($1))",
  "%str_eq": "VBool(as_str($0) == as_str($1))",
  "%str_length": "VInt(as_str($0).length())",
  "%bool_eq": "VBool(as_bool($0) == as_bool($1))",
  "%bool_not": "VBool(!as_bool($0))",
  "%bool_to_string": "VStr(as_bool($0).to_string())",
  "%char_eq": "VBool(as_char($0) == as_char($1))",
  "%char_to_string": "VStr(as_char($0).to_string())",
  "%array_length": "VInt(as_arr($0).length())",
  "%array_push": "{ as_arr($0).push($1); VUnit }",
  "%print": "{ rt_write(as_str($0)); VUnit }",
  "%nat_succ": "VNat(as_nat($0) + 1N)",
  "%axiom": "VType",
  // code is its body, waiting to be run on the code of its splices
  // (tt/staging.mbt)
  "%quote": "make_code($0, $1)",
  "%splice": "apply($0, VUnit)",
  "%run": "apply($0, VUnit)",
  "%physical_equal": "VBool(physical_equal($0, $1))",
  "%nat_of_int": "VNat(nat_of_int(as_int($0)))",
  "%nat_to_int": "VInt(as_nat($0).to_int())",
  "%nat_add": "VNat(as_nat($0) + as_nat($1))",
  "%nat_mul": "VNat(as_nat($0) * as_nat($1))",
  "%nat_eq": "VBool(as_nat($0) == as_nat($1))",
  "%nat_compare": "VInt(as_nat($0).compare(as_nat($1)))",
  "%nat_to_string": "VStr(as_nat($0).to_string())",
}

///|
fn subst_args(template : String, args : Array[String]) -> String {
  let mut s = template
  for k = args.length() - 1; k >= 0; k = k - 1 {
    // `2.to_byte()` would be a Double: `(2).to_byte()`
    let a = args[k]
    let a = if a.length() > 0 && a[0] >= '0' && a[0] <= '9' {
      "(" + a + ")"
    } else {
      a
    }
    s = s.replace_all(old="$" + k.to_string(), new=a)
  }
  s
}

///|
fn Gen::prim_call(self : Gen, p : String, args : Array[String]) -> String {
  if args.iter().any(a => a.contains("$")) {
    return "prim(" + p.escape() + ", [" + args.join(", ") + "])"
  }
  if p == "%nat_deq" {
    return "if as_nat(\{args[0]}) == as_nat(\{args[1]}) { " +
      self.con_code("Dec::Yes", []) +
      " } else { " +
      self.con_code("Dec::No", []) +
      " }"
  }
  match (inline_prims.get(p), native_prims.get(p)) {
    (Some(tpl), _) => subst_args(tpl, args)
    // the native template, between conversions
    (None, Some((tpl, tys, res))) if args.length() == tys.length() =>
      self.to_value(
        res,
        subst_args(tpl, args.mapi((i, a) => self.of_value(tys[i], a, None))),
        None,
      )
    _ => "prim(" + p.escape() + ", [" + args.join(", ") + "])"
  }
}

///|
fn flatten_app(t : @tt.Tm) -> (@tt.Tm, Array[@tt.Tm]) {
  let args : Array[@tt.Tm] = []
  let mut h = t
  while h is App(f, a, _) {
    args.push(a)
    h = f
  }
  args.rev_in_place()
  (h, args)
}

///|
fn apply_rest(code : String, rest : Array[String]) -> String {
  let mut c = code
  for a in rest {
    c = "apply(" + c + ", " + a + ")"
  }
  c
}

///|
/// An application, calling known globals directly when it is saturated.
fn Gen::app(self : Gen, env : Array[Local], t : @tt.Tm) -> String {
  let (h, args) = flatten_app(t)
  if h is Global(n) && @tt.is_async_global(n) {
    return self.async_use(n)
  }
  // Nat-like data are `BigInt`s (see natlike.mbt), and the prelude
  // functions on `Nat` (`@tt.nat_natives`) are native
  if self.nat_numeral(t) is Some((k, _)) {
    return "VNat(\{k}N)"
  }
  match nat_prim(h) {
    Some((p, k)) if args.length() >= k => {
      let cs = args.map(a => self.tm(env, a))
      return apply_rest(self.prim_call(p, cs[:k].to_array()), cs[k:].to_array())
    }
    _ => ()
  }
  match h {
    Global(n) =>
      match @tt.globals.get(n) {
        Some(g) =>
          match g.kind {
            GFunc(_, _, _) if func_arity(n) is Some(k) && args.length() >= k => {
              let direct : Array[String] = []
              for i = 0; i < k; i = i + 1 {
                if !self.er.fun_erased(n, i) {
                  direct.push(self.tm(env, args[i]))
                }
              }
              let rest = args[k:].to_array().map(a => self.tm(env, a))
              return apply_rest(
                self.gid(n) + "(" + direct.join(", ") + ")",
                rest,
              )
            }
            GCon(ci) if args.length() >= ci.nparams + ci.nargs &&
              self.nat_con(n) is Some((nl, true)) => {
              let total = ci.nparams + ci.nargs
              let rest = args[total:].to_array().map(a => self.tm(env, a))
              let x = self.tm(env, args[ci.nparams + nl.field])
              return apply_rest(self.prim_call("%nat_succ", [x]), rest)
            }
            GCon(ci) if args.length() >= ci.nparams + ci.nargs => {
              let total = ci.nparams + ci.nargs
              let own : Array[String] = []
              for j = 0; j < ci.nargs; j = j + 1 {
                if !self.er.con_erased(n, j) {
                  own.push(self.tm(env, args[ci.nparams + j]))
                }
              }
              let rest = args[total:].to_array().map(a => self.tm(env, a))
              return apply_rest(self.con_code(n, own), rest)
            }
            GPrim(p, k) if args.length() >= k && !p.has_prefix("@mbt:") => {
              let icits = binder_icits(g.ty, k)
              let expl : Array[String] = []
              for i = 0; i < k; i = i + 1 {
                if icits[i] == Expl {
                  expl.push(self.tm(env, args[i]))
                }
              }
              let rest = args[k:].to_array().map(a => self.tm(env, a))
              return apply_rest(self.prim_call(p, expl), rest)
            }
            _ => ()
          }
        None => ()
      }
    _ => ()
  }
  apply_rest(self.tm(env, h), args.map(a => self.tm(env, a)))
}

///|
/// The native operation of a prelude function on `Nat`, and its arity (see
/// `Gen::app`).
fn nat_prim(h : @tt.Tm) -> (String, Int32)? {
  match h {
    Global(n) if @tt.prelude_nat.val => @tt.nat_natives.get(n)
    _ => None
  }
}

///|
/// `if c { a } else { b }` as elaborated by the checker.
fn if_parts(
  ss : Array[@tt.Tm],
  cls : Array[@tt.Clause],
) -> (@tt.Tm, @tt.Tm, @tt.Tm)? {
  match (ss, cls) {
    (
      [c],
      [
        { pats: [CPLit(LBool(true))], cond: None, body: a, },
        { pats: [CPWild | CPLit(LBool(false))], cond: None, body: b, },
      ],
    ) => Some((c, a, b))
    _ => None
  }
}

///|
fn Gen::tm(self : Gen, env : Array[Local], t : @tt.Tm) -> String {
  match t {
    Var(ix) => local_code(env[env.length() - 1 - ix])
    Global(n) => self.global_value(n)
    Lam(x, _, _, b) => {
      let v = self.name(x)
      let body = self.tm(push_local(env, LVar(v)), b)
      let body = catch_return(has_return(b), body)
      // `moon fmt` may turn a long `x => y` into `x => { y }`, which is a
      // record: a variable alone is `value_id(y)`
      let body = if is_ident(body) { "value_id(" + body + ")" } else { body }
      "VFun(" + v + " => " + body + ")"
    }
    App(_, _, _) => self.app(env, t)
    // a proof is not computed
    Let(_, ty, v, b) if @tt.is_prop_head(ty) || self.is_erased_tm(env, v) =>
      self.tm(push_local(env, LErased), b)
    Let(x, _, v, b) => {
      let n = self.name(x)
      "{\nlet " +
      n +
      " = " +
      self.tm(env, v) +
      "\n" +
      self.tm(push_local(env, LVar(n)), b) +
      "\n}"
    }
    LetMut(x, _, v, b) => {
      let n = self.name(x)
      "{\nlet " +
      n +
      " = Ref::new(" +
      self.tm(env, v) +
      ")\n" +
      self.tm(push_local(env, LMut(n)), b) +
      "\n}"
    }
    U
    | PropU
    | Pi(_, _, _, _, _)
    | Raises(_, _)
    | Meta(_)
    | InsertedMeta(_, _) => "VType"
    Lit(l) => lit_code(l)
    Match(ss, cls) =>
      match if_parts(ss, cls) {
        Some((c, a, b)) => {
          // the branches are under one (unused) slot: the condition
          let n = self.name("cond")
          let env2 = push_local(env, LVar(n))
          "{\nlet " +
          n +
          " = " +
          self.tm(env, c) +
          "\nif truthy(" +
          n +
          ") {\n" +
          self.tm(env2, a) +
          "\n} else {\n" +
          self.tm(env2, b) +
          "\n}\n}"
        }
        None => {
          let lets = StringBuilder()
          // a column matching a proof matches anything (see match_code)
          let proofs = ss.map(s => self.is_erased_tm(env, s))
          let names = ss.mapi((k, s) => {
            if proofs[k] {
              return "VType"
            }
            let code = self.tm(env, s)
            if is_ident(code) {
              code
            } else {
              let n = self.name("s")
              lets.write_string("let " + n + " = " + code + "\n")
              n
            }
          })
          let m = self.match_code(
            env,
            names,
            cls,
            "rt_fail(\"no match\")",
            proofs~,
          )
          if lets.is_empty() {
            m
          } else {
            "{\n" + lets.to_string() + m + "\n}"
          }
        }
      }
    Assign(ix, v) =>
      match env[env.length() - 1 - ix] {
        LMut(n) => "{\n" + n + ".val = " + self.tm(env, v) + "\nVUnit\n}"
        _ => "rt_fail(\"assignment to an immutable variable\")"
      }
    While(c, b, step) =>
      "{\nwhile truthy(" +
      self.tm(env, c) +
      ") {\n" +
      "let brk = try {\nignore(" +
      self.tm(env, b) +
      ")\nfalse\n} catch {\nCBreak => true\nCContinue => false\ne => raise e\n}\n" +
      "if brk {\nbreak\n}\nignore(" +
      self.tm(env, step) +
      ")\n}\nVUnit\n}"
    Break => "rt_break()"
    Continue => "rt_continue()"
    Return(v) => "rt_return(" + self.tm(env, v) + ")"
    Raise(v) => "rt_raise(" + self.tm(env, v) + ")"
    Try(b, cls) => {
      let err = self.name("err")
      "(try {\n(" +
      self.tm(env, b) +
      ")\n} catch {\nCRaise(" +
      err +
      ") => " +
      self.match_code(env, [err], cls, "rt_raise(" + err + ")") +
      "\ne => raise e\n})"
    }
    ArrayLit(es) => "VArr([" + es.map(x => self.tm(env, x)).join(", ") + "])"
    Seq(a, b) =>
      "{\nignore(" + self.tm(env, a) + ")\n" + self.tm(env, b) + "\n}"
    // MoonBit's `defer` (it may not raise: errors of `a` are dropped)
    Defer(a, b) =>
      "{\ndefer (try { ignore(" +
      self.tm(env, a) +
      ") } catch { _ => () })\n" +
      self.tm(env, b) +
      "\n}"
  }
}

///|
/// A global used as a value.
fn Gen::global_value(self : Gen, n : String) -> String {
  if @tt.is_async_global(n) {
    return self.async_use(n)
  }
  match @tt.globals.get(n) {
    Some({ kind: GCon(ci), .. }) if ci.nparams + ci.nargs == 0 &&
      self.nat_con(n) is Some(_) => "VNat(0N)"
    Some({ kind: GCon(ci), .. }) if ci.nparams + ci.nargs == 0 =>
      self.con_code(n, [])
    Some({ kind: GData(_), .. }) => "VType"
    _ => self.gid(n) + "_v()"
  }
}

///|
/// The native function computing the global value `name`.
fn Gen::native_init(
  self : Gen,
  id : String,
  name : String,
  code : String,
  nt : NTy,
  raise_ : String,
) -> Unit {
  self.write(
    "\n/// " +
    name +
    "\nfn " +
    id +
    "_init() -> " +
    self.mbt_result(nt) +
    raise_ +
    " {\n" +
    code +
    "\n}\n",
  )
}

///|
/// Nested functions collecting `n` arguments `a0 .. a(n-1)`, then `final`.
fn curried(n : Int32, final_ : String) -> String {
  let mut code = final_
  for k = n - 1; k >= 0; k = k - 1 {
    code = "VFun(a" + k.to_string() + " => " + code + ")"
  }
  code
}

///|
/// The icitness of the binders of a (closed) Pi type.
fn binder_icits(ty : @tt.Tm, n : Int32) -> Array[@tt.Icit] {
  let out : Array[@tt.Icit] = []
  let mut t = ty
  for _ in 0..<n {
    match t {
      Pi(_, i, _, _, b) => {
        out.push(i)
        t = b
      }
      _ => out.push(Expl)
    }
  }
  out
}

///|
fn Gen::cached(self : Gen, id : String, code : String) -> Unit {
  self.write(
    (
      $|
      $|let \{id}_cache : Ref[Value?] = Ref::new(None)
      $|
      $|fn \{id}_v() -> Value raise {
      $|  match \{id}_cache.val {
      $|    Some(v) => v
      $|    None => {
      $|      let v = \{code}
      $|      \{id}_cache.val = Some(v)
      $|      v
      $|    }
      $|  }
      $|}
      $|
    ),
  )
}

///|
fn Gen::global(self : Gen, name : String) -> Unit raise CodegenError {
  // the definition goes to the file of its source
  let saved = self.cur_file
  self.cur_file = self.file_of(name)
  self.cur_global = name
  self.global_def(name) catch {
    e => {
      self.cur_file = saved
      raise e
    }
  }
  self.cur_file = saved
}

///|
fn Gen::global_def(self : Gen, name : String) -> Unit raise CodegenError {
  let g = match @tt.globals.get(name) {
    Some(g) => g
    None => raise CodegenError("unknown global " + name)
  }
  let id = self.gid(name)
  // the prelude functions on `Nat` are native (see `app`)
  match nat_prim(Global(name)) {
    Some((p, k)) => {
      let xs = Array::makei(k, j => "a" + j.to_string())
      self.cached(id, curried(k, self.prim_call(p, xs)))
      return
    }
    None => ()
  }
  // an async function only has its native version (see `check_async_fns`;
  // uses in uniform code are errors, see `async_use`)
  if @tt.is_async_global(name) {
    if g.kind is GFunc(Some(_), _, _) && self.typed_set.contains(name) {
      self.write("\n/// " + name + "\n" + self.typed_fn(name).unwrap())
      self.export_fn(name, self.native_sig(name).unwrap())
    }
    return
  }
  match g.kind {
    GFunc(Some(body), _, _) if self.typed_set.contains(name) =>
      match self.native_sig(name) {
        Some(sig) if self.wrappable(sig) => {
          self.write(self.typed_def(name))
          self.export_fn(name, sig)
        }
        _ => {
          // with trait bounds (or read-only types): the native version, and
          // the uniform one (which gets the instances as values)
          self.write("\n/// " + name + "\n" + self.typed_fn(name).unwrap())
          self.export_fn(name, self.native_sig(name).unwrap())
          self.uniform_fn(name, id, body, func_arity(name).unwrap())
        }
      }
    GFunc(Some(body), _, _) if func_arity(name) is Some(n) =>
      self.uniform_fn(name, id, body, n)
    GFunc(Some(_), _, _) if self.native_consts.contains(name) => {
      // a native constant: computed once, natively; the uniform code sees
      // it converted (only when it can be: otherwise no uniform code uses
      // it, see `compute_typed`)
      let (code, nt) = self.typed_const(name).unwrap()
      let r = if self.fn_raises(name) { " raise" } else { "" }
      let ty = self.mbt_ty(nt)
      // `((A) -> B raise)?`
      let ty = if nt is (NFun(_, _) | NAsyncFun(_, _)) {
        "(" + ty + ")"
      } else {
        ty
      }
      self.native_init(id, name, code, nt, r)
      self.write(
        (
          $|
          $|let \{id}_cell : Ref[\{ty}?] = Ref::new(None)
          $|
          $|fn \{id}_n() -> \{ty}\{r} {
          $|  match \{id}_cell.val {
          $|    Some(v) => v
          $|    None => {
          $|      let v : \{ty} = \{id}_init()
          $|      \{id}_cell.val = Some(v)
          $|      v
          $|    }
          $|  }
          $|}
          $|
        ),
      )
      self.cached(
        id,
        if self.convertible(nt, false) {
          self.to_value(nt, id + "_n()", None)
        } else {
          "rt_fail(\"\{name} has no uniform representation\")"
        },
      )
    }
    GFunc(Some(body), _, _) =>
      // a value (or `main`) whose definition is in the native fragment: its
      // native code, in a function (for `return`)
      match self.typed_const(name) {
        Some((code, nt)) if !self.dry && self.convertible(nt, false) => {
          self.native_init(id, name, code, nt, " raise")
          self.cached(id, self.to_value(nt, id + "_init()", None))
        }
        _ => {
          self.write("\n/// " + name)
          self.cached(id, catch_return(has_return(body), self.tm([], body)))
        }
      }
    GFunc(None, _, _) =>
      self.cached(id, "rt_fail(\"" + name + " has no definition\")")
    GData(_) => self.cached(id, "VType")
    GCon(ci) if self.nat_con(name) is Some((nl, is_succ)) => {
      let total = ci.nparams + ci.nargs
      let code = if is_succ {
        "VNat(as_nat(a\{ci.nparams + nl.field}) + 1N)"
      } else {
        "VNat(0N)"
      }
      self.cached(id, curried(total, code))
    }
    GCon(ci) => {
      let args : Array[String] = []
      for j = 0; j < ci.nargs; j = j + 1 {
        if !self.er.con_erased(name, j) {
          args.push("a" + (ci.nparams + j).to_string())
        }
      }
      self.cached(id, curried(ci.nparams + ci.nargs, self.con_code(name, args)))
    }
    GPrim(p, arity) => {
      let all : Array[String] = []
      for k = 0; k < arity; k = k + 1 {
        all.push("a" + k.to_string())
      }
      let call = if p.has_prefix("@mbt:") {
        self.ffi_fn(name, p, g.ty, arity) + "([" + all.join(", ") + "])"
      } else {
        let icits = binder_icits(g.ty, arity)
        let expl : Array[String] = []
        for k = 0; k < arity; k = k + 1 {
          if icits[k] == Expl {
            expl.push("a" + k.to_string())
          }
        }
        self.prim_call(p, expl)
      }
      self.cached(id, curried(arity, call))
    }
  }
}

///|
/// Emit a function of `n` parameters in the uniform representation.
fn Gen::uniform_fn(
  self : Gen,
  name : String,
  id : String,
  body : @tt.Tm,
  n : Int32,
) -> Unit {
  // a function: strip its n lambdas
  let erased : Array[Bool] = []
  for i = 0; i < n; i = i + 1 {
    erased.push(self.er.fun_erased(name, i))
  }
  let params : Array[String] = []
  let mut env : Array[Local] = []
  let mut b = body
  for i = 0; i < n; i = i + 1 {
    match b {
      Lam(x, _, _, rest) => {
        if erased[i] {
          env = push_local(env, LErased)
        } else {
          let p = self.name(x)
          params.push(p)
          env = push_local(env, LVar(p))
        }
        b = rest
      }
      _ => ()
    }
  }
  let code = catch_return(has_return(b), self.tm(env, b))
  let sig = params.map(p => p + " : Value").join(", ")
  // as a value: a curried closure over all n parameters
  let pass : Array[String] = []
  for i = 0; i < n; i = i + 1 {
    if !erased[i] {
      pass.push("a" + i.to_string())
    }
  }
  self.write(
    (
      $|
      $|/// \{name}
      $|fn \{id}(\{sig}) -> Value raise {
      $|\{code}
      $|}
      $|
      $|fn \{id}_v() -> Value {
      $|  \{curried(n, id + "(" + pass.join(", ") + ")")}
      $|}
      $|
    ),
  )
}

///|
fn Gen::new(imports : Array[(String, String)]) -> Gen {
  let g : Gen = {
    ids: {},
    todo: [],
    files: {},
    cur_file: imports_file,
    foreign: {},
    foreign_order: [],
    dyn_wrappers: {},
    aliases: {},
    er: compute_erasure(),
    fresh: 0,
    enums_ok: {},
    enums_done: [],
    typed_set: [],
    async_vars: false,
    async_fns: {},
    async_busy: [],
    cur_result: None,
    cur_step: None,
    dry: false,
    scheduled: {},
    cur_bounds: [],
    mbt_impls: [],
    impls_done: [],
    traits_done: [],
    diagnose: false,
    culprit: None,
    ctors: {},
    ctor_order: [],
    nat_likes: {},
    native_consts: [],
    raising: {},
    may_raise: false,
    cur_global: "",
    async_misuse: [],
  }
  for im in imports {
    g.aliases.set(im.0, im.1)
  }
  g
}

///|
/// Which of the functions `names` have a native translation, so that they
/// could be `#mbt` (see `@tt.mbt_hints`).
pub fn native_fns(
  imports : Array[(String, String)],
  names : Array[String],
) -> Array[String] {
  let g = Gen::new(imports)
  g.dry = true
  g.compute_typed()
  let reserved = [..runtime_fns(), "con_name", "con_fields", "main"]
  names.filter(n => g.typed_set.contains(n) && !reserved.contains(n))
}

///|
/// The generated program (all files but the runtime) as one text, each file
/// introduced by a `// ==== name ====` line.
pub fn generate(imports : Array[(String, String)]) -> String raise CodegenError {
  generate_files(imports)
  .map(f => "// ==== " + f.0 + " ====\n" + f.1)
  .join("\n")
}

///|
/// The output file name of the runtime.
pub fn runtime_file_name() -> String {
  runtime_file
}

///|
/// The runtime support file of generated programs (`mbtpp_runtime.mbt`).
pub fn runtime_code() -> String {
  "// Generated by moonpp: the runtime support of compiled MoonBit++.\n\n" +
  runtime_src
}

///|
/// Generate the MoonBit program for the last type checked MoonBit++
/// program. `imports` are the imported packages (path, alias).
pub fn generate_files(
  imports : Array[(String, String)],
) -> Array[(String, String)] raise CodegenError {
  if !@tt.globals.contains("main") {
    raise CodegenError("no main function")
  }
  warnings.clear()
  let g = Gen::new(imports)
  g.dry = true
  g.compute_typed()
  g.check_mbt_fns()
  g.check_async_fns()
  g.dry = false
  let main_async = @tt.is_async_global("main")
  let main_code = if main_async {
    g.async_main()
  } else {
    "\n///|\nfn main {\n  run_main(() => " + g.global_value("main") + ")\n}\n"
  }
  // `#mbt` functions are exported whether `main` uses them or not
  for f, _ in @tt.mbt_fns {
    ignore(g.gid(f))
  }
  // and so are the impls of `#mbt` traits, like the types
  for i in g.mbt_impls.copy() {
    // impls for the native enums of MoonBit++ datatypes are made when used
    match g.impl_info(i) {
      Some((_, _, NEnum(d, _), tr)) if @tt.mbt_info(d) is None &&
        !(@tt.mbt_info(tr) is Some({ defined: true, .. })) => continue
      _ => ()
    }
    g.need_impl(i)
  }
  while g.todo.length() > 0 {
    let n = g.todo.pop().unwrap()
    g.global(n)
  }
  // the async versions of effect polymorphic functions (typed.mbt)
  for n, code in g.async_fns {
    g.write_to(g.file_of(n), "\n/// " + n + " (async)\n" + code)
  }
  g.write_to(g.file_of("main"), main_code)
  match g.async_misuse {
    [] => ()
    [(f, user), ..] =>
      raise CodegenError(
        "async fn " +
        f +
        " is used by " +
        user +
        ", which is not compiled to native MoonBit code (async functions can only be used from native code)",
      )
  }
  g.output_files()
}
