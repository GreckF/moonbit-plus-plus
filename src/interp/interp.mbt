///|
/// A tree-walking interpreter for elaborated core terms.
pub(all) enum RVal {
  RLit(@tt.Lit)
  /// Constructor with its own arguments (datatype parameters dropped).
  RCon(String, Array[RVal])
  /// A constructor or primitive waiting for more arguments.
  RPartial(Partial, Array[(RVal, @tt.Icit)])
  RClo(REnv, @tt.Tm)
  RArr(Array[RVal])
  /// A `Nat` (`Z` is 0, `S(n)` is n + 1).
  RNat(BigInt)
  /// Types and other erased values.
  RType
}

///|
pub(all) enum Partial {
  PCon(String, Int32, Int32)
  PPrim(String, Int32)
}

///|
pub(all) enum REnv {
  ENil
  ECons(Ref[RVal], REnv)
}

///|
priv suberror Ctl {
  CBreak
  CContinue
  CReturn(RVal)
  CRaise(RVal)
  CAbort(String)
}

///|
pub suberror RunError {
  RunError(String)
}

///|
priv struct Machine {
  cache : Map[String, RVal]
  write : (String) -> Unit
}

///|
fn lookup(env : REnv, ix : Int32) -> Ref[RVal] raise Ctl {
  let mut e = env
  let mut k = ix
  while true {
    match e {
      ECons(r, rest) => {
        if k == 0 {
          return r
        }
        k = k - 1
        e = rest
      }
      ENil => raise CAbort("unbound variable")
    }
  }
  raise CAbort("unbound variable")
}

///|
pub fn show_rval(v : RVal) -> String {
  match v {
    RLit(LStr(s)) => s.escape()
    RLit(LChar(c)) => c.to_string().escape()
    RLit(LInt(n)) => n.to_string()
    RLit(LBool(b)) => b.to_string()
    RLit(LUnit) => "()"
    RLit(LDouble(d)) => d.to_string()
    RLit(LInt64(n)) => n.to_string()
    RLit(LUInt(n)) => n.to_string()
    RLit(LUInt64(n)) => n.to_string()
    RLit(LByte(b)) => b.to_string()
    RLit(LFloat(f)) => f.to_string()
    RCon(c, args) => {
      let short = match c.rev_find("::") {
        Some(i) => c.unsafe_substring(start=i + 2, end=c.length())
        None => c
      }
      if args.length() == 0 {
        short
      } else {
        short + "(" + args.map(show_rval).join(", ") + ")"
      }
    }
    RArr(xs) => "[" + xs.map(show_rval).join(", ") + "]"
    RNat(n) => n.to_string()
    RClo(_, _) | RPartial(_, _) => "<function>"
    RType => "<type>"
  }
}

///|
fn Machine::global(self : Machine, n : String) -> RVal raise Ctl {
  match self.cache.get(n) {
    Some(v) => return v
    None => ()
  }
  let v = match @tt.globals.get(n) {
    // `Nat` is native: its constructors and the prelude functions on it
    _ if n == "Nat::Z" && @tt.prelude_nat.val => RNat(0N)
    _ if n == "Nat::S" && @tt.prelude_nat.val =>
      RPartial(PPrim("%nat_succ", 1), [])
    _ if @tt.prelude_nat.val && @tt.nat_natives.get(n) is Some((p, arity)) =>
      RPartial(PPrim(p, arity), [])
    Some(g) =>
      match g.kind {
        GFunc(Some(body), _, _) => self.eval(ENil, body)
        GFunc(None, _, _) => raise CAbort("function " + n + " has no body")
        GData(_) => RType
        GCon(ci) =>
          if ci.nparams + ci.nargs == 0 {
            RCon(n, [])
          } else {
            RPartial(PCon(n, ci.nparams, ci.nparams + ci.nargs), [])
          }
        GPrim(p, 0) => self.prim(p, [])
        GPrim(p, arity) => RPartial(PPrim(p, arity), [])
      }
    None => raise CAbort("unknown global " + n)
  }
  self.cache.set(n, v)
  v
}

///|
fn truthy(v : RVal) -> Bool raise Ctl {
  match v {
    RLit(LBool(b)) => b
    _ => raise CAbort("expected a boolean")
  }
}

///|
fn rmatch(p : @tt.CPat, v : RVal, out : Array[RVal]) -> Bool {
  out.push(v)
  match p {
    CPVar(_) | CPWild => true
    CPCon("Nat::Z", []) if @tt.prelude_nat.val => v is RNat(n) && n == 0N
    CPCon("Nat::S", [q]) if @tt.prelude_nat.val =>
      match v {
        RNat(n) if n > 0N => rmatch(q, RNat(n - 1N), out)
        _ => false
      }
    // a proof that is not computed (an axiom): proofs are irrelevant, and
    // only matched where the result is a proof or the proposition is a
    // subsingleton
    CPCon(_, ps) if v is RType => {
      for q in ps {
        ignore(rmatch(q, RType, out))
      }
      true
    }
    CPCon(c, ps) =>
      match v {
        RCon(c2, args) if c2 == c && args.length() == ps.length() => {
          for k = 0; k < ps.length(); k = k + 1 {
            if !rmatch(ps[k], args[k], out) {
              return false
            }
          }
          true
        }
        _ => false
      }
    CPLit(l) =>
      match v {
        RLit(l2) => l == l2
        _ => false
      }
  }
}

///|
fn push_env(env : REnv, vs : Array[RVal]) -> REnv {
  let mut e = env
  for v in vs {
    e = ECons(Ref(v), e)
  }
  e
}

///|
fn Machine::run_clauses(
  self : Machine,
  env : REnv,
  vs : Array[RVal],
  cls : Array[@tt.Clause],
) -> RVal? raise Ctl {
  for cl in cls {
    let out : Array[RVal] = []
    let mut ok = true
    for k = 0; k < cl.pats.length(); k = k + 1 {
      if !rmatch(cl.pats[k], vs[k], out) {
        ok = false
        break
      }
    }
    if ok {
      let env2 = push_env(env, out)
      match cl.cond {
        Some(g) => if !(self.eval(env2, g) is RLit(LBool(true))) { continue }
        None => ()
      }
      return Some(self.eval(env2, cl.body))
    }
  }
  None
}

///|
fn Machine::eval(self : Machine, env : REnv, t : @tt.Tm) -> RVal raise Ctl {
  match t {
    Var(ix) => lookup(env, ix).val
    Global(n) => self.global(n)
    Meta(_)
    | InsertedMeta(_, _)
    | Pi(_, _, _, _, _)
    | U
    | PropU
    | Raises(_, _) => RType
    Lam(_, _, _, _) => RClo(env, t)
    App(f, a, i) => {
      let fv = self.eval(env, f)
      let av = self.eval(env, a)
      self.apply(fv, av, i)
    }
    Let(_, _, v, b) | LetMut(_, _, v, b) => {
      let x = self.eval(env, v)
      self.eval(ECons(Ref(x), env), b)
    }
    Lit(l) => RLit(l)
    Match(ss, cls) => {
      let vs = ss.map(s => self.eval(env, s))
      match self.run_clauses(env, vs, cls) {
        Some(v) => v
        None => raise CAbort("no match for " + vs.map(show_rval).join(", "))
      }
    }
    Assign(ix, v) => {
      let x = self.eval(env, v)
      lookup(env, ix).val = x
      RLit(LUnit)
    }
    While(c, b, step) => {
      while truthy(self.eval(env, c)) {
        ignore(self.eval(env, b)) catch {
          CBreak => break
          CContinue => ()
          e => raise e
        }
        ignore(self.eval(env, step))
      }
      RLit(LUnit)
    }
    Break => raise CBreak
    Continue => raise CContinue
    Return(v) => raise CReturn(self.eval(env, v))
    Raise(v) => raise CRaise(self.eval(env, v))
    Try(b, cls) =>
      self.eval(env, b) catch {
        CRaise(err) =>
          match self.run_clauses(env, [err], cls) {
            Some(v) => v
            None => raise CRaise(err)
          }
        e => raise e
      }
    ArrayLit(es) => RArr(es.map(e => self.eval(env, e)))
    Seq(a, b) => {
      ignore(self.eval(env, a))
      self.eval(env, b)
    }
    // the deferred expression runs however the body is left
    Defer(d, b) => {
      let r = self.eval(env, b) catch {
        e => {
          ignore(self.eval(env, d))
          raise e
        }
      }
      ignore(self.eval(env, d))
      r
    }
  }
}

///|
fn Machine::apply(
  self : Machine,
  f : RVal,
  a : RVal,
  i : @tt.Icit,
) -> RVal raise Ctl {
  match f {
    RClo(env, Lam(_, _, _, body)) => {
      let env2 = ECons(Ref(a), env)
      match body {
        Lam(_, _, _, _) => RClo(env2, body)
        _ =>
          self.eval(env2, body) catch {
            CReturn(v) => v
            e => raise e
          }
      }
    }
    RPartial(PCon(n, np, total), args) => {
      let args2 = args.copy()
      args2.push((a, i))
      if args2.length() == total {
        RCon(n, args2[np:].to_owned().map(x => x.0))
      } else {
        RPartial(PCon(n, np, total), args2)
      }
    }
    RPartial(PPrim(p, arity), args) => {
      let args2 = args.copy()
      args2.push((a, i))
      if args2.length() == arity {
        self.prim(p, args2.filter(x => x.1 == Expl).map(x => x.0))
      } else {
        RPartial(PPrim(p, arity), args2)
      }
    }
    RType => RType
    _ => raise CAbort("cannot apply " + show_rval(f))
  }
}

///|
let effect_markers : Ref[Int32] = Ref(0)

///|
fn Machine::prim(
  self : Machine,
  p : String,
  args : Array[RVal],
) -> RVal raise Ctl {
  match (p, args) {
    ("%print", [RLit(LStr(s))]) => {
      (self.write)(s)
      RLit(LUnit)
    }
    ("%error_to_string", [e]) => RLit(LStr(show_rval(e)))
    (p, _) if p.has_prefix("@mbt:") =>
      raise CAbort(
        "cannot run the imported MoonBit function " +
        p.unsafe_substring(start=5, end=p.length()) +
        " in the interpreter (imports are only type checked)",
      )
    // the markers of effect handlers (tt/ctl.mbt)
    ("%effect_marker", _) => {
      effect_markers.val = effect_markers.val + 1
      RLit(LInt(effect_markers.val))
    }
    ("%panic", _) => raise CAbort("panic")
    ("%abort", [RLit(LStr(s))]) => raise CAbort(s)
    ("%array_make", [RLit(LInt(n)), x]) => RArr(Array::make(n, x))
    ("%array_new", _) => RArr([])
    ("%array_length", [RArr(xs)]) => RLit(LInt(xs.length()))
    ("%array_get", [RArr(xs), RLit(LInt(i))]) =>
      if i >= 0 && i < xs.length() {
        xs[i]
      } else {
        raise CAbort("index out of bounds: " + i.to_string())
      }
    ("%array_set", [RArr(xs), RLit(LInt(i)), x]) =>
      if i >= 0 && i < xs.length() {
        xs[i] = x
        RLit(LUnit)
      } else {
        raise CAbort("index out of bounds: " + i.to_string())
      }
    // code is its body, waiting to be run on the code of its splices
    // (tt/staging.mbt): `${ c }` and `c.run()` run it
    ("%quote", [s, f]) =>
      RPartial(PPrim("%run_code", 3), [(s, Expl), (f, Expl)])
    ("%run_code", [s, f, _]) => self.apply(f, s, Expl)
    ("%splice", [c, _, _]) | ("%run", [c]) => self.apply(c, RLit(LUnit), Expl)
    // proofs by axioms are not computed
    ("%axiom", _) => RType
    ("%physical_equal", [a, b]) => RLit(LBool(physical_equal(a, b)))
    ("%nat_deq", [RNat(a), RNat(b)]) =>
      if a == b {
        RCon("Dec::Yes", [RType])
      } else {
        RCon("Dec::No", [RType])
      }
    ("%nat_succ", [RNat(n)]) => RNat(n + 1N)
    ("%nat_of_int", [RLit(LInt(i))]) =>
      RNat(if i <= 0 { 0N } else { BigInt::from_int(i) })
    ("%nat_to_int", [RNat(n)]) => RLit(LInt(n.to_int()))
    ("%nat_add", [RNat(a), RNat(b)]) => RNat(a + b)
    ("%nat_mul", [RNat(a), RNat(b)]) => RNat(a * b)
    ("%nat_eq", [RNat(a), RNat(b)]) => RLit(LBool(a == b))
    ("%nat_compare", [RNat(a), RNat(b)]) => RLit(LInt(a.compare(b)))
    ("%nat_to_string", [RNat(n)]) => RLit(LStr(n.to_string()))
    ("%nat_lt", [RNat(a), RNat(b)]) => RLit(LBool(a < b))
    ("%nat_le", [RNat(a), RNat(b)]) => RLit(LBool(a <= b))
    ("%nat_gt", [RNat(a), RNat(b)]) => RLit(LBool(a > b))
    ("%nat_ge", [RNat(a), RNat(b)]) => RLit(LBool(a >= b))
    ("%nat_sub", [RNat(a), RNat(b)]) => RNat(if a > b { a - b } else { 0N })
    ("%nat_div", [RNat(a), RNat(b)]) => RNat(if b == 0N { 0N } else { a / b })
    ("%nat_mod", [RNat(a), RNat(b)]) => RNat(if b == 0N { a } else { a % b })
    ("%nat_gcd", [RNat(a), RNat(b)]) => RNat(big_gcd(a, b))
    ("%nat_pow", [RNat(a), RNat(b)]) => RNat(a.pow(b))
    ("%nat_shl", [RNat(a), RNat(b)]) => RNat(a << b.to_int())
    ("%nat_shr", [RNat(a), RNat(b)]) =>
      RNat(if b.bit_length() > 31 { 0N } else { a >> b.to_int() })
    ("%nat_log2", [RNat(a)]) =>
      RNat(if a <= 1N { 0N } else { BigInt::from_int(a.bit_length() - 1) })
    ("%nat_land", [RNat(a), RNat(b)]) => RNat(a & b)
    ("%nat_lor", [RNat(a), RNat(b)]) => RNat(a | b)
    ("%nat_lxor", [RNat(a), RNat(b)]) => RNat(a ^ b)
    ("%nat_to_bigint", [RNat(a)]) => RNat(a)
    ("%nat_of_bigint", [RNat(a)]) => RNat(if a < 0N { 0N } else { a })
    // `BigInt`s are `RNat`s too
    ("%bigint_of_int", [RLit(LInt(i))]) => RNat(BigInt::from_int(i))
    ("%bigint_of_int64", [RLit(LInt64(i))]) => RNat(BigInt::from_int64(i))
    ("%bigint_to_int", [RNat(a)]) => RLit(LInt(a.to_int()))
    ("%bigint_to_int64", [RNat(a)]) => RLit(LInt64(a.to_int64()))
    ("%bigint_add", [RNat(a), RNat(b)]) => RNat(a + b)
    ("%bigint_sub", [RNat(a), RNat(b)]) => RNat(a - b)
    ("%bigint_mul", [RNat(a), RNat(b)]) => RNat(a * b)
    ("%bigint_div" | "%bigint_mod", [RNat(_), RNat(b)]) if b == 0N =>
      raise CAbort("division by zero")
    ("%bigint_div", [RNat(a), RNat(b)]) => RNat(a / b)
    ("%bigint_mod", [RNat(a), RNat(b)]) => RNat(a % b)
    ("%bigint_neg", [RNat(a)]) => RNat(-a)
    ("%bigint_land", [RNat(a), RNat(b)]) => RNat(a & b)
    ("%bigint_lor", [RNat(a), RNat(b)]) => RNat(a | b)
    ("%bigint_lxor", [RNat(a), RNat(b)]) => RNat(a ^ b)
    ("%bigint_shl", [RNat(a), RLit(LInt(n))]) => RNat(a << n)
    ("%bigint_shr", [RNat(a), RLit(LInt(n))]) => RNat(a >> n)
    ("%bigint_eq", [RNat(a), RNat(b)]) => RLit(LBool(a == b))
    ("%bigint_lt", [RNat(a), RNat(b)]) => RLit(LBool(a < b))
    ("%bigint_le", [RNat(a), RNat(b)]) => RLit(LBool(a <= b))
    ("%bigint_gt", [RNat(a), RNat(b)]) => RLit(LBool(a > b))
    ("%bigint_ge", [RNat(a), RNat(b)]) => RLit(LBool(a >= b))
    ("%bigint_compare", [RNat(a), RNat(b)]) => RLit(LInt(a.compare(b)))
    ("%bigint_pow", [RNat(a), RNat(b)]) => RNat(a.pow(b))
    ("%bigint_to_string", [RNat(a)]) => RLit(LStr(a.to_string()))
    ("%bigint_hash", [RNat(a)]) => RLit(LInt(a.hash()))
    ("%array_push", [RArr(xs), x]) => {
      xs.push(x)
      RLit(LUnit)
    }
    _ => {
      let lits : Array[@tt.Lit] = []
      for a in args {
        match a {
          RLit(l) => lits.push(l)
          _ => raise CAbort("bad arguments to primitive " + p)
        }
      }
      match @tt.prim_pure(p, lits) {
        Some(l) => RLit(l)
        None =>
          if p.has_suffix("_div") || p.has_suffix("_mod") {
            raise CAbort("division by zero")
          } else {
            raise CAbort("primitive " + p + " failed")
          }
      }
    }
  }
}

///|
fn big_gcd(a : BigInt, b : BigInt) -> BigInt {
  let mut x = a
  let mut y = b
  while y != 0N {
    let t = x % y
    x = y
    y = t
  }
  x
}

///|
/// Run `main` of the program that was last type checked.
pub fn run_main(write : (String) -> Unit) -> Unit raise RunError {
  let m = { cache: {}, write, }
  let body = match @tt.global_body("main") {
    Some(b) => b
    None => raise RunError("no main function")
  }
  ignore(m.eval(ENil, body)) catch {
    CReturn(_) => ()
    CRaise(e) => raise RunError("uncaught error: " + show_rval(e))
    CAbort(msg) => raise RunError("runtime error: " + msg)
    CBreak | CContinue => raise RunError("break/continue outside of a loop")
  }
}

///|
/// Run the global `name` (a `test` block).
pub fn run_global(
  name : String,
  write : (String) -> Unit,
) -> Unit raise RunError {
  let m = { cache: {}, write, }
  let body = match @tt.global_body(name) {
    Some(b) => b
    None => raise RunError("no definition of " + name)
  }
  ignore(m.eval(ENil, body)) catch {
    CReturn(_) => ()
    CRaise(e) => raise RunError("uncaught error: " + show_rval(e))
    CAbort(msg) => raise RunError("runtime error: " + msg)
    CBreak | CContinue => raise RunError("break/continue outside of a loop")
  }
}

///|
/// Evaluate a global constant (for tests).
pub fn eval_global(name : String) -> String raise RunError {
  let m = { cache: {}, write: _ => (), }
  show_rval(m.global(name)) catch {
    CRaise(e) => raise RunError("uncaught error: " + show_rval(e))
    CAbort(msg) => raise RunError("runtime error: " + msg)
    _ => raise RunError("control flow escaped")
  }
}
