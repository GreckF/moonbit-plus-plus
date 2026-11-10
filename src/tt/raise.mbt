///|
/// Errors as values of the logic. A call that raises an error computes, during
/// type checking, to the value `raise e` (`%raise(e)`), which can be written
/// in types, compared and caught by `try`. Errors propagate as at run time
/// (call by value):
///
/// - a match on `raise e`, a call or a constructor with an argument
///   `raise e`, and `let x = raise e; ...` are `raise e`;
/// - a function body is not run before it is called: `(x) => raise e` is a
///   value;
/// - a function is only unfolded on arguments that are known not to raise:
///   with an argument that is a raising call that cannot run yet (it depends
///   on a variable), the call stays folded. Otherwise `const0(head(xs))`
///   would be `0`, but it raises when `xs` is empty.
///
/// Implicit arguments are erased, so they are not evaluated at run time and
/// do not propagate errors.

///|
pub fn raise_val(e : Val) -> Val {
  VPrim("%raise", [(e, Expl)])
}

///|
pub fn is_raise(v : Val) -> Bool {
  v is VPrim("%raise", _)
}

///|
/// An application that waits for an argument that may raise: `%app(f, a)`
/// is `f(a)` once `a` is known (a value or an error).
fn delayed_app(f : Val, a : Val, i : Icit) -> Val {
  VGlobal("%app", [(f, Expl), (a, i)])
}

///|
let raises_cache : Map[String, Bool] = {}

///|
/// Does a saturated call of the global `n` raise errors?
fn global_raises(n : String) -> Bool {
  match raises_cache.get(n) {
    Some(b) => b
    None => {
      let b = match globals.get(n) {
        Some({ kind: GFunc(_, _, arity), .. }) => fn_raises(n, arity)
        _ => false
      }
      // a global without a body yet may get one: only remember defined ones
      if globals.get(n) is Some({ kind: GFunc(Some(_), _, _), .. }) {
        raises_cache.set(n, b)
      }
      b
    }
  }
}

///|
fn global_arity(n : String) -> Int32 {
  match globals.get(n) {
    Some({ kind: GFunc(_, _, arity), .. }) => arity
    _ => 0
  }
}

///|
fn sp_may_raise(sp : Spine) -> Bool {
  sp.iter().any(a => a.1 != Impl && may_raise(a.0))
}

///|
/// Could `v` be an error that is not computed yet (or an error)? Constructor
/// applications never are: a constructor applied to such an argument is a
/// `%app`.
pub fn may_raise(v : Val) -> Bool {
  match force_meta(v) {
    VPrim("%raise", _) => true
    VGlobal(n, sp) =>
      (
        sp.length() >= global_arity(n) &&
        (global_raises(n) || call_raises(n, sp))
      ) ||
      sp_may_raise(sp)
    // code that is not known yet may raise when it is run (staging.mbt)
    VPrim(n, sp) if splice_may_raise(n, sp) => true
    VRigid(_, sp) | VFlex(_, sp) | VPrim(_, sp) => sp_may_raise(sp)
    VMatch(_, vs, cls, sp) =>
      vs.iter().any(may_raise) ||
      sp_may_raise(sp) ||
      cls
      .iter()
      .any(cl => {
        cl.cond.map(tm_may_raise).unwrap_or(false) || tm_may_raise(cl.body)
      })
    VStuck(_, t, sp) => tm_may_raise(t) || sp_may_raise(sp)
    VArrLit(vs) => vs.iter().any(may_raise)
    _ => false
  }
}

///|
/// Could evaluating `t` raise an error (outside of the lambdas of `t`)?
fn tm_may_raise(t : Tm) -> Bool {
  match t {
    Raise(_) => true
    Global("%raise") => true
    App(_, _, _) => {
      let (h, args) = flatten_app(t)
      (h is Global(n) && args.length() >= global_arity(n) && global_raises(n)) ||
      // a splice of code that raises (staging.mbt)
      (
        h is Global(n) &&
        is_splice_prim(n) &&
        args.length() >= 2 &&
        args[0].0 is Raises(_, _)
      ) ||
      // an effect polymorphic function given a lambda that raises
      (
        h is Global(n) &&
        global_row_has_var(n) &&
        args.iter().any(a => a.0 is Lam(_, _, _, b) && lam_body_raises(b))
      ) ||
      tm_may_raise(h) ||
      args.iter().any(a => a.1 != Impl && tm_may_raise(a.0))
    }
    Let(_, _, v, b) | LetMut(_, _, v, b) => tm_may_raise(v) || tm_may_raise(b)
    Match(ss, cls) =>
      ss.iter().any(tm_may_raise) ||
      cls
      .iter()
      .any(cl => {
        cl.cond.map(tm_may_raise).unwrap_or(false) || tm_may_raise(cl.body)
      })
    Try(b, cls) =>
      tm_may_raise(b) ||
      cls
      .iter()
      .any(cl => {
        cl.cond.map(tm_may_raise).unwrap_or(false) || tm_may_raise(cl.body)
      })
    Assign(_, v) | Return(v) => tm_may_raise(v)
    While(c, b, s) => tm_may_raise(c) || tm_may_raise(b) || tm_may_raise(s)
    Seq(a, b) | Defer(a, b) => tm_may_raise(a) || tm_may_raise(b)
    ArrayLit(es) => es.iter().any(tm_may_raise)
    _ => false
  }
}

///|
/// Evaluate `v` as far as needed to know whether it is an error: `Some` of
/// the value (`raise e` for an error), or `None` if that is not known yet.
pub fn strict(v : Val) -> Val? {
  if !may_raise(v) {
    return Some(v)
  }
  let w = force(v)
  if is_raise(w) {
    Some(w)
  } else if may_raise(w) {
    None
  } else {
    Some(w)
  }
}

///|
priv enum ArgsRes {
  ArgsOk
  ArgsRaise(Val)
  ArgsUnknown
}

///|
/// The arguments of a call, from left to right: all known values, or the
/// first error, or an argument not known yet.
fn strict_args(sp : Spine) -> ArgsRes {
  for a in sp {
    if a.1 == Impl {
      continue
    }
    match strict(a.0) {
      Some(w) => if is_raise(w) { return ArgsRaise(w) }
      None => return ArgsUnknown
    }
  }
  ArgsOk
}

///|
/// `try body catch { cls }` on the value of `body`: `None` while it is not
/// known whether `body` raises.
fn try_val(env : Env, b : Val, cls : Array[Clause]) -> Val? {
  match strict(b) {
    Some(VPrim("%raise", [(e, _), ..]) as r) =>
      match match_vals_opt(env, [e], cls) {
        Some(v) => Some(v)
        // no arm applies: the error goes on
        None => if no_clause_applies([e], cls) { Some(r) } else { None }
      }
    Some(w) => Some(w)
    None => None
  }
}

///|
/// Does every clause fail on `vs` (rather than being blocked)?
fn no_clause_applies(vs : Array[Val], cls : Array[Clause]) -> Bool {
  cls
  .iter()
  .all(cl => {
    let out : Array[Val] = []
    let mut failed = false
    for k = 0; k < cl.pats.length(); k = k + 1 {
      match match_pat(cl.pats[k], vs[k], out) {
        Failed => {
          failed = true
          break
        }
        Stuck => return false
        Matched => ()
      }
    }
    failed
  })
}

///|
/// Does a call of the effect polymorphic function `n` raise, once its
/// effect variable is instantiated by the spine `sp` (an argument that
/// raises makes the call raise)?
fn call_raises(n : String, sp : Spine) -> Bool {
  if !global_row_has_var(n) {
    return false
  }
  let arity = global_arity(n)
  let mut t = match globals.get(n) {
    Some(g) => g.vty
    None => return false
  }
  for k = 0; k < arity; k = k + 1 {
    match force(t) {
      VPi(_, _, _, _, cl) => t = inst(cl, sp[k].0)
      _ => return false
    }
  }
  match force(t) {
    VRaises(_, e) => effect_of(e).1 is Some(_)
    _ => false
  }
}

///|
/// Does the body of a lambda (under its parameters) raise?
fn lam_body_raises(b : Tm) -> Bool {
  match b {
    Lam(_, _, _, b2) => lam_body_raises(b2)
    _ => tm_may_raise(b)
  }
}
