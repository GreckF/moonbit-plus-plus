///|
/// Normalisation by evaluation.
pub fn eval(env : Env, t : Tm) -> Val {
  // out of time (see timelimit.mbt): stop computing
  if time_up() {
    return VStuck(env, t, [])
  }
  match t {
    Var(ix) => env[env.length() - 1 - ix]
    Global("%raise") => VPrim("%raise", [])
    Global(n) => global_val(n)
    Meta(m) =>
      match metas[m].sol {
        Some(v) => v
        None => VFlex(m, [])
      }
    InsertedMeta(m, mask) => {
      let mut v = match metas[m].sol {
        Some(s) => s
        None => VFlex(m, [])
      }
      for i = 0; i < mask.length(); i = i + 1 {
        if mask[i] {
          v = subst_app(v, env[i], Expl)
        }
      }
      v
    }
    Lam(x, i, g, b) => VLam(x, i, g, { env, body: b, })
    App(f, a, i) => app_val(eval(env, f), eval(env, a), i)
    Pi(x, i, g, a, b) => VPi(x, i, g, eval(env, a), { env, body: b, })
    Let(_, _, v, b) => {
      let x = eval(env, v)
      match strict(x) {
        Some(r) if is_raise(r) => r
        // the program stops there: no value for the rest
        Some(r) if is_abort(r) => VStuck(env, t, [])
        Some(_) => eval(env_push(env, x), b)
        None => VStuck(env, t, [])
      }
    }
    U => VU
    PropU => VProp
    Lit(l) => VLit(l)
    Match(scruts, cls) => match_vals(env, scruts.map(s => eval(env, s)), cls)
    Raises(a, e) => VRaises(eval(env, a), eval(env, e))
    LetMut(_, _, _, _)
    | Assign(_, _)
    | While(_, _, _)
    | Break
    | Continue
    | Return(_)
    | Raise(_)
    | Defer(_, _) => VStuck(env, t, [])
    // `a; b` where `a` only matters by its errors
    Seq(a, b) =>
      match strict(eval(env, a)) {
        Some(r) if is_raise(r) => r
        Some(x) if !has_effect(x, true) => eval(env, b)
        _ => VStuck(env, t, [])
      }
    Try(b, cls) =>
      match try_val(env, eval(env, b), cls) {
        Some(v) => v
        None => VStuck(env, t, [])
      }
    ArrayLit(es) => VArrLit(es.map(e => eval(env, e)))
  }
}

///|
pub fn global_val(n : String) -> Val {
  match globals.get(n) {
    Some(g) =>
      match g.kind {
        GFunc(_, _, _) => VGlobal(n, [])
        GData(_) => VData(n, [])
        GCon(_) => VCon(n, [])
        GPrim(_, _) => VPrim(n, [])
      }
    None => VGlobal(n, [])
  }
}

///|
pub fn inst(cl : Closure, v : Val) -> Val {
  eval(env_push(cl.env, v), cl.body)
}

///|
fn sp_push(sp : Spine, v : Val, i : Icit) -> Spine {
  let s = sp.copy()
  s.push((v, i))
  s
}

///|
pub fn app_val(f : Val, a : Val, i : Icit) -> Val {
  match f {
    // call by value: an error in the argument is the result
    VLam(_, _, _, cl) if i != Impl =>
      match strict(a) {
        Some(r) if is_raise(r) => r
        Some(_) => inst(cl, a)
        None => delayed_app(f, a, i)
      }
    VLam(_, _, _, cl) => inst(cl, a)
    VPrim("%raise", sp) if sp.length() > 0 => f
    VRigid(l, sp) => VRigid(l, sp_push(sp, a, i))
    VFlex(m, sp) => VFlex(m, sp_push(sp, a, i))
    VGlobal(n, sp) => VGlobal(n, sp_push(sp, a, i))
    VData(n, sp) => VData(n, sp_push(sp, a, i))
    VCon(n, sp) if i != Impl =>
      match strict(a) {
        Some(r) if is_raise(r) => r
        Some(_) => VCon(n, sp_push(sp, a, i))
        None => delayed_app(f, a, i)
      }
    VCon(n, sp) => VCon(n, sp_push(sp, a, i))
    VPrim(n, sp) => reduce_prim(n, sp_push(sp, a, i), lazy=true)
    VMatch(env, vs, cls, sp) => VMatch(env, vs, cls, sp_push(sp, a, i))
    VStuck(env, t, sp) => VStuck(env, t, sp_push(sp, a, i))
    _ => VStuck([], Lit(LUnit), [(f, Expl), (a, i)])
  }
}

///|
/// Apply the solution of a meta: a substitution, not a call, so an error in
/// the argument does not propagate (see raise.mbt).
fn subst_app(f : Val, a : Val, i : Icit) -> Val {
  match f {
    VLam(_, _, _, cl) => inst(cl, a)
    _ => app_val(f, a, i)
  }
}

///|
fn subst_spine(f : Val, sp : Spine) -> Val {
  let mut v = f
  for a in sp {
    v = subst_app(v, a.0, a.1)
  }
  v
}

///|
pub fn app_spine(f : Val, sp : Spine) -> Val {
  let mut v = f
  for a in sp {
    v = app_val(v, a.0, a.1)
  }
  v
}

///|
/// With `lazy` (when the primitive is applied), an argument that is not a
/// value yet and cannot raise is not computed: `force` does it when the value
/// is needed (a primitive of an argument that is large to compute, like
/// `int_to_nat(1000000).to_string()`, is not computed when it is merely
/// checked).
fn reduce_prim(n : String, sp : Spine, lazy~ : Bool = false) -> Val {
  match globals.get(n) {
    // `${ c }`, `c.run()`: the code `c` is run (see staging.mbt)
    // arrays and `print`, when a splice runs (staging.mbt)
    Some({ kind: GPrim(p, arity), .. }) if sp.length() == arity &&
      unfold_everything.val &&
      run_prim(p, sp) is Some(r) => r
    Some({ kind: GPrim("%splice" | "%run", arity), .. }) if sp.length() >= arity =>
      match splice_val(sp, arity, lazy) {
        Some(w) => w
        None => VPrim(n, sp)
      }
    Some({ kind: GPrim(p, arity), .. }) if sp.length() == arity => {
      let lits : Array[Lit] = []
      for a in sp {
        if a.1 == Expl {
          if lazy && !(a.0 is (VLit(_) | VPrim("%raise", _))) && !may_raise(a.0) {
            return VPrim(n, sp)
          }
          match force(a.0) {
            VLit(l) => lits.push(l)
            VPrim("%raise", [_, ..]) as r => return r
            _ => return VPrim(n, sp)
          }
        }
      }
      match prim_pure(p, lits) {
        Some(l) => VLit(l)
        None => VPrim(n, sp)
      }
    }
    _ => VPrim(n, sp)
  }
}

///|
/// Weak head normal form, as far as metas and folded applications allow.
pub fn force(v : Val) -> Val {
  match v {
    VFlex(m, sp) =>
      match metas[m].sol {
        Some(s) => force(subst_spine(s, sp))
        None => v
      }
    VGlobal(n, sp) =>
      match unfold(n, sp) {
        Some(w) => {
          let w = force(w)
          if is_blocked(w) {
            v
          } else {
            w
          }
        }
        None => v
      }
    VMatch(env, vs, cls, sp) =>
      match match_vals_opt(env, vs, cls) {
        Some(r) => force(app_spine(r, sp))
        None => v
      }
    // a splice of known code is that code (staging.mbt)
    VPrim(n, sp) if splice_arity(n) is Some(arity) && sp.length() >= arity =>
      match splice_val(sp, arity, false) {
        Some(w) => force(w)
        None => v
      }
    VPrim(n, sp) =>
      match reduce_prim(n, sp) {
        VPrim(_, _) => v
        w => w
      }
    _ => v
  }
}

///|
/// Like `force`, but keeps global function applications folded.
pub fn force_meta(v : Val) -> Val {
  match v {
    VFlex(m, sp) =>
      match metas[m].sol {
        Some(s) => force_meta(subst_spine(s, sp))
        None => v
      }
    VMatch(env, vs, cls, sp) =>
      match match_vals_opt(env, vs, cls) {
        Some(r) => force_meta(app_spine(r, sp))
        None => v
      }
    VPrim(n, sp) if splice_arity(n) is Some(arity) && sp.length() >= arity =>
      match splice_val(sp, arity, true) {
        Some(w) => force_meta(w)
        None => v
      }
    // (arguments that are folded applications are not computed either)
    VPrim(n, sp) =>
      match reduce_prim(n, sp, lazy=true) {
        VPrim(_, _) => v
        w => w
      }
    _ => v
  }
}

///|
/// Results that keep a function application folded.
fn is_blocked(v : Val) -> Bool {
  match v {
    // an error, and quoted code, are values
    VPrim("%raise" | "%quote", _) => false
    VMatch(_, _, _, _) | VPrim(_, _) | VStuck(_, _, _) => true
    _ => false
  }
}

///|
/// Functions that could not be unfolded because their bodies were not
/// elaborated yet (they are defined later), since the start of the current
/// declaration: an error may come from the order in which files are checked.
pub let unfolded_too_early : Array[String] = []

///|
fn note_no_body(n : String) -> Unit {
  if !unfolded_too_early.contains(n) {
    unfolded_too_early.push(n)
  }
}

///|
/// Unfold a global function applied to at least as many arguments as it
/// has leading lambdas.
pub fn unfold(n : String, sp : Spine) -> Val? {
  match strict_call(n, sp) {
    Some(r) => return r
    None => ()
  }
  if !can_unfold(n) {
    return None
  }
  match globals.get(n) {
    Some({ kind: GFunc(Some(body), false, arity), .. }) if sp.length() >= arity => {
      last_unfolded.val = Some(n)
      Some(app_spine(eval([], body), sp))
    }
    // with mutable state: run it (see exec.mbt)
    Some({ kind: GFunc(Some(body), true, arity), .. }) if sp.length() >= arity =>
      exec_call(n, body, arity, sp)
    Some({ kind: GFunc(None, _, _), .. }) => {
      note_no_body(n)
      None
    }
    _ => None
  }
}

///|
/// Before unfolding the function `n`: `Some(Some(raise e))` if an argument
/// is an error, `Some(None)` if an argument may still raise (the call stays
/// folded), `None` to go on. Also performs the delayed applications `%app`.
fn strict_call(n : String, sp : Spine) -> Val?? {
  if n == "%app" {
    return Some(
      match strict_args(sp) {
        ArgsUnknown => None
        ArgsRaise(r) => Some(r)
        ArgsOk => Some(app_spine(sp[0].0, sp[1:].to_array()))
      },
    )
  }
  match globals.get(n) {
    Some({ kind: GFunc(Some(_), _, arity), .. }) if sp.length() >= arity =>
      match strict_args(sp) {
        ArgsUnknown => Some(None)
        ArgsRaise(r) => Some(Some(r))
        ArgsOk => None
      }
    _ => None
  }
}

///|
/// Unfold regardless of the number of arguments (used by conversion).
pub fn unfold_any(n : String, sp : Spine) -> Val? {
  match strict_call(n, sp) {
    Some(r) => return r
    None => ()
  }
  if !can_unfold(n) {
    return None
  }
  match globals.get(n) {
    Some({ kind: GFunc(Some(body), false, _), .. }) =>
      Some(app_spine(eval([], body), sp))
    Some({ kind: GFunc(Some(body), true, arity), .. }) if sp.length() >= arity =>
      exec_call(n, body, arity, sp)
    Some({ kind: GFunc(None, _, _), .. }) => {
      note_no_body(n)
      None
    }
    _ => None
  }
}

// ---------------------------------------------------------------------------
// Pattern matching

///|
priv enum MatchRes {
  Matched
  Failed
  Stuck
}

///|
fn match_pat(p : CPat, v : Val, out : Array[Val]) -> MatchRes {
  out.push(v)
  match p {
    CPVar(_) | CPWild => Matched
    CPCon(c, ps) =>
      match force(v) {
        VCon(c2, sp) => {
          if c2 != c {
            return Failed
          }
          let np = match con_info(c) {
            Some(ci) => ci.nparams
            None => 0
          }
          if sp.length() - np != ps.length() {
            return Stuck
          }
          let mut res = Matched
          for k = 0; k < ps.length(); k = k + 1 {
            match match_pat(ps[k], sp[np + k].0, out) {
              Failed => return Failed
              Stuck => res = Stuck
              Matched => ()
            }
          }
          res
        }
        _ => Stuck
      }
    CPLit(l) =>
      match force(v) {
        VLit(l2) => if l == l2 { Matched } else { Failed }
        _ => Stuck
      }
  }
}

///|
/// Select the first clause that matches; `None` if the match is blocked.
pub fn match_vals_opt(env : Env, vs : Array[Val], cls : Array[Clause]) -> Val? {
  // call by value: the scrutinees are evaluated first
  for v in vs {
    match strict(v) {
      Some(r) if is_raise(r) => return Some(r)
      Some(_) => ()
      None => return None
    }
  }
  for cl in cls {
    let out : Array[Val] = []
    let mut res = Matched
    for k = 0; k < cl.pats.length(); k = k + 1 {
      match match_pat(cl.pats[k], vs[k], out) {
        Failed => {
          res = Failed
          break
        }
        Stuck => res = Stuck
        Matched => ()
      }
    }
    match res {
      Matched => {
        let env2 = env.copy()
        for v in out {
          env2.push(v)
        }
        match cl.cond {
          Some(g) =>
            match force(eval(env2, g)) {
              VLit(LBool(true)) => ()
              VLit(LBool(false)) => continue
              _ => return None
            }
          None => ()
        }
        return Some(eval(env2, cl.body))
      }
      Failed => continue
      Stuck => return None
    }
  }
  None
}

///|
fn match_vals(env : Env, vs : Array[Val], cls : Array[Clause]) -> Val {
  match match_vals_opt(env, vs, cls) {
    Some(v) => v
    None => VMatch(env, vs, cls, [])
  }
}

// ---------------------------------------------------------------------------
// Quotation

///|
fn quote_sp(lvl : Int32, h : Tm, sp : Spine, full : Bool) -> Tm {
  let mut t = h
  for a in sp {
    t = App(t, quote_with(lvl, a.0, full), a.1)
  }
  t
}

///|
pub fn fresh_vars(lvl : Int32, k : Int32) -> Array[Val] {
  let out : Array[Val] = []
  for j = 0; j < k; j = j + 1 {
    out.push(v_var(lvl + j))
  }
  out
}

///|
/// Evaluate the body of a clause of a blocked match under fresh variables.
pub fn clause_body_val(env : Env, lvl : Int32, cl : Clause) -> Val {
  eval(concat(env, fresh_vars(lvl, pats_slots(cl.pats))), cl.body)
}

///|
/// Evaluate the guard of a clause of a blocked match under fresh variables.
pub fn clause_guard_val(env : Env, lvl : Int32, cl : Clause) -> Val? {
  cl.cond.map(g => eval(concat(env, fresh_vars(lvl, pats_slots(cl.pats))), g))
}

///|
pub fn quote(lvl : Int32, v : Val) -> Tm {
  quote_with(lvl, v, false)
}

///|
/// Quote, unfolding global functions where they reduce.
pub fn quote_full(lvl : Int32, v : Val) -> Tm {
  quote_with(lvl, v, true)
}

///|
fn quote_with(lvl : Int32, v : Val, full : Bool) -> Tm {
  let q = (l : Int32, x : Val) => quote_with(l, x, full)
  match (if full { force(v) } else { force_meta(v) }) {
    VRigid(l, sp) => quote_sp(lvl, Var(lvl - 1 - l), sp, full)
    VFlex(m, sp) => quote_sp(lvl, Meta(m), sp, full)
    VGlobal(n, sp) | VData(n, sp) | VCon(n, sp) | VPrim(n, sp) =>
      quote_sp(lvl, Global(n), sp, full)
    VLam(x, i, g, cl) => Lam(x, i, g, q(lvl + 1, inst(cl, v_var(lvl))))
    VPi(x, i, g, a, cl) =>
      Pi(x, i, g, q(lvl, a), q(lvl + 1, inst(cl, v_var(lvl))))
    VU => U
    VProp => PropU
    VLit(l) => Lit(l)
    VRaises(a, e) => Raises(q(lvl, a), q(lvl, e))
    VMatch(env, vs, cls, sp) => {
      let cls2 = cls.map(cl => {
        let l2 = lvl + pats_slots(cl.pats)
        {
          pats: cl.pats,
          cond: clause_guard_val(env, lvl, cl).map(g => q(l2, g)),
          body: q(l2, clause_body_val(env, lvl, cl)),
        }
      })
      quote_sp(lvl, Match(vs.map(x => q(lvl, x)), cls2), sp, full)
    }
    VStuck(_, t, sp) => quote_sp(lvl, t, sp, full)
    VArrLit(vs) => ArrayLit(vs.map(x => q(lvl, x)))
  }
}

///|
pub fn nf(env : Env, t : Tm) -> Tm {
  quote(env.length(), eval(env, t))
}

///|
/// A call of `abort` or `panic`: the program stops.
fn is_abort(v : Val) -> Bool {
  match force(v) {
    VPrim(n, _) =>
      match globals.get(n) {
        Some({ kind: GPrim(p, _), .. }) => p == "%abort" || p == "%panic"
        _ => false
      }
    _ => false
  }
}
