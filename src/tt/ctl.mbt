///|
/// `ctl` operations (see doc/mbtpp/effects.md): handlers that resume any
/// number of times. Code that may perform them is translated into code that
/// returns a computation, a value of `%Comp`:
///
/// - `Pure(v)`: done, with the value `v`;
/// - `Op(m, i, p, k)`: performs operation `i` of the handler with marker `m`;
///   `p` applies a function to the operation's arguments, `k` is the rest of
///   the computation, given the result of the operation;
/// - `Ret(v)`, `Brk`, `Cont`: `return v`, `break` and `continue`, on their
///   way to the function or the loop.
///
/// A handler (`%eff_handle`) runs the arm of its operations, with `resume`
/// = `v => handle(k(v))`, and passes the others on with a longer `k`. The
/// marker of a handler is fresh each time it runs: handlers are lexically
/// scoped. `let mut` variables keep their values per resumption: each bind
/// saves the variables of its function when an operation passes, and the
/// continuation restores them.
///
/// During elaboration, effectful calls are marked `%mcall[row](call)`, and
/// function bodies `%mbody[row](body)`; a `try` with `ctl` arms is
/// `%handle(marker, dispatch, body)`. When a body is stored, the marks are
/// lowered (`lower`): bodies whose row has a `ctl` effect are translated,
/// the others keep direct code. A function with an effect variable gets a
/// translated version `f$m`, used where the variable stands for `ctl`
/// effects.

// ---------------------------------------------------------------------------
// Named terms, to write the runtime

///|
priv enum N {
  NV(String)
  NG(String)
  NLit(Lit)
  NApp(N, Array[N])
  NLam(Array[String], N)
  NLet(String, N, N)
  NSeq(N, N)
  /// A match on a `%Comp`: (constructor, variables, body), and a default
  /// (the value is bound to the given name).
  NCase(N, Array[(String, Array[String], N)], (String, N)?)
  NIf(N, N, N)
  NCon(String, Array[N])
}

///|
fn n_index(scope : Array[String], x : String) -> Int32 {
  for k = scope.length() - 1; k >= 0; k = k - 1 {
    if scope[k] == x {
      return scope.length() - 1 - k
    }
  }
  abort("ctl runtime: unbound " + x)
}

///|
fn n_tm(n : N, scope : Array[String]) -> Tm {
  match n {
    NV(x) => Var(n_index(scope, x))
    NG(g) => Global(g)
    NLit(l) => Lit(l)
    NApp(f, args) => {
      let mut t = n_tm(f, scope)
      for a in args {
        t = App(t, n_tm(a, scope), Expl)
      }
      t
    }
    NLam(xs, b) => {
      let s = concat(scope, xs)
      let mut t = n_tm(b, s)
      for k = xs.length() - 1; k >= 0; k = k - 1 {
        t = Lam(xs[k], Expl, true, t)
      }
      t
    }
    NLet(x, v, b) => Let(x, any_ty(), n_tm(v, scope), n_tm(b, push1(scope, x)))
    NSeq(a, b) => Seq(n_tm(a, scope), n_tm(b, scope))
    NCase(s, cases, dflt) => {
      let cls : Array[Clause] = []
      for c in cases {
        let (con, xs, body) = c
        let s2 = concat(push1(scope, "%con"), xs)
        cls.push({
          pats: [CPCon("%Comp::" + con, xs.map(x => CPVar(x)))],
          cond: None,
          body: n_tm(body, s2),
        })
      }
      match dflt {
        Some((x, body)) =>
          cls.push({
            pats: [CPVar(x)],
            cond: None,
            body: n_tm(body, push1(scope, x)),
          })
        None => ()
      }
      Match([n_tm(s, scope)], cls)
    }
    NIf(c, t, f) =>
      Match([n_tm(c, scope)], [
        {
          pats: [CPLit(LBool(true))],
          cond: None,
          body: n_tm(t, push1(scope, "%t")),
        },
        { pats: [CPWild], cond: None, body: n_tm(f, push1(scope, "%f")), },
      ])
    NCon(c, fields) => comp(c, fields.map(f => n_tm(f, scope)))
  }
}

///|
/// The type of the runtime's values (not erased; never checked).
fn any_ty() -> Tm {
  Global("%Any")
}

///|
/// A `%Comp` constructor applied to its fields (its four type parameters are
/// not used).
fn comp(con : String, fields : Array[Tm]) -> Tm {
  let mut t = Global("%Comp::" + con)
  for _ in 0..<4 {
    t = App(t, any_ty(), Impl)
  }
  for f in fields {
    t = App(t, f, Expl)
  }
  t
}

///|
fn napp(g : String, args : Array[N]) -> N {
  NApp(NG(g), args)
}

///|
let ctl_ready : Ref[Bool] = @percheck.cell(false)

///|
/// Define the runtime of `ctl` operations (once per check).
fn ensure_ctl_runtime() -> Unit {
  if ctl_ready.val && globals.contains("%eff_bind") {
    return
  }
  ctl_ready.val = true
  let any = any_ty()
  let fn_ty = (n : Int32) => {
    let mut t = any
    for _ in 0..<n {
      t = Pi("_", Expl, true, any, t)
    }
    t
  }
  let def = (name : String, params : Array[String], body : N) => {
    register(name, fn_ty(params.length()), GFunc(None, false, params.length()))
    let t = n_tm(NLam(params, body), [])
    globals.get(name).unwrap().kind = GFunc(
      Some(t),
      contains_imperative(t),
      params.length(),
    )
  }
  register(
    "%effect_marker",
    Pi("_", Expl, true, Global("Unit"), Global("Int")),
    GPrim("%effect_marker", 1),
  )
  // bind(c, f, save): `save()` saves the `let mut` variables of the bind's
  // function and returns their restorer
  def(
    "%eff_bind",
    ["c", "f", "save"],
    NCase(
      NV("c"),
      [
        ("Pure", ["v"], NApp(NV("f"), [NV("v")])),
        (
          "Op",
          ["m", "i", "p", "k"],
          NLet(
            "r",
            NApp(NV("save"), [NLit(LUnit)]),
            NCon("Op", [
              NV("m"),
              NV("i"),
              NV("p"),
              NLam(
                ["v"],
                NSeq(
                  NApp(NV("r"), [NLit(LUnit)]),
                  napp("%eff_bind", [
                    NApp(NV("k"), [NV("v")]),
                    NV("f"),
                    NV("save"),
                  ]),
                ),
              ),
            ]),
          ),
        ),
      ],
      Some(("other", NV("other"))),
    ),
  )
  // handle(c, marker, dispatch): dispatch(i, p, resume)
  def(
    "%eff_handle",
    ["c", "marker", "dispatch"],
    NCase(
      NV("c"),
      [
        (
          "Op",
          ["m", "i", "p", "k"],
          NLet(
            "resume",
            NLam(
              ["v"],
              napp("%eff_handle", [
                NApp(NV("k"), [NV("v")]),
                NV("marker"),
                NV("dispatch"),
              ]),
            ),
            NIf(
              napp("Int::op_equal", [NV("m"), NV("marker")]),
              NApp(NV("dispatch"), [NV("i"), NV("p"), NV("resume")]),
              NCon("Op", [NV("m"), NV("i"), NV("p"), NV("resume")]),
            ),
          ),
        ),
      ],
      Some(("other", NV("other"))),
    ),
  )
  // the value of a computation in direct code
  def(
    "%eff_run",
    ["c"],
    NCase(
      NV("c"),
      [("Pure", ["v"], NV("v"))],
      Some(
        (
          "other",
          napp("abort", [NLit(LStr("an effect operation was not handled"))]),
        ),
      ),
    ),
  )
  // the end of a function: `return v` is its result
  def(
    "%eff_fn",
    ["c"],
    NCase(
      NV("c"),
      [
        ("Ret", ["v"], NCon("Pure", [NV("v")])),
        (
          "Op",
          ["m", "i", "p", "k"],
          NCon("Op", [
            NV("m"),
            NV("i"),
            NV("p"),
            NLam(["v"], napp("%eff_fn", [NApp(NV("k"), [NV("v")])])),
          ]),
        ),
      ],
      Some(("other", NV("other"))),
    ),
  )
  // the body of a loop, then `next(())` (also on `continue`), or `done`
  // on `break`
  def(
    "%eff_body",
    ["c", "next"],
    NCase(
      NV("c"),
      [
        ("Pure", ["v"], NApp(NV("next"), [NLit(LUnit)])),
        ("Cont", [], NApp(NV("next"), [NLit(LUnit)])),
        ("Brk", [], NCon("Pure", [NLit(LUnit)])),
        (
          "Op",
          ["m", "i", "p", "k"],
          NCon("Op", [
            NV("m"),
            NV("i"),
            NV("p"),
            NLam(
              ["v"],
              napp("%eff_body", [NApp(NV("k"), [NV("v")]), NV("next")]),
            ),
          ]),
        ),
      ],
      Some(("other", NV("other"))),
    ),
  )
  // while(cond, body, step): thunks of computations
  def(
    "%eff_while",
    ["cond", "body", "step"],
    napp("%eff_bind", [
      NApp(NV("cond"), [NLit(LUnit)]),
      NLam(
        ["b"],
        NIf(
          NV("b"),
          napp("%eff_body", [
            NApp(NV("body"), [NLit(LUnit)]),
            NLam(
              ["_"],
              napp("%eff_bind", [
                NApp(NV("step"), [NLit(LUnit)]),
                NLam(
                  ["_"],
                  napp("%eff_while", [NV("cond"), NV("body"), NV("step")]),
                ),
                NG("%eff_nosave"),
              ]),
            ),
          ]),
          NCon("Pure", [NLit(LUnit)]),
        ),
      ),
      NG("%eff_nosave"),
    ]),
  )
  def("%eff_nosave", ["_"], NLam(["_"], NLit(LUnit)))
}

// ---------------------------------------------------------------------------
// Shifting

///|
/// Shift the free variables (index >= c) of `t` by `d`; all constructs.
pub fn shift_tm(t : Tm, d : Int32, c : Int32) -> Tm {
  if d == 0 {
    return t
  }
  let go = (x : Tm) => shift_tm(x, d, c)
  let cl = (k : Clause) => k.map(b => shift_tm(b, d, c + pats_slots(k.pats)))
  match t {
    Var(ix) => if ix >= c { Var(ix + d) } else { t }
    Lam(x, i, g, b) => Lam(x, i, g, shift_tm(b, d, c + 1))
    App(f, a, i) => App(go(f), go(a), i)
    Pi(x, i, g, a, b) => Pi(x, i, g, go(a), shift_tm(b, d, c + 1))
    Let(x, a, v, b) => Let(x, go(a), go(v), shift_tm(b, d, c + 1))
    LetMut(x, a, v, b) => LetMut(x, go(a), go(v), shift_tm(b, d, c + 1))
    Assign(ix, v) => Assign(if ix >= c { ix + d } else { ix }, go(v))
    Match(ss, cls) => Match(ss.map(go), cls.map(cl))
    Try(b, cls) => Try(go(b), cls.map(cl))
    Raises(a, e) => Raises(go(a), go(e))
    While(a, b, s) => While(go(a), go(b), go(s))
    Return(v) => Return(go(v))
    Raise(v) => Raise(go(v))
    Seq(a, b) => Seq(go(a), go(b))
    Defer(a, b) => Defer(go(a), go(b))
    ArrayLit(es) => ArrayLit(es.map(go))
    _ => t
  }
}

// ---------------------------------------------------------------------------
// Marks

///|
fn mark(g : String, row : Tm, t : Tm) -> Tm {
  App(App(Global(g), row, Impl), t, Expl)
}

///|
/// Could a row contain `ctl` effects (now or once its metas are solved)?
fn row_may_ctl(row : Val) -> Bool {
  let (items, tail) = row_flat(row)
  items.iter().any(it => item_effect(it) is Some(n) && is_ctl_effect(n)) ||
  !(tail is VData("%RowNil", _))
}

///|
/// Mark an effectful call (or `perform`) whose row may contain `ctl` effects.
fn mark_call(cxt : Cxt, t : Tm, row : Val) -> Tm {
  if cxt.in_type || !row_may_ctl(row) {
    t
  } else {
    mark("%mcall", cxt.quote(row), t)
  }
}

///|
/// Mark the body of a function or lambda whose row may contain `ctl` effects.
fn mark_body(cxt : Cxt, t : Tm, row : Val) -> Tm {
  if cxt.in_type || !row_may_ctl(row) {
    t
  } else {
    mark("%mbody", cxt.quote(row), t)
  }
}

///|
/// Does the effect have `ctl` operations (`%Resume`: the calls of `resume`)?
fn is_ctl_effect(name : String) -> Bool {
  name == "%Resume" ||
  (match effect_decls.get(name) {
    Some(ops) => ops.iter().any(op => effect_ops[op].ctl)
    None => false
  })
}

///|
/// Is a (marked) row `ctl`? Effect variables are when `vars` is set (in the
/// translated version of a function).
fn row_is_ctl(row : Tm, vars : Bool) -> Bool {
  let mut r = row
  while r is App(App(Global("%Row"), item, _), rest, _) {
    match flatten_app(item).0 {
      Global(n) if is_ctl_effect(n) => return true
      Var(_) => if vars { return true }
      _ => ()
    }
    r = rest
  }
  match flatten_app(r).0 {
    Var(_) => vars
    _ => false
  }
}

///|
/// Does the row of a function's type have an effect variable?
fn global_row_has_var(name : String) -> Bool {
  match globals.get(name) {
    Some({ ty, kind: GFunc(_, _, n), .. }) => {
      let mut t = ty
      for _ in 0..<n {
        match t {
          Pi(_, _, _, _, b) => t = b
          _ => return false
        }
      }
      match t {
        Raises(_, App(App(Global("%Effs"), row, _), _, _)) => {
          let mut r = row
          while r is App(App(Global("%Row"), _, _), rest, _) {
            r = rest
          }
          flatten_app(r).0 is Var(_)
        }
        _ => false
      }
    }
    _ => false
  }
}

// ---------------------------------------------------------------------------
// Lowering

///|
/// Marked bodies of functions, for their translated versions.
let marked_bodies : Map[String, Tm] = @percheck.map()

///|
/// Translated versions waiting for the body of their function.
let pending_m : Array[String] = @percheck.array()

///|
/// An error found while translating (reported by the declaration).
let ctl_error : Ref[String?] = @percheck.cell(None)

///|
/// The body to store for the function `name` (marked `body`).
fn lower_body(name : String, body : Tm) -> Tm {
  if has_marks(body) {
    marked_bodies.set(name, body)
  }
  let out = lower(body, false)
  if pending_m.contains(name) {
    pending_m.retain(n => n != name)
    make_m(name)
  }
  out
}

///|
fn has_marks(t : Tm) -> Bool {
  match t {
    Global("%mcall" | "%mbody" | "%marm" | "%handle") => true
    App(f, a, _) => has_marks(f) || has_marks(a)
    Lam(_, _, _, b) => has_marks(b)
    Let(_, _, v, b) | LetMut(_, _, v, b) => has_marks(v) || has_marks(b)
    Match(ss, cls) | Try(Match(ss, _), cls) =>
      ss.iter().any(has_marks) ||
      cls
      .iter()
      .any(c => has_marks(c.body) || c.cond.map(has_marks).unwrap_or(false))
    Try(b, cls) =>
      has_marks(b) ||
      cls
      .iter()
      .any(c => has_marks(c.body) || c.cond.map(has_marks).unwrap_or(false))
    While(a, b, s) => has_marks(a) || has_marks(b) || has_marks(s)
    Seq(a, b) | Defer(a, b) => has_marks(a) || has_marks(b)
    Assign(_, v) | Return(v) | Raise(v) => has_marks(v)
    ArrayLit(es) => es.iter().any(has_marks)
    _ => false
  }
}

///|
/// Make the translated version `name$m` of a function with an effect
/// variable, now or once its body is known.
fn ensure_m(name : String) -> String {
  let m = name + "$m"
  if globals.contains(m) {
    return m
  }
  let g = globals.get(name).unwrap()
  let n = match g.kind {
    GFunc(_, _, n) => n
    _ => 0
  }
  register(m, g.ty, GFunc(None, false, n))
  if marked_bodies.contains(name) {
    make_m(name)
  } else if !pending_m.contains(name) {
    pending_m.push(name)
  }
  m
}

///|
fn make_m(name : String) -> Unit {
  let m = name + "$m"
  match (marked_bodies.get(name), globals.get(m)) {
    (Some(body), Some(g)) =>
      match g.kind {
        GFunc(_, _, n) => {
          let t = lower(body, true)
          g.kind = GFunc(Some(t), contains_imperative(t), n)
          // unfolded where the function is (controlled unfolding)
          unfold_deps.set(m, [name])
        }
        _ => ()
      }
    _ => ()
  }
}

///|
/// Remove the marks of direct code, translating the bodies of `ctl`
/// functions and the `try`s with `ctl` arms. `vars`: effect variables stand
/// for `ctl` effects.
fn lower(t : Tm, vars : Bool) -> Tm {
  let go = (x : Tm) => lower(x, vars)
  match t {
    App(App(Global("%mcall"), _, _), c, _) => go(c)
    App(App(Global("%mbody"), row, _), b, _) =>
      if row_is_ctl(row, vars) {
        App(Global("%eff_fn"), m_tr(b, vars, []), Expl)
      } else {
        go(b)
      }
    // the body of a `ctl` arm: its `return` goes on to the function
    App(App(Global("%marm"), _, _), b, _) => m_tr(b, vars, [])
    App(App(App(Global("%handle"), marker, _), dispatch, _), body, _) => {
      let h = handle_tm(marker, dispatch, body, vars)
      // `return`, `break` and `continue` in the body or the arms leave the
      // `try`: done here, in direct code
      let ret = has_jump(body, true, false) || has_jump(dispatch, true, false)
      let brk = has_jump(body, false, false) || has_jump(dispatch, false, false)
      if !ret && !brk {
        return App(Global("%eff_run"), h, Expl)
      }
      let pv = (c : String) => [CPCon("%Comp::" + c, [CPVar("v")])]
      let cls : Array[Clause] = [
        { pats: pv("Pure"), cond: None, body: Var(0), },
      ]
      if ret {
        cls.push({ pats: pv("Ret"), cond: None, body: Return(Var(0)), })
      }
      if brk {
        cls.push({ pats: [CPCon("%Comp::Brk", [])], cond: None, body: Break, })
        cls.push({
          pats: [CPCon("%Comp::Cont", [])],
          cond: None,
          body: Continue,
        })
      }
      cls.push({
        pats: [CPVar("c")],
        cond: None,
        body: App(Global("%eff_run"), Var(0), Expl),
      })
      Match([h], cls)
    }
    App(f, a, i) => App(go(f), go(a), i)
    Lam(x, i, g, b) => Lam(x, i, g, go(b))
    Let(x, a, v, b) => Let(x, a, go(v), go(b))
    LetMut(x, a, v, b) => LetMut(x, a, go(v), go(b))
    Assign(ix, v) => Assign(ix, go(v))
    Match(ss, cls) => Match(ss.map(go), cls.map(c => c.map(go)))
    Try(b, cls) => Try(go(b), cls.map(c => c.map(go)))
    While(a, b, s) => While(go(a), go(b), go(s))
    Return(v) => Return(go(v))
    Raise(v) => Raise(go(v))
    Seq(a, b) => Seq(go(a), go(b))
    Defer(a, b) => Defer(go(a), go(b))
    ArrayLit(es) => ArrayLit(es.map(go))
    _ => t
  }
}

///|
/// A handler: its body is translated (a new function frame).
fn handle_tm(marker : Tm, dispatch : Tm, body : Tm, vars : Bool) -> Tm {
  App(
    App(
      App(Global("%eff_handle"), m_tr(body, vars, []), Expl),
      lower(marker, vars),
      Expl,
    ),
    lower(dispatch, vars),
    Expl,
  )
}

// ---------------------------------------------------------------------------
// Translation

///|
/// Can `t` be evaluated directly in translated code: no `ctl` call, no
/// `return`, no `break`/`continue` out of `t`?
fn is_direct(t : Tm, vars : Bool, loops : Int32) -> Bool {
  let go = (x : Tm) => is_direct(x, vars, loops)
  match t {
    App(App(Global("%mcall"), row, _), c, _) => !row_is_ctl(row, vars) && go(c)
    App(App(App(Global("%handle"), _, _), _, _), _, _) => false
    Return(_) => false
    Break | Continue => loops > 0
    While(a, b, s) =>
      go(a) && is_direct(b, vars, loops + 1) && is_direct(s, vars, loops + 1)
    // a lambda is a value; its body is lowered on its own
    Lam(_, _, _, _) => true
    App(f, a, _) => go(f) && go(a)
    Let(_, _, v, b) | LetMut(_, _, v, b) => go(v) && go(b)
    Match(ss, cls) | Try(Match(ss, _), cls) =>
      ss.iter().all(go) &&
      cls.iter().all(c => go(c.body) && c.cond.map(go).unwrap_or(true))
    Try(b, cls) =>
      go(b) && cls.iter().all(c => go(c.body) && c.cond.map(go).unwrap_or(true))
    Seq(a, b) | Defer(a, b) => go(a) && go(b)
    Assign(_, v) | Raise(v) => go(v)
    ArrayLit(es) => es.iter().all(go)
    _ => true
  }
}

///|
fn pure_tm(t : Tm) -> Tm {
  comp("Pure", [t])
}

///|
/// `%eff_bind(c, f, save)`; `muts` are the indices of the `let mut`
/// variables of the frame, where the bind is.
fn bind_tm(c : Tm, f : Tm, muts : Array[Int32]) -> Tm {
  App(App(App(Global("%eff_bind"), c, Expl), f, Expl), save_tm(muts), Expl)
}

///|
/// A function saving the variables `muts` (indices) and returning their
/// restorer.
fn save_tm(muts : Array[Int32]) -> Tm {
  if muts.length() == 0 {
    return Global("%eff_nosave")
  }
  let n = muts.length()
  // under `_` and the saved values s0 .. s(n-1), then `_` again
  let mut restore = Lit(LUnit)
  for k = n - 1; k >= 0; k = k - 1 {
    // inside the restorer: `_`(0), s(n-1) .. s0, `_`
    let s_ix = 1 + (n - 1 - k)
    let x_ix = muts[k] + 1 + n + 1
    restore = Seq(Assign(x_ix, Var(s_ix)), restore)
  }
  let mut body = Lam("_", Expl, true, restore)
  for k = n - 1; k >= 0; k = k - 1 {
    // `let s_k = x_k`, under `_` and s0 .. s(k-1)
    body = Let("s", any_ty(), Var(muts[k] + 1 + k), body)
  }
  Lam("_", Expl, true, body)
}

///|
/// Shift the indices of `let mut` variables when going under `d` binders.
fn shift_muts(muts : Array[Int32], d : Int32) -> Array[Int32] {
  muts.map(i => i + d)
}

///|
/// The translation of `t`: a term whose value is a computation. `muts`:
/// indices of the `let mut` variables of the current function.
fn m_tr(t : Tm, vars : Bool, muts : Array[Int32]) -> Tm {
  if is_direct(t, vars, 0) {
    return pure_tm(lower(t, vars))
  }
  match t {
    App(App(Global("%mcall"), row, _), c, _) =>
      if row_is_ctl(row, vars) && muts.length() > 0 {
        // a bind, so that the `let mut` variables are saved here too
        bind_tm(
          call_tr(c, vars, muts),
          Lam("v", Expl, true, pure_tm(Var(0))),
          muts,
        )
      } else if row_is_ctl(row, vars) {
        call_tr(c, vars, muts)
      } else {
        m_tr(c, vars, muts)
      }
    App(App(App(Global("%handle"), marker, _), dispatch, _), body, _) =>
      handle_tm(marker, dispatch, body, vars)
    Let(x, a, v, b) =>
      if is_direct(v, vars, 0) {
        Let(x, a, lower(v, vars), m_tr(b, vars, shift_muts(muts, 1)))
      } else {
        bind_tm(
          m_tr(v, vars, muts),
          Lam(x, Expl, true, m_tr(b, vars, shift_muts(muts, 1))),
          muts,
        )
      }
    LetMut(x, a, v, b) =>
      if is_direct(v, vars, 0) {
        LetMut(x, a, lower(v, vars), m_tr(b, vars, [0, ..shift_muts(muts, 1)]))
      } else {
        // under the value's binder `v`: `let mut x = v`
        let b2 = shift_tm(b, 1, 1)
        bind_tm(
          m_tr(v, vars, muts),
          Lam(
            "v",
            Expl,
            true,
            LetMut(
              x,
              shift_tm(a, 1, 0),
              Var(0),
              m_tr(b2, vars, [0, ..shift_muts(muts, 2)]),
            ),
          ),
          muts,
        )
      }
    Seq(a, b) =>
      if is_direct(a, vars, 0) {
        Seq(lower(a, vars), m_tr(b, vars, muts))
      } else {
        bind_tm(
          m_tr(a, vars, muts),
          Lam(
            "_",
            Expl,
            true,
            m_tr(shift_tm(b, 1, 0), vars, shift_muts(muts, 1)),
          ),
          muts,
        )
      }
    Assign(ix, v) =>
      bind_tm(
        m_tr(v, vars, muts),
        Lam("v", Expl, true, Seq(Assign(ix + 1, Var(0)), pure_tm(Lit(LUnit)))),
        muts,
      )
    Return(v) =>
      bind_tm(
        m_tr(v, vars, muts),
        Lam("v", Expl, true, comp("Ret", [Var(0)])),
        muts,
      )
    Break => comp("Brk", [])
    Continue => comp("Cont", [])
    While(c, b, s) => {
      let thunk = (x : Tm) => {
        Lam("_", Expl, true, m_tr(shift_tm(x, 1, 0), vars, shift_muts(muts, 1)))
      }
      App(
        App(App(Global("%eff_while"), thunk(c), Expl), thunk(b), Expl),
        thunk(s),
        Expl,
      )
    }
    Match(ss, cls) =>
      seq_tr(ss, vars, muts, (vs, d) => {
        let cls2 = cls.map(cl => {
          let k = pats_slots(cl.pats)
          match cl.cond {
            Some(g) if !is_direct(g, vars, 0) =>
              ctl_error.val = Some("a guard cannot perform `ctl` operations")
            _ => ()
          }
          {
            pats: cl.pats,
            cond: cl.cond.map(g => lower(shift_tm(g, d, k), vars)),
            body: m_tr(shift_tm(cl.body, d, k), vars, shift_muts(muts, d + k)),
          }
        })
        Match(vs, cls2)
      })
    App(_, _, _) => {
      let (h, args) = flatten_app(t)
      seq_tr([h, ..args.map(a => a.0)], vars, muts, (vs, _) => {
        let mut r = vs[0]
        for k = 0; k < args.length(); k = k + 1 {
          r = App(r, vs[k + 1], args[k].1)
        }
        pure_tm(r)
      })
    }
    Raise(v) =>
      bind_tm(m_tr(v, vars, muts), Lam("v", Expl, true, Raise(Var(0))), muts)
    Try(_, _) | Defer(_, _) => {
      ctl_error.val = Some(
        "`try` and `defer` around code that performs `ctl` operations are not supported yet",
      )
      pure_tm(lower(t, vars))
    }
    _ => pure_tm(lower(t, vars))
  }
}

///|
/// A call that returns a computation: its arguments are evaluated first; a
/// function with an effect variable is replaced by its translated version.
fn call_tr(c : Tm, vars : Bool, muts : Array[Int32]) -> Tm {
  let (h, args) = flatten_app(c)
  let h2 = match h {
    Global(n) if global_row_has_var(n) => Global(ensure_m(n))
    _ => h
  }
  seq_tr([h2, ..args.map(a => a.0)], vars, muts, (vs, _) => {
    let mut r = vs[0]
    for k = 0; k < args.length(); k = k + 1 {
      r = App(r, vs[k + 1], args[k].1)
    }
    r
  })
}

///|
/// Evaluate `parts` from left to right, then `build` from their values
/// (terms valid under `d` new binders, given as the second argument).
/// Direct parts stay in place when no later part needs a bind.
fn seq_tr(
  parts : Array[Tm],
  vars : Bool,
  muts : Array[Int32],
  build : (Array[Tm], Int32) -> Tm,
) -> Tm {
  // the last part that is not direct
  let mut last = -1
  for k = 0; k < parts.length(); k = k + 1 {
    if !is_direct(parts[k], vars, 0) {
      last = k
    }
  }
  if last < 0 {
    return build(parts.map(p => lower(p, vars)), 0)
  }
  // parts 0..=last are bound in order; the others stay in place
  seq_go(parts, vars, muts, 0, last + 1, build)
}

///|
fn seq_go(
  parts : Array[Tm],
  vars : Bool,
  muts : Array[Int32],
  k : Int32,
  n : Int32,
  build : (Array[Tm], Int32) -> Tm,
) -> Tm {
  if k == n {
    // parts 0..n-1 are the variables n-1 .. 0; the rest are shifted
    let vs : Array[Tm] = []
    for j = 0; j < parts.length(); j = j + 1 {
      if j < n {
        vs.push(Var(n - 1 - j))
      } else {
        vs.push(lower(shift_tm(parts[j], n, 0), vars))
      }
    }
    return build(vs, n)
  }
  let p = shift_tm(parts[k], k, 0)
  let m = shift_muts(muts, k)
  let rest = seq_go(parts, vars, muts, k + 1, n, build)
  if is_direct(p, vars, 0) {
    Let("p", any_ty(), lower(p, vars), rest)
  } else {
    bind_tm(m_tr(p, vars, m), Lam("p", Expl, true, rest), m)
  }
}

///|
/// Does `t` have a `return` (`ret`), or a `break`/`continue` out of `t`
/// (`in_loop`: under a loop of `t`)?
fn has_jump(t : Tm, ret : Bool, in_loop : Bool) -> Bool {
  let go = (x : Tm) => has_jump(x, ret, in_loop)
  match t {
    Return(_) if ret => true
    Break | Continue => !ret && !in_loop
    While(a, b, s) => go(a) || has_jump(b, ret, true) || has_jump(s, ret, true)
    Lam(_, _, _, b) => go(b)
    App(f, a, _) => go(f) || go(a)
    Let(_, _, v, b) | LetMut(_, _, v, b) => go(v) || go(b)
    Match(ss, cls) | Try(Match(ss, _), cls) =>
      ss.iter().any(go) || cls.iter().any(c => go(c.body))
    Try(b, cls) => go(b) || cls.iter().any(c => go(c.body))
    Seq(a, b) | Defer(a, b) => go(a) || go(b)
    Assign(_, v) | Raise(v) | Return(v) => go(v)
    ArrayLit(es) => es.iter().any(go)
    _ => false
  }
}
