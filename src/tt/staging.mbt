///|
/// Staged metaprogramming (doc/mbtpp/staging.md).
///
/// `code { e }` is the code of `e`, of type `Code[T]`; `${ c }` splices the
/// code `c` where it stands. Code is a function waiting to be run:
/// `code { e }` is `%quote(s, env => e)`, where `s` holds the code of the
/// splices of `e` (made when `code { e }` is evaluated, see `hoist_splices`)
/// and `e` takes them from `env`; `${ c }` is `%splice(c, line, col)` and
/// `c.run()` is `%run(c)`, both running the code. So a program means what
/// it means without the staging annotations, and that is how the checker
/// computes with it (`${ code { e } }` is `e`).
///
/// Stages make sure the splices of a definition can run before the program
/// does: `code { }` raises the stage, `${ }` lowers it, and a variable cannot
/// be used at a stage lower than the one it is bound at (its value is not
/// known yet). A splice at stage 0, in the body of a definition, is then
/// closed code: it is run when the program is checked and replaced by the
/// code it makes (`unstage_all`), so that the interpreter and the compiler
/// only see ordinary terms there. The other splices and `run` run code at
/// run time.

///|
/// Was `code { }` or `${ }` used since the last expansion?
let staging_used : Ref[Bool] = Ref::new(false)

///|
/// The stage at which a lifted local function (localfn.mbt) was defined,
/// when it is not 0.
let lifted_stages : Map[String, Int32] = Map([])

///|
/// During the expansion of splices every function is unfolded: `#opaque` is
/// about type checking, not about running (see unfolding.mbt).
let unfold_everything : Ref[Bool] = Ref::new(false)

///|
/// What the splices print while they run (`print` and `println` in a
/// generator), in order.
pub let staging_output : Array[String] = []

///|
/// Are the messages of splices also printed when they are made?
pub let staging_echo : Ref[Bool] = Ref::new(true)

///|
fn reset_staging() -> Unit {
  reset_ffi()
  staging_output.clear()
  staging_used.val = false
  lifted_stages.clear()
  unfold_everything.val = false
  specialized.clear()
  specializing.val = None
  specialized_count.val = 0
}

///|
/// The primitives that a splice runs for real when it is applied to all its
/// arguments (`spliced` code runs when the program is checked, with the
/// state it makes): arrays, which are mutable values there, and `print`.
/// `None` if the primitive is not one of them or an argument is not known.
fn run_prim(p : String, sp : Spine) -> Val? {
  let args : Array[Val] = []
  for a in sp {
    if a.1 == Expl {
      args.push(a.0)
    }
  }
  let arr = (k : Int32) => {
    match force(args[k]) {
      VArrLit(xs) => Some(xs)
      _ => None
    }
  }
  let int = (k : Int32) => {
    match force(args[k]) {
      VLit(LInt(i)) => Some(i)
      _ => None
    }
  }
  match (p, args.length()) {
    ("%array_new", _) => Some(VArrLit([]))
    ("%array_make", 2) =>
      match int(0) {
        Some(n) if n >= 0 => Some(VArrLit(Array::make(n, args[1])))
        _ => None
      }
    ("%array_length", 1) =>
      match arr(0) {
        Some(xs) => Some(VLit(LInt(xs.length())))
        None => None
      }
    ("%array_get", 2) =>
      match (arr(0), int(1)) {
        (Some(xs), Some(i)) if i >= 0 && i < xs.length() => Some(xs[i])
        _ => None
      }
    ("%array_set", 3) =>
      match (arr(0), int(1)) {
        (Some(xs), Some(i)) if i >= 0 && i < xs.length() => {
          xs[i] = args[2]
          Some(VLit(LUnit))
        }
        _ => None
      }
    ("%array_push", 2) =>
      match arr(0) {
        Some(xs) => {
          xs.push(args[1])
          Some(VLit(LUnit))
        }
        None => None
      }
    ("%print", 1) =>
      match force(args[0]) {
        VLit(LStr(s)) => {
          staging_output.push(s)
          if staging_echo.val {
            // (`println` adds the newline that `println(x)` of MoonBit++ wrote)
            println(
              if s.has_suffix("\n") {
                s.unsafe_substring(start=0, end=s.length() - 1)
              } else {
                s
              },
            )
          }
          Some(VLit(LUnit))
        }
        _ => None
      }
    _ => None
  }
}

///|
/// The type `Code[T]` and the primitives of quotation.
fn setup_staging() -> Unit {
  let code = (a : Tm) => App(Global("Code"), a, Impl)
  builtin_data("Code", Pi("T", Impl, false, U, U), 1, false)
  // [A](s : Unit, f : (Unit) -> A) -> Code[A] (`s` is `()` until the
  // splices are hoisted)
  register(
    "%quote",
    Pi(
      "A",
      Impl,
      false,
      U,
      Pi(
        "s",
        Expl,
        true,
        Global("Unit"),
        Pi(
          "f",
          Expl,
          false,
          Pi("_", Expl, true, Global("Unit"), Var(2)),
          code(Var(2)),
        ),
      ),
    ),
    GPrim("%quote", 3),
  )
  // [A](c : Code[A], line : Int, col : Int) -> A
  register(
    "%splice",
    Pi(
      "A",
      Impl,
      false,
      U,
      Pi(
        "c",
        Expl,
        true,
        code(Var(0)),
        Pi(
          "line",
          Expl,
          false,
          Global("Int"),
          Pi("col", Expl, false, Global("Int"), Var(3)),
        ),
      ),
    ),
    GPrim("%splice", 4),
  )
}

///|
/// Is the global `n` a primitive that runs code (`${ }` or `run`)?
fn is_splice_prim(n : String) -> Bool {
  globals.get(n) is Some({ kind: GPrim("%splice" | "%run", _), .. })
}

///|
/// `code { e }` as a term: the type of `e`, its splices and its body.
fn quote_parts(t : Tm) -> (Tm, Tm, Tm)? {
  match t {
    App(App(App(Global("%quote"), a, Impl), s, Expl), f, Expl) =>
      Some((a, s, f))
    _ => None
  }
}

///|
fn quote_tm(a : Tm, s : Tm, f : Tm) -> Tm {
  apps(Global("%quote"), [(a, Impl), (s, Expl), (f, Expl)])
}

///|
/// The body of the code `%quote(s, f)` (under the parameter of `f`) as it
/// is written, with its splices in place (the inverse of `hoist`), to show
/// it.
fn quoted_body(s : Tm, f : Tm) -> Tm {
  let cs : Array[Tm] = []
  let mut cur = s
  while cur is Let(_, _, c, rest) {
    // without the earlier `let`s
    cs.push(shift_tm(c, -cs.length(), 0))
    cur = rest
  }
  match f {
    Lam(_, _, _, body) =>
      if cs.length() == 0 {
        body
      } else {
        unhoist(body, 1, cs)
      }
    _ => f
  }
}

///|
fn unhoist(t : Tm, b : Int32, cs : Array[Tm]) -> Tm {
  let under = (x : Tm, k : Int32) => unhoist(x, b + k, cs)
  let clause = (cl : Clause) => {
    let k = pats_slots(cl.pats)
    cl.map(x => under(x, k))
  }
  match t {
    App(Var(ix), Lit(LInt(j)), Expl) if ix == b - 1 && j >= 0 && j < cs.length() =>
      shift_tm(cs[j], b, 0)
    Lam(x, i, g, body) => Lam(x, i, g, under(body, 1))
    Pi(x, i, g, a, body) => Pi(x, i, g, under(a, 0), under(body, 1))
    Let(x, a, v, body) => Let(x, under(a, 0), under(v, 0), under(body, 1))
    LetMut(x, a, v, body) => LetMut(x, under(a, 0), under(v, 0), under(body, 1))
    Match(ss, cls) => Match(ss.map(x => under(x, 0)), cls.map(clause))
    Try(body, cls) => Try(under(body, 0), cls.map(clause))
    _ => tm_map(t, x => under(x, 0))
  }
}

// ---------------------------------------------------------------------------
// Stages

///|
/// The context of code `d` stages later.
fn Cxt::shift_stage(self : Cxt, d : Int32) -> Cxt {
  let stage = self.stage + d
  { ..self, stage, stage_marks: push1(self.stage_marks, (self.lvl, stage)), }
}

///|
/// The stage at which the variable of level `l` is bound.
fn Cxt::var_stage(self : Cxt, l : Int32) -> Int32 {
  let mut s = 0
  for m in self.stage_marks {
    if m.0 <= l {
      s = m.1
    }
  }
  s
}

///|
/// Types and proofs are erased: they may be used at any stage.
fn stage_free(cxt : Cxt, ty : Val) -> Bool {
  let mut t = force(ty)
  let mut lvl = cxt.lvl
  while t is VPi(_, _, _, _, cl) {
    t = force(inst(cl, v_var(lvl)))
    lvl = lvl + 1
  }
  t is (VU | VProp) || is_prop_type(cxt.ltypes(), ty)
}

///|
/// The variable `x` (of level `l`) is used here: is its value known at this
/// stage?
fn check_stage(cxt : Cxt, x : String, l : Int32) -> Unit raise ElabError {
  if cxt.stage_marks.length() == 0 {
    return
  }
  let bound = cxt.var_stage(l)
  if bound == cxt.stage {
    return
  }
  let at = " (it is bound at stage " +
    bound.to_string() +
    " and used at stage " +
    cxt.stage.to_string() +
    ")"
  // a `let mut` variable is shared, not copied: generated code could not
  // assign the variable of its generator, nor see its later values
  if cxt.muts[l] {
    cxt.fail(
      "the mutable variable " +
      x +
      " cannot be used across `code { }` or `" +
      dollar +
      "{ }`" +
      at +
      "; copy it first: let " +
      x +
      "0 = " +
      x,
    )
  }
  if bound > cxt.stage && !cxt.in_type && !stage_free(cxt, cxt.types[l]) {
    cxt.fail(
      x +
      " is not known when this splice runs: it is a variable of the generated code" +
      at +
      ". Use it inside `code { }`",
    )
  }
}

// ---------------------------------------------------------------------------
// Elaboration

///|
/// `code { e }`, given as the thunk `() => e`: the thunk is checked one
/// stage later.
fn elab_quote(
  cxt : Cxt,
  lam : @parser.Expr,
  expected : Val?,
) -> (Tm, Val) raise ElabError {
  staging_used.val = true
  let qc = { ..cxt.shift_stage(1), quote_cxt: Some(cxt), }
  let known = match expected {
    Some(e) =>
      match force(e) {
        VData("Code", [(a, _)]) if !(force(a) is VFlex(_, _)) => Some(a)
        _ => None
      }
    None => None
  }
  let (t, a) = match known {
    Some(a) => {
      let lty = VPi("_", Expl, true, VData("Unit", []), {
        env: [a],
        body: Var(1),
      })
      (check(qc, lam, lty), a)
    }
    // the type and the effects of the code are those of the thunk
    None => {
      let (t, lty) = infer(qc, lam)
      match force(lty) {
        VPi(_, Expl, _, _, cl) => (t, inst(cl, VLit(LUnit)))
        _ => cxt.fail("internal error: the type of quoted code")
      }
    }
  }
  (quote_tm(cxt.quote(a), Lit(LUnit), t), VData("Code", [(a, Impl)]))
}

///|
/// Does the splice `x`, in the code written in the context `g`, only use
/// what `g` has? Then it runs when the code is made, where the code is
/// written. (Not if a variable of `g` was refined since by a match.)
fn runs_with_quote(cxt : Cxt, g : Cxt, x : @parser.Expr) -> Bool {
  for l = g.lvl; l < cxt.lvl; l = l + 1 {
    if mentions(x, cxt.names[l]) {
      return false
    }
  }
  for l = 0; l < g.lvl; l = l + 1 {
    if cxt.bound[l] != g.bound[l] {
      return false
    }
  }
  true
}

///|
/// The context of a splice that runs when the code it is in does, or when
/// the program is checked: one stage earlier, without effects.
fn pure_splice_cxt(cxt : Cxt, outer : Cxt?) -> Cxt {
  let note = if cxt.quote_cxt is Some(_) {
    "\nhint: this splice uses variables of the code it is in, so it runs when that code does: it cannot raise errors or perform effects"
  } else {
    "\nhint: a splice in a definition runs when the program is checked: it cannot raise errors or perform effects"
  }
  {
    ..cxt.shift_stage(-1),
    splice_note: note,
    can_raise: false,
    can_async: false,
    ret_ty: None,
    in_loop: false,
    eff_row: row_nil(),
    handled: [],
    arm_lams: false,
    in_fun_arm: false,
    quote_cxt: outer,
  }
}

///|
/// `${ x }` at `p`: `x` is checked one stage earlier; the splice runs the
/// code (it has its effects). In `code { }`, a splice that does not use the
/// variables of the code is part of what makes the code: it is checked
/// where the code is written, with the effects allowed there. The other
/// splices have no effects.
fn elab_splice(
  cxt : Cxt,
  p : Pos,
  x : @parser.Expr,
) -> (Tm, Val) raise ElabError {
  staging_used.val = true
  let (t, ty) = match cxt.quote_cxt {
    Some(g) if runs_with_quote(cxt, g, x) => {
      let (t, ty) = infer_ins(g.at(p), x)
      (shift_tm(t, cxt.lvl - g.lvl, 0), ty)
    }
    Some(g) => infer_ins(pure_splice_cxt(cxt, g.quote_cxt), x)
    None => infer_ins(pure_splice_cxt(cxt, None), x)
  }
  match force(ty) {
    VData("Code", _) | VFlex(_, _) => ()
    _ =>
      cxt.fail(
        "`" +
        dollar +
        "{ }` splices code (a value of type Code[T]), but this has type " +
        cxt.show(ty),
      )
  }
  let int = VData("Int", [])
  app_core(
    cxt,
    Global("%splice"),
    globals.get("%splice").unwrap().vty,
    0,
    None,
    Some([AV(t, ty), AV(Lit(LInt(p.line)), int), AV(Lit(LInt(p.col)), int)]),
  )
}

// ---------------------------------------------------------------------------
// Evaluation

///|
/// The number of arguments of the global `n` if it runs code (`${ }` or
/// `run`).
fn splice_arity(n : String) -> Int32? {
  match globals.get(n) {
    Some({ kind: GPrim("%splice" | "%run", arity), .. }) => Some(arity)
    _ => None
  }
}

///|
/// `${ c }` or `c.run()` on the spine `sp` (the primitive takes `arity`
/// arguments): the body of the code `c` when it is known, applied to the
/// rest of the spine; `None` while `c` is not known. With `delay`, `c` is
/// not computed.
fn splice_val(sp : Spine, arity : Int32, delay : Bool) -> Val? {
  let c = if delay { force_meta(sp[1].0) } else { force(sp[1].0) }
  match c {
    VPrim("%quote", [_, (s, _), (f, _)]) =>
      Some(app_spine(app_val(f, s, Expl), sp[arity:].to_array()))
    VPrim("%raise", [_, ..]) => Some(c)
    _ => None
  }
}

///|
/// The code that a blocked `${ c }` or `c.run()` runs (positions are not part
/// of it).
fn spliced_code(v : Val) -> Val? {
  match v {
    VPrim(n, sp) if splice_arity(n) is Some(arity) && sp.length() == arity =>
      Some(sp[1].0)
    _ => None
  }
}

///|
/// Does a blocked `${ c }` or `c.run()` run code that may raise?
fn splice_may_raise(n : String, sp : Spine) -> Bool {
  sp.length() >= 2 && is_splice_prim(n) && force_meta(sp[0].0) is VRaises(_, _)
}

///|
/// Does the code `%quote(s, f)` hold a value with effects? Only the
/// variables it uses count, and its body does not: it is not run by what
/// makes the code.
fn quoted_effect(s : Val, f : Val) -> Bool {
  let part = (v : Val) => {
    match v {
      VLam(_, _, _, cl) => {
        let n = cl.env.length()
        for i = 0; i < n; i = i + 1 {
          // under the parameter of the function
          if var_exists(cl.body, 1, ix => ix == n - 1 - i) &&
            has_effect(cl.env[i], false) {
            return true
          }
        }
        false
      }
      _ => has_effect(v, false)
    }
  }
  part(s) || part(f)
}

///|
/// Does a free variable of `t` satisfy `p`? `d` binders are crossed: `p`
/// gets the index outside of them. (A negative index, of a variable out of
/// scope, always counts.)
fn var_exists(t : Tm, d : Int32, p : (Int32) -> Bool) -> Bool {
  let go = (x : Tm) => var_exists(x, d, p)
  let under = (x : Tm, k : Int32) => var_exists(x, d + k, p)
  let clause = (cl : Clause) => {
    let k = pats_slots(cl.pats)
    cl.cond.map(c => under(c, k)).unwrap_or(false) || under(cl.body, k)
  }
  match t {
    Var(ix) => ix < 0 || (ix >= d && p(ix - d))
    Assign(ix, v) => ix < 0 || (ix >= d && p(ix - d)) || go(v)
    Lam(_, _, _, b) => under(b, 1)
    Pi(_, _, _, a, b) => go(a) || under(b, 1)
    Let(_, a, v, b) | LetMut(_, a, v, b) => go(a) || go(v) || under(b, 1)
    App(f, a, _) | Raises(f, a) | Seq(f, a) | Defer(f, a) => go(f) || go(a)
    Match(ss, cls) => ss.iter().any(go) || cls.iter().any(clause)
    Try(b, cls) => go(b) || cls.iter().any(clause)
    While(c, b, s) => go(c) || go(b) || go(s)
    Return(v) | Raise(v) => go(v)
    ArrayLit(es) => es.iter().any(go)
    Global(_)
    | Meta(_)
    | InsertedMeta(_, _)
    | U
    | PropU
    | Lit(_)
    | Break
    | Continue => false
  }
}

// ---------------------------------------------------------------------------
// The splices of code are run when the code is made

///|
/// Apply `f` to the subterms of `t`.
fn tm_map(t : Tm, f : (Tm) -> Tm) -> Tm {
  match t {
    Lam(x, i, g, b) => Lam(x, i, g, f(b))
    App(a, b, i) => App(f(a), f(b), i)
    Pi(x, i, g, a, b) => Pi(x, i, g, f(a), f(b))
    Let(x, a, v, b) => Let(x, f(a), f(v), f(b))
    LetMut(x, a, v, b) => LetMut(x, f(a), f(v), f(b))
    Match(ss, cls) => Match(ss.map(f), cls.map(cl => cl.map(f)))
    Try(b, cls) => Try(f(b), cls.map(cl => cl.map(f)))
    Raises(a, e) => Raises(f(a), f(e))
    Assign(ix, v) => Assign(ix, f(v))
    While(c, b, s) => While(f(c), f(b), f(s))
    Return(v) => Return(f(v))
    Raise(v) => Raise(f(v))
    ArrayLit(es) => ArrayLit(es.map(f))
    Seq(a, b) => Seq(f(a), f(b))
    Defer(a, b) => Defer(f(a), f(b))
    Var(_)
    | Global(_)
    | Meta(_)
    | InsertedMeta(_, _)
    | U
    | PropU
    | Lit(_)
    | Break
    | Continue => t
  }
}

///|
/// In the (zonked) body of a definition, the splices of each `code { e }`
/// that do not depend on the variables of `e` are evaluated when the code is
/// made, as in MetaOCaml: `code { … ${a} … ${b} … }` becomes
///
///   %quote({ let s0 = a; let s1 = b; j => match j { 0 => s0; 1 => s1 } },
///          env => … ${env(0)} … ${env(1)} …)
///
/// so that the effects of `a` and `b` are those of what makes the code, and
/// what they compute is computed once. The other splices are pure (see
/// `elab_splice`), and run with the code.
fn hoist_splices(t : Tm) -> Tm {
  let quote : Map[String, Bool] = { "%quote": true }
  if tm_mentions_any(t, quote) {
    hoist(t)
  } else {
    t
  }
}

///|
fn hoist(t : Tm) -> Tm {
  let t = tm_map(t, hoist)
  match t {
    App(
      App(App(Global("%quote"), a, Impl), Lit(LUnit), Expl),
      Lam(x, i, g, body),
      Expl
    ) => {
      let found : Array[(Tm, Tm)] = []
      let body2 = hoist_from(body, 1, 0, found)
      let k = found.length()
      if k == 0 {
        return t
      }
      // under s0 … s(k-1), j and the slot of the pattern
      let sel = if k == 1 {
        Var(1)
      } else {
        Match(
          [Var(0)],
          Array::makei(k, j => {
            pats: [CPLit(LInt(j))],
            cond: None,
            body: Var(k + 1 - j),
          }),
        )
      }
      let mut s = Lam("j", Expl, true, sel)
      for j = k - 1; j >= 0; j = j - 1 {
        let (ty, c) = found[j]
        s = Let(
          "s" + j.to_string(),
          App(Global("Code"), shift_tm(ty, j, 0), Impl),
          shift_tm(c, j, 0),
          s,
        )
      }
      quote_tm(a, s, Lam(x, i, g, body2))
    }
    _ => t
  }
}

///|
/// The body `t` of some code, `b` binders and `depth` nested `code { }`
/// below its start, without its splices that are closed there: their type
/// and code are added to `found`, and each is replaced by the splice of an
/// item of the first variable of the body.
fn hoist_from(t : Tm, b : Int32, depth : Int32, found : Array[(Tm, Tm)]) -> Tm {
  let go = (x : Tm) => hoist_from(x, b, depth, found)
  let under = (x : Tm, k : Int32) => hoist_from(x, b + k, depth, found)
  let clause = (cl : Clause) => {
    let k = pats_slots(cl.pats)
    cl.map(x => under(x, k))
  }
  let closed = (x : Tm) => !var_exists(x, 0, ix => ix < b)
  match t {
    App(_, _, _) => {
      let (h, args) = flatten_app(t)
      // implicit arguments are erased: their splices are not run
      let rest = (k : Int32) => {
        args[k:]
        .to_array()
        .map(a => if a.1 == Impl { a } else { (go(a.0), a.1) })
      }
      match h {
        Global("%quote") if args.length() >= 3 =>
          apps(
            h,
            [
              args[0],
              (go(args[1].0), Expl),
              (hoist_from(args[2].0, b, depth + 1, found), Expl),
              ..rest(3),
            ],
          )
        Global("%splice") if args.length() >= 4 =>
          if depth > 0 {
            apps(
              h,
              [
                args[0],
                (hoist_from(args[1].0, b, depth - 1, found), Expl),
                args[2],
                args[3],
                ..rest(4),
              ],
            )
          } else if closed(args[0].0) && closed(args[1].0) {
            let j = found.length()
            found.push((shift_tm(args[0].0, -b, 0), shift_tm(args[1].0, -b, 0)))
            apps(
              h,
              [
                args[0],
                (App(Var(b - 1), Lit(LInt(j)), Expl), Expl),
                args[2],
                args[3],
                ..rest(4),
              ],
            )
          } else {
            // (what it runs is not code of this stage)
            apps(h, [args[0], args[1], args[2], args[3], ..rest(4)])
          }
        _ => apps(go(h), rest(0))
      }
    }
    Lam(x, i, g, body) => Lam(x, i, g, under(body, 1))
    // (types are erased too)
    Pi(_, _, _, _, _) | Raises(_, _) => t
    Let(x, a, v, body) => Let(x, a, go(v), under(body, 1))
    LetMut(x, a, v, body) => LetMut(x, a, go(v), under(body, 1))
    Match(ss, cls) => Match(ss.map(go), cls.map(clause))
    Try(body, cls) => Try(go(body), cls.map(clause))
    _ => tm_map(t, go)
  }
}

// ---------------------------------------------------------------------------
// Expansion of the splices of stage 0

///|
/// The global whose splices are being expanded.
let unstage_owner : Ref[String] = Ref::new("")

///|
/// A depth at which no splice is expanded (in a value kept for run time).
let no_expand : Int32 = 1000000

///|
fn[T] unstage_fail(pos : Pos?, msg : String) -> T raise ElabError {
  let p = match pos {
    Some(p) => p
    None => decl_pos.get(unstage_owner.val).unwrap_or({ line: 0, col: 0, })
  }
  raise ElabError(p, msg)
}

///|
/// The names of the slots of a pattern.
fn slot_names(p : CPat, out : Array[String]) -> Unit {
  match p {
    CPVar(x) => out.push(x)
    CPWild | CPLit(_) => out.push("_")
    CPCon(_, ps) => {
      out.push("_")
      for q in ps {
        slot_names(q, out)
      }
    }
  }
}

///|
/// Does `t` return from the function it is in?
fn has_return(t : Tm) -> Bool {
  let clause = (cl : Clause) => {
    cl.cond.map(has_return).unwrap_or(false) || has_return(cl.body)
  }
  match t {
    Return(_) => true
    App(f, a, _) | Seq(f, a) | Defer(f, a) => has_return(f) || has_return(a)
    Let(_, _, v, b) | LetMut(_, _, v, b) => has_return(v) || has_return(b)
    Match(ss, cls) => ss.iter().any(has_return) || cls.iter().any(clause)
    Try(b, cls) => has_return(b) || cls.iter().any(clause)
    Assign(_, v) | Raise(v) => has_return(v)
    While(c, b, s) => has_return(c) || has_return(b) || has_return(s)
    ArrayLit(es) => es.iter().any(has_return)
    _ => false
  }
}

///|
/// The variables in scope in generated code: their names, and their types
/// when they are known (those of parameters and `let`s).
priv struct Scope {
  names : Array[String]
  types : Array[Val?]
}

///|
fn Scope::length(self : Scope) -> Int32 {
  self.names.length()
}

///|
fn Scope::bind_all(self : Scope, xs : Array[String]) -> Scope {
  {
    names: concat(self.names, xs),
    types: concat(self.types, xs.map(_ => None)),
  }
}

///|
fn Scope::bind_typed(self : Scope, x : String, ty : Val) -> Scope {
  { names: push1(self.names, x), types: push1(self.types, Some(ty)), }
}

///|
/// `t` (in the environment `env`) as a term in the scope `names`, with its
/// splices of depth 0 expanded: the variables of `t` are replaced by their
/// values, and the rest is kept as it is written (nothing is computed in
/// code that is not run now). `code { }` raises the depth, `${ }` lowers it.
fn expand(
  names : Scope,
  env : Env,
  depth : Int32,
  t : Tm,
) -> Tm raise ElabError {
  let lvl = names.length()
  let go = (x : Tm) => expand(names, env, depth, x)
  // types and implicit arguments are erased: their splices are not run
  let erased = (x : Tm) => expand(names, env, no_expand, x)
  let under = (xs : Array[String], x : Tm) => {
    expand(
      names.bind_all(xs),
      concat(env, fresh_vars(lvl, xs.length())),
      depth,
      x,
    )
  }
  // under a variable whose type is known
  let under_typed = (x : String, ty : Tm, b : Tm) => {
    expand(
      names.bind_typed(x, eval(env, ty)),
      env_push(env, v_var(lvl)),
      depth,
      b,
    )
  }
  let clause = (cl : Clause) => {
    let xs : Array[String] = []
    for p in cl.pats {
      slot_names(p, xs)
    }
    let cond = match cl.cond {
      Some(c) => Some(under(xs, c))
      None => None
    }
    ({ pats: cl.pats, cond, body: under(xs, cl.body), } : Clause)
  }
  match t {
    Var(ix) => reify(names, env[env.length() - 1 - ix])
    Meta(_) | InsertedMeta(_, _) => quote(lvl, eval(env, t))
    Global(_) | Lit(_) | U | PropU | Break | Continue => t
    Lam(x, i, g, b) => Lam(x, i, g, under([x], b))
    Pi(_, _, _, _, _) | Raises(_, _) if depth != no_expand => erased(t)
    Pi(x, i, g, a, b) => Pi(x, i, g, go(a), under([x], b))
    Let(x, a, v, b) => Let(x, erased(a), go(v), under_typed(x, a, b))
    LetMut(x, a, v, b) => LetMut(x, erased(a), go(v), under_typed(x, a, b))
    App(_, _, _) => {
      let (h, args) = flatten_app(t)
      let rest = (k : Int32) => {
        args[k:]
        .to_array()
        .map(a => if a.1 == Impl { (erased(a.0), a.1) } else { (go(a.0), a.1) })
      }
      match h {
        Global("%quote") if args.length() >= 3 =>
          apps(
            Global("%quote"),
            [
              (erased(args[0].0), Impl),
              (go(args[1].0), Expl),
              (expand(names, env, depth + 1, args[2].0), Expl),
              ..rest(3),
            ],
          )
        Global("%splice") if args.length() >= 4 =>
          if depth == 0 {
            let pos : Pos? = match (args[2].0, args[3].0) {
              (Lit(LInt(line)), Lit(LInt(col))) => Some({ line, col, })
              _ => None
            }
            apps(splice_code(names, env, args[1].0, pos), rest(4))
          } else {
            apps(
              Global("%splice"),
              [
                (erased(args[0].0), Impl),
                (expand(names, env, depth - 1, args[1].0), Expl),
                args[2],
                args[3],
                ..rest(4),
              ],
            )
          }
        // a local function of code that is being generated: the function
        // for what is known of its context
        Global(g) if depth == 0 &&
          local_fn_arity(g) is Some(n) &&
          args.length() >= n =>
          match
            specialize(
              names,
              g,
              n,
              args[0:n].to_array().map(a => eval(env, a.0)),
            ) {
            Some(f) => apps(f, rest(n))
            None => apps(h, rest(0))
          }
        _ => apps(go(h), rest(0))
      }
    }
    Match(ss, cls) => Match(ss.map(go), cls.map(clause))
    Try(b, cls) => Try(go(b), cls.map(clause))
    Raises(a, e) => Raises(go(a), go(e))
    Assign(ix, v) =>
      match force(env[env.length() - 1 - ix]) {
        VRigid(l, []) if l < lvl => Assign(lvl - 1 - l, go(v))
        _ =>
          unstage_fail(
            None,
            "generated code assigns a variable that is not one of its own",
          )
      }
    While(c, b, s) => While(go(c), go(b), go(s))
    Return(v) => Return(go(v))
    Raise(v) => Raise(go(v))
    ArrayLit(es) => ArrayLit(es.map(go))
    // (a splice of `code { () }` leaves nothing)
    Seq(a, b) =>
      match statement(go(a)) {
        Some(a2) => Seq(a2, go(b))
        None => go(b)
      }
    Defer(a, b) => Defer(go(a), go(b))
  }
}

///|
/// `t`, whose value is not used, without the `()` at its end; `None` if
/// nothing is left.
fn statement(t : Tm) -> Tm? {
  match t {
    Lit(LUnit) => None
    Seq(a, b) =>
      match statement(b) {
        Some(b2) => Some(Seq(a, b2))
        None => Some(a)
      }
    _ => Some(t)
  }
}

///|
/// The code that `c` makes, in place of `${ c }`.
fn splice_code(
  names : Scope,
  env : Env,
  c : Tm,
  pos : Pos?,
) -> Tm raise ElabError {
  let lvl = names.length()
  let v = force(eval(env, c))
  match v {
    VPrim("%quote", [_, (s, _), (f, _)]) =>
      match force(f) {
        // a `return` in the code leaves the code, not the function it is
        // spliced in: it is the body of a function, called
        VLam(_, _, _, cl) if has_return(cl.body) =>
          App(
            Lam(
              "_",
              Expl,
              true,
              expand(names.bind_all(["_"]), env_push(cl.env, s), 0, cl.body),
            ),
            Lit(LUnit),
            Expl,
          )
        VLam(_, _, _, cl) => expand(names, env_push(cl.env, s), 0, cl.body)
        _ => unstage_fail(pos, "internal error: the body of quoted code")
      }
    VPrim("%raise", [(e, _), ..]) =>
      unstage_fail(
        pos,
        "this splice raised an error when it was run: " +
        show_tm(names.names, quote(lvl, e)),
      )
    _ =>
      unstage_fail(
        pos,
        "this splice cannot be run when the program is checked: the code it makes is stuck on\n  " +
        show_tm(names.names, quote(lvl, v)) +
        (match ffi_error.val {
          Some(msg) => "\n" + msg
          None => ""
        }) +
        "\n(a generator can use arrays and `print`, but not variables of the generated code or, without moonpp, imported MoonBit functions; to run the code at run time instead, use .run())",
      )
  }
}

///|
/// The value `v`, known when a splice runs, as a term of the generated code
/// (in the scope `names`): variables of the generated code are themselves;
/// functions, code and blocked computations are kept as they are written.
fn reify(names : Scope, v : Val) -> Tm raise ElabError {
  let lvl = names.length()
  let sp_tm = (h : Tm, sp : Spine) => {
    apps(h, sp.map(a => (reify(names, a.0), a.1)))
  }
  // a large number is a literal again, not a tower of `S`
  match nat_val(v) {
    Some(k) if k > 64 => return nat_tm(k)
    _ => ()
  }
  let w = force(v)
  match w {
    VRigid(l, sp) =>
      if l < lvl {
        sp_tm(Var(lvl - 1 - l), sp)
      } else {
        unstage_fail(
          None,
          "generated code uses a variable outside of its scope",
        )
      }
    VGlobal(n, sp) | VData(n, sp) | VCon(n, sp) | VPrim(n, sp) =>
      sp_tm(Global(n), sp)
    VLit(l) => Lit(l)
    VLam(x, i, g, cl) =>
      Lam(
        x,
        i,
        g,
        expand(
          names.bind_all([x]),
          env_push(cl.env, v_var(lvl)),
          no_expand,
          cl.body,
        ),
      )
    VMatch(env, vs, cls, sp) => {
      let cls2 = cls.map(cl => {
        let xs : Array[String] = []
        for p in cl.pats {
          slot_names(p, xs)
        }
        let env2 = concat(env, fresh_vars(lvl, xs.length()))
        let names2 = names.bind_all(xs)
        let cond = match cl.cond {
          Some(c) => Some(expand(names2, env2, no_expand, c))
          None => None
        }
        (
          {
            pats: cl.pats,
            cond,
            body: expand(names2, env2, no_expand, cl.body),
          } : Clause)
      })
      sp_tm(Match(vs.map(x => reify(names, x)), cls2), sp)
    }
    VStuck(env, t, sp) => sp_tm(expand(names, env, no_expand, t), sp)
    VArrLit(vs) => ArrayLit(vs.map(x => reify(names, x)))
    // types
    VFlex(_, _) | VPi(_, _, _, _, _) | VU | VProp | VRaises(_, _) =>
      quote_full(lvl, w)
  }
}

///|
/// The number that a `Nat` value `S(…S(Z))` is (with the Prelude's `Nat`).
fn nat_val(v : Val) -> Int32? {
  if !prelude_nat.val {
    return None
  }
  let mut n = 0
  let mut cur = v
  while true {
    match force_meta(cur) {
      VGlobal("int_to_nat", [(a, _)]) =>
        match force(a) {
          VLit(LInt(k)) if k >= 0 => return Some(n + k)
          _ => return None
        }
      _ => ()
    }
    match force(cur) {
      VCon("Nat::Z", []) => return Some(n)
      VCon("Nat::S", [(x, _)]) => {
        n = n + 1
        cur = x
      }
      _ => return None
    }
  }
  None
}

// ---------------------------------------------------------------------------
// Local functions of generated code

///|
/// Apply `f` to the subterms of `t`, with the number of binders above them
/// (`d` above `t`).
fn tm_map_d(t : Tm, d : Int32, f : (Tm, Int32) -> Tm) -> Tm {
  let clause = (cl : Clause) => {
    let k = pats_slots(cl.pats)
    cl.map(x => f(x, d + k))
  }
  match t {
    Lam(x, i, g, b) => Lam(x, i, g, f(b, d + 1))
    Pi(x, i, g, a, b) => Pi(x, i, g, f(a, d), f(b, d + 1))
    Let(x, a, v, b) => Let(x, f(a, d), f(v, d), f(b, d + 1))
    LetMut(x, a, v, b) => LetMut(x, f(a, d), f(v, d), f(b, d + 1))
    Match(ss, cls) => Match(ss.map(x => f(x, d)), cls.map(clause))
    Try(b, cls) => Try(f(b, d), cls.map(clause))
    _ => tm_map(t, x => f(x, d))
  }
}

///|
/// Rename the free variables of `t` (under `d` binders): `r` maps their
/// indices outside of these binders.
fn map_free(t : Tm, d : Int32, r : (Int32) -> Int32) -> Tm {
  match t {
    Var(ix) => if ix >= d { Var(d + r(ix - d)) } else { t }
    Assign(ix, v) =>
      Assign(if ix >= d { d + r(ix - d) } else { ix }, map_free(v, d, r))
    _ => tm_map_d(t, d, (x, d2) => map_free(x, d2, r))
  }
}

///|
/// A local function of quoted code (lifted to the global `g`, which takes
/// the variables of its context first, see localfn.mbt) and the number of
/// these variables.
fn local_fn_arity(g : String) -> Int32? {
  match (lifted_stages.get(g), globals.get(g)) {
    (Some(stage), Some({ kind: GFunc(Some(_), _, n), .. })) if stage >= 1 =>
      Some(n)
    _ => None
  }
}

///|
/// The specializations made for the definition being expanded: the local
/// function, the values of its context, the new global and the variables
/// (levels) of the generated code it takes.
let specialized : Array[(String, Array[Val], String, Array[Int32])] = []

///|
/// The specialization being made: its recursive calls are `%spec` until the
/// variables it takes are known.
let specializing : Ref[(String, Array[Val])?] = Ref::new(None)

///|
let specialized_count : Ref[Int32] = Ref::new(0)

///|
fn same_values(lvl : Int32, vs : Array[Val], ws : Array[Val]) -> Bool {
  if vs.length() != ws.length() {
    return false
  }
  let ts : LTypes = Array::make(lvl, None)
  let snap = snapshot_metas()
  for k = 0; k < vs.length(); k = k + 1 {
    let same = try {
      unify(ts, vs[k], ws[k])
      true
    } catch {
      _ => false
    }
    if !same {
      restore_metas(snap)
      return false
    }
  }
  true
}

///|
/// The local function `g` of code that is being generated, for the values
/// `vals` of the `n` variables of its context: a new global function, whose
/// body is that of `g` with what is known replaced (its splices are
/// expanded), applied to the variables of the generated code it uses. As
/// the function is recursive, so is the new one. `None` inside another
/// specialization (the call of `g` is then kept: it runs its splices at run
/// time).
fn specialize(
  sc : Scope,
  g : String,
  n : Int32,
  vals : Array[Val],
) -> Tm? raise ElabError {
  let lvl = sc.length()
  let call = (name : String, levels : Array[Int32]) => {
    apps(Global(name), levels.map(l => (Var(lvl - 1 - l), Expl)))
  }
  for s in specialized {
    if s.0 == g && same_values(lvl, s.1, vals) {
      return Some(call(s.2, s.3))
    }
  }
  match specializing.val {
    Some((g2, vals2)) =>
      return if g2 == g && same_values(lvl, vals2, vals) {
        Some(Global("%spec"))
      } else {
        None
      }
    None => ()
  }
  let ge = globals.get(g).unwrap()
  let mut body = match ge.kind {
    GFunc(Some(b), _, _) => b
    _ => return None
  }
  let mut fty = ge.vty
  for k = 0; k < n; k = k + 1 {
    match (body, force(fty)) {
      (Lam(_, _, _, b), VPi(_, _, _, _, cl)) => {
        body = b
        fty = inst(cl, vals[k])
      }
      _ => return None
    }
  }
  specializing.val = Some((g, vals))
  let res : Result[Tm, ElabError] = Ok(expand(sc, vals, 0, body)) catch {
    ElabError(p, m) => Err(ElabError(p, m))
  }
  specializing.val = None
  let t = match res {
    Ok(t) => t
    Err(e) => raise e
  }
  let fty_tm = quote_full(lvl, fty)
  // the variables of the generated code that the function uses: its
  // parameters
  let used = Array::make(lvl, false)
  let note = (x : Tm) => {
    ignore(
      var_exists(x, 0, ix => {
        if ix < lvl {
          used[lvl - 1 - ix] = true
        }
        false
      }),
    )
  }
  note(t)
  note(fty_tm)
  let levels : Array[Int32] = []
  for l = 0; l < lvl; l = l + 1 {
    if used[l] {
      levels.push(l)
    }
  }
  let m = levels.length()
  let position = (l : Int32) => levels.search(l).unwrap_or(0)
  let rename = (x : Tm) => map_free(x, 0, ix => m - 1 - position(lvl - 1 - ix))
  specialized_count.val = specialized_count.val + 1
  let name = g + "$s" + specialized_count.val.to_string()
  // the recursive calls
  fn self_calls(x : Tm, d : Int32) -> Tm {
    match x {
      Global("%spec") =>
        apps(Global(name), levels.map(l => (Var(d + lvl - 1 - l), Expl)))
      _ => tm_map_d(x, d, self_calls)
    }
  }

  let mut ty = rename(fty_tm)
  let mut def = rename(self_calls(t, 0))
  for i = m - 1; i >= 0; i = i - 1 {
    let l = levels[i]
    // the type of a parameter, if it is known and only mentions the
    // parameters before it
    let pty = match sc.types[l] {
      Some(v) => {
        let a = quote_full(lvl, v)
        if var_exists(a, 0, ix => ix >= lvl || !used[lvl - 1 - ix]) {
          Global("%Any")
        } else {
          shift_tm(rename(a), i - m, 0)
        }
      }
      None => Global("%Any")
    }
    ty = Pi(sc.names[l], Expl, i == m - 1, pty, ty)
    def = Lam(sc.names[l], Expl, i == m - 1, def)
  }
  register(name, ty, GFunc(Some(def), contains_imperative(def), m))
  match global_files.get(g) {
    Some(f) => global_files.set(name, f)
    None => ()
  }
  specialized.push((g, vals, name, levels))
  Some(call(name, levels))
}

///|
/// Run the splices of stage 0 of every definition, and replace them by the
/// code they make.
fn unstage_all() -> Unit raise ElabError {
  if !staging_used.val {
    return
  }
  staging_used.val = false
  let splice : Map[String, Bool] = { "%splice": true }
  // the imported MoonBit functions the splices may call are made callable
  // by the host, if there is one (ffi.mbt)
  match ffi_host.val {
    Some(host) => {
      let imported = imported_functions_of_splices()
      if imported.length() > 0 {
        match (host.prepare)(imported) {
          Some(msg) =>
            raise ElabError(
              { line: 0, col: 0, },
              "cannot make the imported MoonBit functions of the splices callable: " +
              msg,
            )
          None => {
            (host.set_callback)(ffi_callback)
            for n in imported {
              ffi_ready.set(n, true)
            }
          }
        }
      }
    }
    None => ()
  }
  let names : Array[String] = globals.keys().collect()
  for n in names {
    let g = globals.get(n).unwrap()
    match g.kind {
      GFunc(Some(body), _, arity) if tm_mentions_any(body, splice) => {
        // a local function of a splice is only run by it; one of quoted
        // code starts at the stage of that code
        let depth = lifted_stages.get(n).unwrap_or(0)
        if depth < 0 {
          continue
        }
        unstage_owner.val = n
        unfold_everything.val = true
        let res : Result[Tm, ElabError] = try {
          let mut out = body
          with_time_limit(n, () => {
            specialized.clear()
            specializing.val = None
            // the parameters, with their types
            let lams : Array[(String, Icit, Bool)] = []
            let mut sc : Scope = { names: [], types: [], }
            let mut ty = g.vty
            let mut b = body
            while b is Lam(x, i, gr, rest) && force(ty) is VPi(_, _, _, a, cl) {
              lams.push((x, i, gr))
              ty = inst(cl, v_var(sc.length()))
              sc = sc.bind_typed(x, a)
              b = rest
            }
            out = wrap_lams(
              lams,
              expand(sc, fresh_vars(0, sc.length()), depth, b),
            )
          })
          Ok(out)
        } catch {
          ElabError(p, m) => Err(ElabError(p, m))
        }
        unfold_everything.val = false
        match res {
          Ok(t) => g.kind = GFunc(Some(t), contains_imperative(t), arity)
          Err(e) => raise e
        }
        // an imported function that the host could not call
        match ffi_error.val {
          Some(msg) =>
            raise ElabError(
              decl_pos.get(n).unwrap_or({ line: 0, col: 0, }),
              msg,
            )
          None => ()
        }
      }
      _ => ()
    }
  }
}

///|
/// The definition of the global `name` as it is run (after the expansion of
/// its splices), in MoonBit++ syntax.
pub fn show_global_body(name : String) -> String? {
  match globals.get(name) {
    Some({ kind: GFunc(Some(b), _, _), .. }) => Some(show_tm([], b))
    _ => None
  }
}
