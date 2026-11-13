///|
/// Recursive local functions. The core has no local recursion: a local
/// function that calls itself is lifted to a global function `f$go$N`
/// taking the variables of the enclosing context as parameters. Its body is
/// the lambda, where `go` is `f$go$N(ctx)`, and so is the local definition: the
/// function sees the context as it was when it was defined (it may not use
/// `let mut` variables, which a MoonBit closure would share).

///|
/// Lifted functions waiting for the end of the declaration that defines
/// them (their metas may be solved by the rest of it): owner, name, type,
/// body, arity.
let lifted : Array[(String, String, Tm, Tm, Int32)] = []

///|
let lifted_count : Ref[Int32] = Ref(0)

///|
/// Does `e` mention the variable `x` (ignoring shadowing)?
fn mentions(e : @parser.Expr, x : String) -> Bool {
  let found = Ref(false)
  mention_walk(e, x, found)
  found.val
}

///|
/// Is the variable `x` used by the code `code { e }` when it runs, or does
/// it escape in a splice of `e`? (A splice runs where the code is made.)
fn code_mentions(e : @parser.Expr, x : String) -> Bool {
  let saved = code_depth.val
  code_depth.val = 0
  let found = Ref(false)
  mention_walk(e, x, found)
  code_depth.val = saved
  found.val
}

///|
/// When not negative, `mention_walk` is in `code { }` (for `code_mentions`),
/// that many `code { }` below the code asked about.
let code_depth : Ref[Int32] = Ref(-1)

///|
fn mention_walk(e : @parser.Expr, x : String, found : Ref[Bool]) -> Unit {
  let walk = (y : @parser.Expr) => mention_walk(y, x, found)
  let walk_s = (st : @parser.Stmt) => mention_walk_s(st, x, found)
  match e {
    EVar(_, y) => if y == x { found.val = true }
    // (see `code_mentions`)
    EApp(_, EVar(_, "%quote"), None, Some([a])) if code_depth.val >= 0 => {
      code_depth.val = code_depth.val + 1
      walk(a)
      code_depth.val = code_depth.val - 1
    }
    EApp(_, EVar(_, "%splice"), None, Some([a])) if code_depth.val > 0 => {
      code_depth.val = code_depth.val - 1
      walk(a)
      code_depth.val = code_depth.val + 1
    }
    // a splice given code (of the variables around it, most likely) runs
    // when that code does
    EApp(_, EVar(_, "%splice"), None, Some([a])) if code_depth.val == 0 => {
      code_depth.val = -1
      if (mentions(a, "%quote") && mentions(a, x)) || escapes(a, x) {
        found.val = true
      }
      code_depth.val = 0
    }
    EApp(_, f, i, a) => {
      walk(f)
      for y in i.unwrap_or([]) {
        walk(y)
      }
      for y in a.unwrap_or([]) {
        walk(y)
      }
    }
    ELam(_, _, _, _, b) => walk(b)
    EBlock(_, stmts) =>
      for s in stmts {
        walk_s(s)
      }
    EIf(_, c, t, el) => {
      walk(c)
      walk(t)
      el.map(walk) |> ignore
    }
    EMatch(_, s, _, arms) | ETry(_, s, arms, _) => {
      walk(s)
      for a in arms {
        a.cond.map(walk) |> ignore
        a.rhs.map(walk) |> ignore
      }
    }
    ELoop(_, _, args, arms) => {
      args.each(walk)
      for a in arms {
        a.cond.map(walk) |> ignore
        a.rhs.map(walk) |> ignore
      }
    }
    EAnn(_, a, _)
    | EField(_, a, _)
    | EUn(_, _, a)
    | ETryQ(_, a)
    | ERaise(_, a)
    | EMonad(_, a)
    | EUnfold(_, _, a)
    | EBind(_, a) => walk(a)
    ERange(_, a, b, _) => {
      walk(a)
      walk(b)
    }
    EPerform(_, _, args) => args.each(walk)
    EMethod(_, a, _, _, args) => {
      walk(a)
      args.each(walk)
    }
    EBin(_, _, a, b) => {
      walk(a)
      walk(b)
    }
    ETuple(_, es) | EArray(_, es) => es.each(walk)
    EStruct(_, fs) => fs.each(f => walk(f.1))
    EReturn(_, v) | EBreak(_, _, v) => v.map(walk) |> ignore
    EContinue(_, _, args) => args.each(walk)
    EIs(_, a, _) => walk(a)
    EInterp(_, parts) =>
      for q in parts {
        if q is IExpr(y) {
          walk(y)
        }
      }
    ETagged(_, _, a, _) => walk(a)
    _ => ()
  }
}

///|
fn mention_walk_s(s : @parser.Stmt, x : String, found : Ref[Bool]) -> Unit {
  let walk = (y : @parser.Expr) => mention_walk(y, x, found)
  let walk_s = (st : @parser.Stmt) => mention_walk_s(st, x, found)
  match s {
    SLet(_, _, _, e)
    | SLetMut(_, _, _, e)
    | SLetBind(_, _, e)
    | SAssign(_, _, _, e)
    | SDefer(_, e)
    | SExpr(_, e) => walk(e)
    SFn(_, d) =>
      match d.body {
        BodyExpr(b) => walk(b)
        _ => ()
      }
    SGuard(_, c, el) => {
      walk(c)
      el.map(walk) |> ignore
    }
    SWhile(_, c, b) => {
      walk(c)
      walk(b)
    }
    SFor(_, inits, c, ups, b) => {
      inits.each(x => walk(x.1))
      c.map(walk) |> ignore
      ups.each(x => walk(x.1))
      walk(b)
    }
    SForIn(_, _, e, b) => {
      walk(e)
      walk(b)
    }
    SLoopX(_, _, inner, nb) => {
      walk_s(inner)
      nb.map(walk) |> ignore
    }
  }
}

///|
/// The levels of the context (below `lvl`) that `t` refers to, `t` being
/// under `depth` more binders.
fn ref_levels(t : Tm, lvl : Int32, depth : Int32, out : Array[Int32]) -> Unit {
  let go = (x : Tm, d : Int32) => ref_levels(x, lvl, depth + d, out)
  match t {
    Var(ix) => if ix >= depth { out.push(lvl - 1 - (ix - depth)) }
    Lam(_, _, _, b) => go(b, 1)
    App(f, a, _) => {
      go(f, 0)
      go(a, 0)
    }
    Pi(_, _, _, a, b) => {
      go(a, 0)
      go(b, 1)
    }
    Let(_, a, v, b) | LetMut(_, a, v, b) => {
      go(a, 0)
      go(v, 0)
      go(b, 1)
    }
    Match(ss, cls) => {
      ss.each(s => go(s, 0))
      for cl in cls {
        let k = pats_slots(cl.pats)
        cl.cond.map(c => go(c, k)) |> ignore
        go(cl.body, k)
      }
    }
    Try(b, cls) => {
      go(b, 0)
      for cl in cls {
        let k = pats_slots(cl.pats)
        cl.cond.map(c => go(c, k)) |> ignore
        go(cl.body, k)
      }
    }
    Raises(a, e) => {
      go(a, 0)
      go(e, 0)
    }
    Assign(ix, v) => {
      if ix >= depth {
        out.push(lvl - 1 - (ix - depth))
      }
      go(v, 0)
    }
    Return(v) | Raise(v) => go(v, 0)
    While(c, b, s) => {
      go(c, 0)
      go(b, 0)
      go(s, 0)
    }
    Seq(a, b) | Defer(a, b) => {
      go(a, 0)
      go(b, 0)
    }
    ArrayLit(es) => es.each(e => go(e, 0))
    _ => ()
  }
}

///|
/// A recursive local function `name`: elaborate it with itself in scope,
/// lift it, and continue with `rest` where `name` is the lifted function
/// applied to the context.
fn elab_local_rec(
  cxt : Cxt,
  p : Pos,
  name : String,
  lam : @parser.Expr,
) -> (Tm, Val, Tm) raise ElabError {
  let c = cxt.at(p)
  let (impls, ps, ret) = match lam {
    ELam(_, i, ps, r, _) => (i, ps, r)
    _ => c.fail("expected a function")
  }
  let (fty_tm, fty) = infer_lam_type(c, impls, ps, ret)
  // the function, with itself as the last variable of its context
  let c2 = c.bind(name, fty)
  let t = check(c2, lam, fty)
  let levels : Array[Int32] = []
  ref_levels(t, c2.lvl, 0, levels)
  for l in levels {
    if l < cxt.lvl && cxt.muts[l] {
      c.fail(
        "the recursive local function " +
        name +
        " cannot use the mutable variable " +
        cxt.names[l],
      )
    }
  }
  lifted_count.val = lifted_count.val + 1
  let owner = match time_frames.last() {
    Some(f) => f.name
    None => ""
  }
  let g = owner + "$" + name + "$" + lifted_count.val.to_string()
  // the context as parameters: g(ctx) is the function
  let n = cxt.lvl
  let call = apps(Global(g), Array::makei(n, k => (Var(n - 1 - k), Expl)))
  let mut gty = quote(n, fty)
  // `go` is replaced by `g(ctx)` (a `let` would evaluate it, forever)
  let mut gbody = subst_go(t, n, g, 0)
  for k = n - 1; k >= 0; k = k - 1 {
    gty = Pi(cxt.names[k], Expl, k == n - 1, quote(k, cxt.types[k]), gty)
    gbody = Lam(cxt.names[k], Expl, k == n - 1, gbody)
  }
  ignore(fty_tm)
  // its splices are those of the stage it is defined at (staging.mbt)
  if cxt.stage != 0 {
    lifted_stages.set(g, cxt.stage)
  }
  lifted.push((owner, g, gty, gbody, n))
  (call, fty, Global(g))
}

///|
/// Register the functions lifted from declaration `owner`, now that its
/// metas are solved.
fn register_lifted(cxt : Cxt, owner : String) -> Unit raise ElabError {
  let mine = lifted.filter(x => x.0 == owner)
  if mine.length() == 0 {
    return
  }
  let others = lifted.filter(x => x.0 != owner)
  lifted.clear()
  for x in others {
    lifted.push(x)
  }
  for x in mine {
    let (_, g, ty, body, n) = x
    let ty = zonk(0, ty)
    let body = zonk(0, body)
    if has_metas(ty) || has_metas(body) {
      cxt.fail("cannot infer the types of the local function " + g)
    }
    register(g, ty, GFunc(None, false, n))
    set_body(g, body, n)
    match global_files.get(owner) {
      Some(f) => global_files.set(g, f)
      None => ()
    }
  }
}

///|
/// `t`, in the context of `n` variables followed by the function itself,
/// without the function: its occurrences become `g(ctx)`. `d` binders are
/// crossed.
fn subst_go(t : Tm, n : Int32, g : String, d : Int32) -> Tm {
  let go = (x : Tm, k : Int32) => subst_go(x, n, g, d + k)
  let var_of = (ix : Int32) => {
    if ix < d {
      Var(ix)
    } else if ix == d {
      apps(Global(g), Array::makei(n, k => (Var(d + n - 1 - k), Expl)))
    } else {
      Var(ix - 1)
    }
  }
  let clause = (cl : Clause) => {
    let k = pats_slots(cl.pats)
    cl.map(b => go(b, k))
  }
  match t {
    Var(ix) => var_of(ix)
    Lam(x, i, gr, b) => Lam(x, i, gr, go(b, 1))
    App(f, a, i) => App(go(f, 0), go(a, 0), i)
    Pi(x, i, gr, a, b) => Pi(x, i, gr, go(a, 0), go(b, 1))
    Let(x, a, v, b) => Let(x, go(a, 0), go(v, 0), go(b, 1))
    LetMut(x, a, v, b) => LetMut(x, go(a, 0), go(v, 0), go(b, 1))
    Match(ss, cls) => Match(ss.map(s => go(s, 0)), cls.map(clause))
    Try(b, cls) => Try(go(b, 0), cls.map(clause))
    Raises(a, e) => Raises(go(a, 0), go(e, 0))
    Assign(ix, v) =>
      match var_of(ix) {
        Var(j) => Assign(j, go(v, 0))
        _ => t
      }
    While(c, b, s) => While(go(c, 0), go(b, 0), go(s, 0))
    Return(v) => Return(go(v, 0))
    Raise(v) => Raise(go(v, 0))
    ArrayLit(es) => ArrayLit(es.map(e => go(e, 0)))
    Seq(a, b) => Seq(go(a, 0), go(b, 0))
    Defer(a, b) => Defer(go(a, 0), go(b, 0))
    InsertedMeta(m, mask) =>
      // the function's own slot is dropped from the mask
      if mask.length() > n {
        InsertedMeta(m, mask[0:n].to_array() + mask[n + 1:].to_array())
      } else {
        t
      }
    _ => t
  }
}
