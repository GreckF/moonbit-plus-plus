///|
/// Loops with labels, `break` values, `nobreak` blocks, and `loop`
/// expressions. They are rewritten into the plain `while`/`for` loops of the
/// core, which only `break` and `continue` their innermost loop:
///
/// - `break e` of the loop `L` stores `Some(e)` in a result variable and
///   breaks; after `L`, the result is `e`, or the `nobreak` block (or `()`)
///   when the loop ended without a `break`;
/// - from a nested loop, `break L~` and `continue L~` set a flag and break
///   the nested loop; after each nested loop, the flag breaks (or continues)
///   the enclosing one, up to `L`;
/// - `loop a, b { arms }` keeps its arguments in a state variable: an arm's
///   value ends the loop, `continue x, y` sets the state and runs the arms
///   again.

///|
priv struct LoopRw {
  label : String?
  /// The result variable (`Option[T]`).
  r : String
  /// Flags of a `break` or `continue` of the loop from a nested loop.
  b : String
  c : String
  /// The state variable of a `loop` expression.
  s : String?
  /// The depths of the references to the loop that were rewritten.
  refs : Array[Int32]
}

///|
fn LoopRw::targets(self : LoopRw, label : String?, d : Int32) -> Bool {
  match label {
    None => d == 0
    Some(l) => self.label == Some(l)
  }
}

///|
fn assign(p : Pos, x : String, e : @parser.Expr) -> @parser.Stmt {
  SAssign(p, EVar(p, x), "=", e)
}

///|
fn some_of(p : Pos, e : @parser.Expr) -> @parser.Expr {
  EApp(p, EVar(p, "Option::Some"), None, Some([e]))
}

///|
fn tuple_of(p : Pos, es : Array[@parser.Expr]) -> @parser.Expr {
  if es.length() == 1 {
    es[0]
  } else {
    ETuple(p, es)
  }
}

///|
/// Rewrite the references to the loop in `e`, at loop depth `d` (0: the
/// body of the loop itself).
fn LoopRw::expr(self : LoopRw, e : @parser.Expr, d : Int32) -> @parser.Expr {
  let go = (x : @parser.Expr) => self.expr(x, d)
  let arms = (xs : Array[@parser.Arm], dd : Int32) => {
    xs.map(a => {
      ..a,
      cond: a.cond.map(c => self.expr(c, dd)),
      rhs: a.rhs.map(r => self.expr(r, dd)),
    })
  }
  match e {
    EBreak(p, label, v) if self.targets(label, d) => {
      self.refs.push(d)
      let v = v.map(go).unwrap_or(ELit(p, LUnit))
      let stmts = [assign(p, self.r, some_of(p, v))]
      if d > 0 {
        stmts.push(assign(p, self.b, ELit(p, LBool(true))))
      }
      stmts.push(SExpr(p, EBreak(p, None, None)))
      EBlock(p, stmts)
    }
    EContinue(p, label, args) if self.targets(label, d) => {
      self.refs.push(d)
      let stmts : Array[@parser.Stmt] = []
      match self.s {
        Some(s) => stmts.push(assign(p, s, tuple_of(p, args.map(go))))
        None => ()
      }
      if d > 0 {
        stmts.push(assign(p, self.c, ELit(p, LBool(true))))
        stmts.push(SExpr(p, EBreak(p, None, None)))
      } else {
        stmts.push(SExpr(p, EContinue(p, None, [])))
      }
      EBlock(p, stmts)
    }
    EBreak(p, l, v) => EBreak(p, l, v.map(go))
    EContinue(p, l, args) => EContinue(p, l, args.map(go))
    ELoop(p, l, args, xs) => ELoop(p, l, args.map(go), arms(xs, d + 1))
    EBlock(p, stmts) => EBlock(p, self.stmts(stmts, d))
    // break and continue do not cross functions
    ELam(_, _, _, _, _) => e
    EApp(p, f, i, x) =>
      EApp(p, go(f), i.map(xs => xs.map(go)), x.map(xs => xs.map(go)))
    EIf(p, c, t, el) => EIf(p, go(c), go(t), el.map(go))
    EMatch(p, s, r, xs) => EMatch(p, go(s), r, arms(xs, d))
    EAnn(p, x, t) => EAnn(p, go(x), t)
    EField(p, x, f) => EField(p, go(x), f)
    EMethod(p, x, m, i, args) => EMethod(p, go(x), m, i, args.map(go))
    EBin(p, op, a, b) => EBin(p, op, go(a), go(b))
    EUn(p, op, a) => EUn(p, op, go(a))
    ETuple(p, es) => ETuple(p, es.map(go))
    EArray(p, es) => EArray(p, es.map(go))
    EStruct(p, fs) => EStruct(p, fs.map(f => (f.0, go(f.1))))
    ETry(p, b, xs, ok) => ETry(p, go(b), arms(xs, d), ok.map(o => arms(o, d)))
    ETryQ(p, x) => ETryQ(p, go(x))
    ERaise(p, x) => ERaise(p, go(x))
    EPerform(p, op, args) => EPerform(p, op, args.map(go))
    EUnfold(p, names, x) => EUnfold(p, names, go(x))
    EReturn(p, x) => EReturn(p, x.map(go))
    EIs(p, x, pat) => EIs(p, go(x), pat)
    EInterp(p, parts) =>
      EInterp(
        p,
        parts.map(q => {
          match q {
            IExpr(x) => IExpr(go(x))
            other => other
          }
        }),
      )
    ETagged(p, l, x, o) => ETagged(p, l, go(x), o)
    _ => e
  }
}

///|
/// A statement list at depth `d`: after a statement whose nested loops
/// referred to the loop, the flags are tested.
fn LoopRw::stmts(
  self : LoopRw,
  stmts : Array[@parser.Stmt],
  d : Int32,
) -> Array[@parser.Stmt] {
  let out : Array[@parser.Stmt] = []
  for s in stmts {
    let before = self.refs.length()
    out.push(self.stmt(s, d))
    let deep = self.refs[before:].iter().any(k => k > d)
    if deep {
      let p = stmt_pos(s)
      let brk : @parser.Expr = EBlock(p, [SExpr(p, EBreak(p, None, None))])
      out.push(SExpr(p, EIf(p, EVar(p, self.b), brk, None)))
      let cont : @parser.Expr = if d == 0 {
        EBlock(p, [
          assign(p, self.c, ELit(p, LBool(false))),
          SExpr(p, EContinue(p, None, [])),
        ])
      } else {
        brk
      }
      out.push(SExpr(p, EIf(p, EVar(p, self.c), cont, None)))
    }
  }
  out
}

///|
fn LoopRw::stmt(self : LoopRw, s : @parser.Stmt, d : Int32) -> @parser.Stmt {
  let go = (x : @parser.Expr) => self.expr(x, d)
  match s {
    SLet(p, pat, t, e) => SLet(p, pat, t, go(e))
    SLetMut(p, x, t, e) => SLetMut(p, x, t, go(e))
    SLetBind(p, pat, e) => SLetBind(p, pat, go(e))
    SFn(_, _) => s
    SAssign(p, l, op, e) => SAssign(p, go(l), op, go(e))
    SExpr(p, e) => SExpr(p, go(e))
    SGuard(p, c, el) => SGuard(p, go(c), el.map(go))
    SDefer(p, e) => SDefer(p, go(e))
    SWhile(p, c, b) => SWhile(p, self.expr(c, d + 1), self.expr(b, d + 1))
    SFor(p, inits, c, ups, b) =>
      SFor(
        p,
        inits.map(x => (x.0, go(x.1))),
        c.map(x => self.expr(x, d + 1)),
        ups.map(x => (x.0, self.expr(x.1, d + 1))),
        self.expr(b, d + 1),
      )
    SForIn(p, xs, e, b) => SForIn(p, xs, go(e), self.expr(b, d + 1))
    SLoopX(p, l, inner, nb) => SLoopX(p, l, self.stmt(inner, d), nb.map(go))
  }
}

///|
fn stmt_pos(s : @parser.Stmt) -> Pos {
  match s {
    SLet(p, _, _, _)
    | SLetMut(p, _, _, _)
    | SLetBind(p, _, _)
    | SFn(p, _)
    | SAssign(p, _, _, _)
    | SExpr(p, _)
    | SGuard(p, _, _)
    | SDefer(p, _)
    | SWhile(p, _, _)
    | SFor(p, _, _, _, _)
    | SForIn(p, _, _, _)
    | SLoopX(p, _, _, _) => p
  }
}

///|
fn new_loop_rw(label : String?, state : Bool) -> LoopRw {
  {
    label,
    r: fresh_name_gen("__loop_r"),
    b: fresh_name_gen("__loop_b"),
    c: fresh_name_gen("__loop_c"),
    s: if state {
      Some(fresh_name_gen("__loop_s"))
    } else {
      None
    },
    refs: [],
  }
}

///|
/// The block computing a rewritten loop: the variables, the loop, and its
/// value.
fn loop_block(
  p : Pos,
  rw : LoopRw,
  pre : Array[@parser.Stmt],
  lp : @parser.Stmt,
  no_break : @parser.Expr?,
) -> @parser.Expr {
  let stmts : Array[@parser.Stmt] = [
    SLetMut(p, rw.r, None, EVar(p, "Option::None")),
    SLetMut(p, rw.b, None, ELit(p, LBool(false))),
    SLetMut(p, rw.c, None, ELit(p, LBool(false))),
    ..pre,
    lp,
  ]
  let v = fresh_name_gen("__loop_v")
  stmts.push(
    SExpr(
      p,
      EMatch(p, EVar(p, rw.r), None, [
        {
          pos: p,
          pat: PCon(p, "Option::Some", None, [PVar(p, v)]),
          cond: None,
          rhs: Some(EVar(p, v)),
        },
        {
          pos: p,
          pat: PCon(p, "Option::None", None, []),
          cond: None,
          rhs: Some(no_break.unwrap_or(ELit(p, LUnit))),
        },
      ]),
    ),
  )
  EBlock(p, stmts)
}

///|
/// The rewriting of a `while` or `for` loop with a label, `break` values
/// or a `nobreak` block.
fn rewrite_loop(
  p : Pos,
  label : String?,
  lp : @parser.Stmt,
  no_break : @parser.Expr?,
) -> @parser.Expr {
  let rw = new_loop_rw(label, false)
  let lp2 = match lp {
    SWhile(q, c, b) => @parser.SWhile(q, rw.expr(c, 0), rw.expr(b, 0))
    SFor(q, inits, c, ups, b) =>
      @parser.SFor(
        q,
        inits,
        c.map(x => rw.expr(x, 0)),
        ups.map(x => (x.0, rw.expr(x.1, 0))),
        rw.expr(b, 0),
      )
    SForIn(q, xs, e, b) => @parser.SForIn(q, xs, e, rw.expr(b, 0))
    other => other
  }
  loop_block(p, rw, [], lp2, no_break)
}

///|
/// `loop a, b { arms }`
fn rewrite_loop_expr(
  p : Pos,
  label : String?,
  args : Array[@parser.Expr],
  arms : Array[@parser.Arm],
) -> @parser.Expr {
  let rw = new_loop_rw(label, true)
  let s = rw.s.unwrap()
  let arms2 = arms.map(a => {
    let rhs = a.rhs.map(r => {
      @parser.EBlock(r.pos(), [
        assign(r.pos(), rw.r, some_of(r.pos(), rw.expr(r, 0))),
        SExpr(r.pos(), EBreak(r.pos(), None, None)),
      ])
    })
    { ..a, cond: a.cond.map(c => rw.expr(c, 0)), rhs, }
  })
  let body : @parser.Expr = EBlock(p, [
    SExpr(p, EMatch(p, EVar(p, s), None, arms2)),
  ])
  loop_block(
    p,
    rw,
    [SLetMut(p, s, None, tuple_of(p, args))],
    SWhile(p, ELit(p, LBool(true)), body),
    Some(EApp(p, EVar(p, "abort"), None, Some([ELit(p, LStr("unreachable"))]))),
  )
}

///|
/// Does a loop body `break` its loop with a value (so that the loop must be
/// rewritten)?
fn has_break_value(e : @parser.Expr, d : Int32) -> Bool {
  let go = (x : @parser.Expr) => has_break_value(x, d)
  match e {
    EBreak(_, None, Some(_)) => d == 0
    EBlock(_, stmts) =>
      stmts
      .iter()
      .any(s => {
        match s {
          SWhile(_, _, _)
          | SFor(_, _, _, _, _)
          | SForIn(_, _, _, _)
          | SLoopX(_, _, _, _) => false
          SLet(_, _, _, x)
          | SLetMut(_, _, _, x)
          | SExpr(_, x)
          | SAssign(_, _, _, x) => go(x)
          SGuard(_, c, el) => go(c) || el.map(go).unwrap_or(false)
          _ => false
        }
      })
    EIf(_, c, t, el) => go(c) || go(t) || el.map(go).unwrap_or(false)
    EMatch(_, s, _, arms) =>
      go(s) || arms.iter().any(a => a.rhs.map(go).unwrap_or(false))
    ETry(_, b, arms, _) =>
      go(b) || arms.iter().any(a => a.rhs.map(go).unwrap_or(false))
    _ => false
  }
}
