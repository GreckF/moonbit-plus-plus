///|
/// Blocks, statements and `monad` blocks.
fn unit_ty() -> Val {
  VData("Unit", [])
}

///|
fn check_block(
  cxt : Cxt,
  stmts : Array[@parser.Stmt],
  goal : Val?,
) -> (Tm, Val) raise ElabError {
  if stmts.length() == 0 {
    match goal {
      Some(g) => cxt.unify(g, unit_ty())
      None => ()
    }
    return (Lit(LUnit), unit_ty())
  }
  let s = stmts[0]
  let rest = stmts[1:].to_owned()
  let last = rest.length() == 0
  match s {
    SExpr(p, e) =>
      if last {
        let c = cxt.at(p)
        match goal {
          Some(g) => (check(c, e, g), g)
          None => infer_ins(c, e)
        }
      } else {
        let (t, _) = infer_ins(cxt.at(p), e)
        let (r, rty) = check_block(cxt, rest, goal)
        (Seq(t, r), rty)
      }
    SLet(p, pat, ty, e) => {
      let c = cxt.at(p)
      match pat {
        PVar(_, _) | PWild(_) => {
          let x = match pat {
            PVar(_, x) => x
            _ => "_"
          }
          let (t, a) = match ty {
            Some(ty) => {
              let a = c.eval(check_type(c, ty))
              (check(c, e, a), a)
            }
            None => infer_ins(c, e)
          }
          let c2 = cxt.define_local(x, a, cxt.eval(t))
          let (r, rty) = check_block(c2, rest, goal)
          (Let(x, cxt.quote(a), t, r), rty)
        }
        _ => {
          let scr : @parser.Expr = match ty {
            Some(ty) => EAnn(p, e, ty)
            None => e
          }
          let m : @parser.Expr = EMatch(p, scr, None, [
            { pos: p, pat, cond: None, rhs: Some(EBlock(p, rest)), },
          ])
          match goal {
            Some(g) => (check(c, m, g), g)
            None => infer(c, m)
          }
        }
      }
    }
    SLetMut(p, x, ty, e) => {
      let c = cxt.at(p)
      let (t, a) = match ty {
        Some(ty) => {
          let a = c.eval(check_type(c, ty))
          (check(c, e, a), a)
        }
        None => infer_ins(c, e)
      }
      let c2 = cxt.bind_mut(x, a)
      let (r, rty) = check_block(c2, rest, goal)
      (LetMut(x, cxt.quote(a), t, r), rty)
    }
    SLetBind(p, _, _) =>
      cxt.at(p).fail("`let x <- e` can only be used inside a monad block")
    SFn(p, d) => {
      let body = match d.body {
        BodyExpr(b) => b
        BodyExtern(_) => cxt.at(p).fail("local functions cannot be external")
      }
      // the effect of a local function is part of its result type
      let ret = match d.raises {
        Some(eff) => Some(@parser.EEff(p, d.ret.unwrap_or(EHole(p)), eff))
        None => d.ret
      }
      let lam : @parser.Expr = ELam(
        p,
        d.impl_params,
        d.params.unwrap_or([]),
        ret,
        body,
      )
      if !mentions(body, d.name) {
        return check_block(
          cxt,
          [SLet(p, PVar(p, d.name), None, lam), ..rest],
          goal,
        )
      }
      // a recursive local function (see localfn.mbt)
      let (call, fty, _) = elab_local_rec(cxt, p, d.name, lam)
      let c2 = cxt.define_local(d.name, fty, cxt.eval(call))
      let (r, rty) = check_block(c2, rest, goal)
      (Let(d.name, cxt.quote(fty), call, r), rty)
    }
    SAssign(p, lhs, op, rhs) => {
      let c = cxt.at(p)
      let rhs : @parser.Expr = if op == "=" {
        rhs
      } else {
        EBin(p, op.unsafe_substring(start=0, end=1), lhs, rhs)
      }
      let t = match lhs {
        EVar(_, x) =>
          match cxt.lookup(x) {
            Some(l) if cxt.muts[l] => {
              check_stage(c, x, l)
              Assign(cxt.lvl - 1 - l, check(c, rhs, cxt.types[l]))
            }
            _ => c.fail(x + " is not a mutable variable")
          }
        EApp(_, arr, Some([i]), None) =>
          infer_ins(c, EMethod(p, arr, "op_set", None, [i, rhs])).0
        // `p.x = v`: a mutable field, written in its box
        EField(fp, e, f) => {
          let (te, tye) = infer_ins(c, e)
          let (tb, tyb) = elab_field(c, te, tye, f, at=fp, raw=true)
          match head_name(tye) {
            Some(d) if mut_fields.contains(d + "::" + f) => ()
            _ => c.fail("the field " + f + " is not mutable")
          }
          elab_method(c, tb, tyb, "op_set", None, [
            AV(Lit(LInt(0)), VData("Int", [])),
            AE(rhs),
          ]).0
        }
        _ => c.fail("invalid assignment target")
      }
      let (r, rty) = check_block(cxt, rest, goal)
      (Seq(t, r), rty)
    }
    // `while x is Some(y) { .. }`: the test is the first statement
    SWhile(p, cond, body) if has_is(cond) => {
      let body2 = cond_expr(cond, body, EBreak(p, None, None))
      check_block(cxt, [SWhile(p, ELit(p, LBool(true)), body2), ..rest], goal)
    }
    // loops with labels, `break` values or `nobreak` (see loops.mbt)
    SLoopX(p, label, lp, nb) =>
      check_block(cxt, [SExpr(p, rewrite_loop(p, label, lp, nb)), ..rest], goal)
    SWhile(p, _, body) | SFor(p, _, _, _, body) | SForIn(p, _, _, body) if has_break_value(
        body, 0,
      ) =>
      check_block(cxt, [SExpr(p, rewrite_loop(p, None, s, None)), ..rest], goal)
    // `defer e; rest`
    SDefer(p, e) => {
      let td = check(cxt.at(p), e, unit_ty())
      let (r, rty) = check_block(cxt, rest, goal)
      (Defer(td, r), rty)
    }
    // `guard c else { e }; rest` is `if c { rest } else { e }`
    SGuard(p, cond, el) => {
      let el = el.unwrap_or(
        EApp(p, EVar(p, "abort"), None, Some([ELit(p, LStr("guard failed"))])),
      )
      check_block(
        cxt,
        [SExpr(p, EIf(p, cond, EBlock(p, rest), Some(el)))],
        goal,
      )
    }
    SWhile(p, cond, body) => {
      let c = cxt.at(p)
      let tc = check(c, cond, bool_ty())
      let tb = check({ ..c, in_loop: true, }, body, unit_ty())
      let (r, rty) = check_block(cxt, rest, goal)
      (Seq(While(tc, tb, Lit(LUnit)), r), rty)
    }
    SFor(p, inits, cond, updates, body) => {
      let mut c = cxt.at(p)
      let lets : Array[(String, Tm, Tm)] = []
      for init in inits {
        let (t, a) = infer_ins(c, init.1)
        lets.push((init.0, c.quote(a), t))
        c = c.bind_mut(init.0, a)
      }
      let tc = match cond {
        Some(e) => check(c, e, bool_ty())
        None => Lit(LBool(true))
      }
      // as in MoonBit, the body sees an immutable copy of each loop variable
      // (closures keep the value of their iteration)
      let mut cb = c
      for k = 0; k < lets.length(); k = k + 1 {
        cb = cb.bind(lets[k].0, c.types[c.lvl - lets.length() + k])
      }
      let mut tb = check({ ..cb, in_loop: true, }, body, unit_ty())
      for k = lets.length() - 1; k >= 0; k = k - 1 {
        // under the variables and the copies 0 .. k-1: variable `k` is n-1
        let (x, a, _) = lets[k]
        tb = Let(x, tm_shift(a, lets.length(), 0), Var(lets.length() - 1), tb)
      }
      let mut step = Lit(LUnit)
      for k = updates.length() - 1; k >= 0; k = k - 1 {
        let (x, e) = updates[k]
        match c.lookup(x) {
          Some(l) =>
            step = Seq(Assign(c.lvl - 1 - l, check(c, e, c.types[l])), step)
          None => c.fail("unknown loop variable " + x)
        }
      }
      let mut loop_tm = While(tc, tb, step)
      for k = lets.length() - 1; k >= 0; k = k - 1 {
        let (x, a, t) = lets[k]
        loop_tm = LetMut(x, a, t, loop_tm)
      }
      let (r, rty) = check_block(cxt, rest, goal)
      (Seq(loop_tm, r), rty)
    }
    // `for k, v in m` on a map: its pairs
    SForIn(p, [k, v], e, body) if infer_ins(cxt.at(p), e).1
      is VData("Map" | "HashMap", _) => {
      let pair = fresh_name_gen("__kv")
      let body2 : @parser.Expr = EBlock(p, [
        SLet(p, PTuple(p, [PVar(p, k), PVar(p, v)]), None, EVar(p, pair)),
        SExpr(p, body),
      ])
      check_block(
        cxt,
        [SForIn(p, [pair], EMethod(p, e, "to_array", None, []), body2), ..rest],
        goal,
      )
    }
    SForIn(p, xs, e, body) => {
      let x = xs[xs.length() - 1]
      let i = fresh_name_gen("__i")
      let ev : @parser.Expr = EVar(p, i)
      let one : @parser.Expr = ELit(p, LInt(1))
      let step : Array[(String, @parser.Expr)] = [
        (i, @parser.EBin(p, "+", ev, one)),
      ]
      let loop_stmts : Array[@parser.Stmt] = match e {
        ERange(_, a, b, incl) => {
          let cond : @parser.Expr = EBin(
            p,
            if incl {
              "<="
            } else {
              "<"
            },
            ev,
            b,
          )
          if xs.length() > 1 {
            cxt.at(p).fail("a range has one loop variable")
          }
          let body2 : @parser.Expr = EBlock(p, [
            SLet(p, PVar(p, x), None, ev),
            SExpr(p, body),
          ])
          [SFor(p, [(i, a)], Some(cond), step, body2)]
        }
        _ => {
          let arr = fresh_name_gen("__a")
          let av : @parser.Expr = EVar(p, arr)
          let cond : @parser.Expr = EBin(
            p,
            "<",
            ev,
            EMethod(p, av, "length", None, []),
          )
          // `for i, x in xs`: the index and the element
          let body2 : @parser.Expr = EBlock(
            p,
            [
              ..xs[0:xs.length() - 1]
              .to_owned()
              .map(i0 => @parser.SLet(p, PVar(p, i0), None, ev)),
              SLet(p, PVar(p, x), None, EApp(p, av, Some([ev]), None)),
              SExpr(p, body),
            ],
          )
          [
            SLet(p, PVar(p, arr), None, e),
            SFor(p, [(i, ELit(p, LInt(0)))], Some(cond), step, body2),
          ]
        }
      }
      let (t, _) = check_block(cxt, loop_stmts, Some(unit_ty()))
      let (r, rty) = check_block(cxt, rest, goal)
      (Seq(t, r), rty)
    }
  }
}

// ---------------------------------------------------------------------------
// monad blocks

///|
fn monad_bind(p : Pos, m : @parser.Expr, f : @parser.Expr) -> @parser.Expr {
  EApp(p, EVar(p, "Monad::bind"), None, Some([m, f]))
}

///|
fn pat_lam(p : Pos, pat : @parser.Pat, body : @parser.Expr) -> @parser.Expr {
  match pat {
    PVar(q, x) =>
      ELam(
        p,
        [],
        [{ pos: q, name: x, ty: None, kind: Positional, }],
        None,
        body,
      )
    PWild(q) =>
      ELam(
        p,
        [],
        [{ pos: q, name: "_", ty: None, kind: Positional, }],
        None,
        body,
      )
    _ => {
      let x = fresh_name_gen("__p")
      ELam(
        p,
        [],
        [{ pos: p, name: x, ty: None, kind: Positional, }],
        None,
        EMatch(p, EVar(p, x), None, [
          { pos: p, pat, cond: None, rhs: Some(body), },
        ]),
      )
    }
  }
}

///|
/// Replace nested `<- m` by fresh variables, collecting the lifted actions.
fn lift_binds(
  e : @parser.Expr,
  out : Array[(String, @parser.Expr)],
) -> @parser.Expr {
  let go = x => lift_binds(x, out)
  match e {
    EBind(p, m) => {
      let m2 = lift_binds(m, out)
      let x = fresh_name_gen("__m")
      out.push((x, m2))
      EVar(p, x)
    }
    EApp(p, f, i, x) => {
      let f2 = go(f)
      let i2 = i.map(xs => xs.map(go))
      EApp(p, f2, i2, x.map(xs => xs.map(go)))
    }
    EMethod(p, x, m, i, args) => {
      let x2 = go(x)
      EMethod(p, x2, m, i, args.map(go))
    }
    EBin(p, op, a, b) => {
      let a2 = go(a)
      EBin(p, op, a2, go(b))
    }
    EUn(p, op, a) => EUn(p, op, go(a))
    ETuple(p, es) => ETuple(p, es.map(go))
    EArray(p, es) => EArray(p, es.map(go))
    EStruct(p, fs) => EStruct(p, fs.map(f => (f.0, go(f.1))))
    EAnn(p, x, t) => EAnn(p, go(x), t)
    EField(p, x, f) => EField(p, go(x), f)
    EIf(p, c, t, el) => EIf(p, go(c), t, el)
    EMatch(p, s, r, arms) => EMatch(p, go(s), r, arms)
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
    _ => e
  }
}

///|
fn desugar_monad(b : @parser.Expr) -> @parser.Expr {
  match b {
    EBlock(_, stmts) => desugar_stmts(stmts)
    _ => desugar_stmts([SExpr(b.pos(), b)])
  }
}

///|
fn desugar_stmts(stmts : Array[@parser.Stmt]) -> @parser.Expr {
  if stmts.length() == 0 {
    return ELit({ line: 0, col: 0, }, LUnit)
  }
  let rest = stmts[1:].to_owned()
  let last = rest.length() == 0
  let binds : Array[(String, @parser.Expr)] = []
  let s : @parser.Stmt = match stmts[0] {
    SExpr(p, e) => SExpr(p, lift_binds(e, binds))
    SLet(p, pat, ty, e) => SLet(p, pat, ty, lift_binds(e, binds))
    SLetBind(p, pat, e) => SLetBind(p, pat, lift_binds(e, binds))
    SAssign(p, l, op, e) => SAssign(p, l, op, lift_binds(e, binds))
    other => other
  }
  let mut inner : @parser.Expr = match s {
    SLetBind(p, pat, m) =>
      monad_bind(p, m, pat_lam(p, pat, desugar_stmts(rest)))
    SExpr(_, e) if last => e
    SExpr(p, e) => monad_bind(p, e, pat_lam(p, PWild(p), desugar_stmts(rest)))
    other => {
      let p = match other {
        SLet(p, _, _, _)
        | SLetMut(p, _, _, _)
        | SFn(p, _)
        | SAssign(p, _, _, _) => p
        SWhile(p, _, _)
        | SFor(p, _, _, _, _)
        | SForIn(p, _, _, _)
        | SLoopX(p, _, _, _) => p
        SExpr(p, _) | SLetBind(p, _, _) | SGuard(p, _, _) | SDefer(p, _) => p
      }
      EBlock(p, [other, SExpr(p, desugar_stmts(rest))])
    }
  }
  for k = binds.length() - 1; k >= 0; k = k - 1 {
    let (x, m) = binds[k]
    let p = m.pos()
    inner = monad_bind(p, m, pat_lam(p, PVar(p, x), inner))
  }
  inner
}
