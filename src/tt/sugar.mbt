///|
/// Pattern and condition sugar: or-patterns, `as` on variables, `e is p`
/// conditions and `try ... noraise`.

///|
/// The alternatives of a pattern without or-patterns, each with the aliases
/// `(x, y)` (`x` names the value of variable `y`) of `y as x`.
fn pat_alts(
  cxt : Cxt,
  p : @parser.Pat,
) -> Array[(@parser.Pat, Array[(String, String)])] raise ElabError {
  match p {
    PVar(_, _)
    | PWild(_)
    | PLit(_, _)
    | PRange(_, _, _, _)
    | PArray(_, _, _, _)
    | PStruct(_, _, _) => [(p, [])]
    PLabel(q, l, inner) =>
      pat_alts(cxt, inner).map(a => (@parser.PLabel(q, l, a.0), a.1))
    PCon(q, c, impl_ps, expl_ps) => {
      let ni = impl_ps.map(ps => ps.length()).unwrap_or(0)
      let subs = impl_ps.unwrap_or([]) + expl_ps
      sub_alts(cxt, subs).map(a => {
        let (ps, al) = a
        let impl2 = impl_ps.map(_ => ps[0:ni].to_owned())
        (@parser.PCon(q, c, impl2, ps[ni:].to_owned()), al)
      })
    }
    PTuple(q, ps) => sub_alts(cxt, ps).map(a => (@parser.PTuple(q, a.0), a.1))
    POr(q, a, b) => {
      let xs = pat_alts(cxt, a)
      let ys = pat_alts(cxt, b)
      let vs = alt_vars(xs[0])
      for y in ys {
        if alt_vars(y) != vs {
          cxt
          .at(q)
          .fail(
            "the alternatives of an or-pattern must bind the same variables",
          )
        }
      }
      xs + ys
    }
    PAs(q, inner, x) =>
      pat_alts(cxt, inner).map(a => {
        let (ip, al) = a
        match ip {
          PWild(_) => (@parser.PVar(q, x), al)
          PVar(_, y) | PAs(_, _, y) => (ip, al + [(x, y)])
          _ => (@parser.PAs(q, ip, x), al)
        }
      })
  }
}

///|
/// The alternatives of a sequence of patterns (their cartesian product).
fn sub_alts(
  cxt : Cxt,
  ps : Array[@parser.Pat],
) -> Array[(Array[@parser.Pat], Array[(String, String)])] raise ElabError {
  let mut out : Array[(Array[@parser.Pat], Array[(String, String)])] = [
    ([], []),
  ]
  for p in ps {
    let alts = pat_alts(cxt, p)
    let next = []
    for prefix in out {
      for a in alts {
        next.push((prefix.0 + [a.0], prefix.1 + a.1))
      }
    }
    out = next
  }
  out
}

///|
/// The variables bound by an alternative, sorted.
fn alt_vars(a : (@parser.Pat, Array[(String, String)])) -> Array[String] {
  let out : Array[String] = a.1.map(x => x.0)
  pat_vars(a.0, out)
  out.sort()
  out
}

///|
fn pat_vars(p : @parser.Pat, out : Array[String]) -> Unit {
  match p {
    PVar(_, x) => out.push(x)
    PWild(_) | PLit(_, _) | PRange(_, _, _, _) => ()
    PStruct(_, fields, _) =>
      for f in fields {
        pat_vars(f.1, out)
      }
    PLabel(_, _, q) => pat_vars(q, out)
    PArray(_, before, rest, after) => {
      for q in before {
        pat_vars(q, out)
      }
      if rest is Some(Some(x)) {
        out.push(x)
      }
      for q in after {
        pat_vars(q, out)
      }
    }
    PCon(_, _, i, e) => {
      for q in i.unwrap_or([]) {
        pat_vars(q, out)
      }
      for q in e {
        pat_vars(q, out)
      }
    }
    PTuple(_, ps) =>
      for q in ps {
        pat_vars(q, out)
      }
    POr(_, a, _) => pat_vars(a, out)
    PAs(_, q, x) => {
      out.push(x)
      pat_vars(q, out)
    }
  }
}

///|
/// Expand the or-patterns of match arms into one arm per alternative (with
/// the same guard and body), and `y as x` into `y` with `let x = y`.
fn expand_arms(
  cxt : Cxt,
  arms : Array[@parser.Arm],
) -> Array[@parser.Arm] raise ElabError {
  let out : Array[@parser.Arm] = []
  for arm in arms {
    for a in pat_alts(cxt, arm.pat) {
      let (pat, al) = a
      let wrap = (e : @parser.Expr) => {
        if al.length() == 0 {
          return e
        }
        let p = e.pos()
        let stmts : Array[@parser.Stmt] = al.map(xy => {
          @parser.SLet(p, PVar(p, xy.0), None, EVar(p, xy.1))
        })
        stmts.push(SExpr(p, e))
        @parser.EBlock(p, stmts)
      }
      out.push({
        pos: arm.pos,
        pat,
        cond: arm.cond.map(wrap),
        rhs: arm.rhs.map(wrap),
      })
    }
  }
  out
}

///|
/// Does the `&&` chain of a condition test a pattern (`e is p`)?
fn has_is(c : @parser.Expr) -> Bool {
  match c {
    EIs(_, _, _) => true
    EBin(_, "&&", a, b) => has_is(a) || has_is(b)
    _ => false
  }
}

///|
fn conjuncts(c : @parser.Expr, out : Array[@parser.Expr]) -> Unit {
  match c {
    EBin(_, "&&", a, b) => {
      conjuncts(a, out)
      conjuncts(b, out)
    }
    _ => out.push(c)
  }
}

///|
/// `if c { t } else { f }` for a condition `c` with pattern tests: each
/// `e is p` becomes a match whose first arm continues with the rest of the
/// chain (so the variables of `p` are in scope there and in `t`), the
/// boolean conditions after it being its guard. `f` is repeated, once per
/// pattern test.
fn cond_expr(
  c : @parser.Expr,
  t : @parser.Expr,
  f : @parser.Expr,
) -> @parser.Expr {
  let cs0 : Array[@parser.Expr] = []
  conjuncts(c, cs0)
  // array and range patterns become tests
  let cs : Array[@parser.Expr] = []
  for x in cs0 {
    expand_is(x, cs)
  }
  // the boolean conditions from `i` to the next pattern test
  let bools = (i : Int32) => {
    let mut k = i
    let mut e : @parser.Expr? = None
    while k < cs.length() && !(cs[k] is EIs(_, _, _)) {
      e = match e {
        None => Some(cs[k])
        Some(a) => Some(EBin(cs[k].pos(), "&&", a, cs[k]))
      }
      k = k + 1
    }
    (e, k)
  }
  fn go(i : Int32) -> @parser.Expr {
    if i >= cs.length() {
      return t
    }
    match cs[i] {
      EIs(p, e, pat) => {
        let (g, k) = bools(i + 1)
        EMatch(p, e, None, [
          { pos: p, pat, cond: g, rhs: Some(go(k)), },
          { pos: p, pat: PWild(p), cond: None, rhs: Some(f), },
        ])
      }
      other => {
        let (g, k) = bools(i)
        EIf(other.pos(), g.unwrap(), go(k), Some(f))
      }
    }
  }

  go(0)
}

///|
/// `try body catch { arms } noraise { ok }`: the handlers and the `noraise`
/// arms run outside of the `try`, so
/// `match (try { Ok(body) } catch { p => Err(rhs) }) { Ok(v) => match v { ok }; Err(r) => r }`.
fn try_noraise(
  p : Pos,
  body : @parser.Expr,
  arms : Array[@parser.Arm],
  ok : Array[@parser.Arm],
) -> @parser.Expr {
  let v = fresh_name_gen("__ok")
  let r = fresh_name_gen("__err")
  let wrap = (c : String, e : @parser.Expr) => {
    @parser.EApp(e.pos(), EVar(e.pos(), "Result::" + c), None, Some([e]))
  }
  let handlers = arms.map(a => { ..a, rhs: a.rhs.map(e => wrap("Err", e)), })
  EMatch(p, ETry(p, wrap("Ok", body), handlers, None), None, [
    {
      pos: p,
      pat: PCon(p, "Result::Ok", None, [PVar(p, v)]),
      cond: None,
      rhs: Some(EMatch(p, EVar(p, v), None, ok)),
    },
    {
      pos: p,
      pat: PCon(p, "Result::Err", None, [PVar(p, r)]),
      cond: None,
      rhs: Some(EVar(p, r)),
    },
  ])
}

///|
/// The expansion of an expression that is sugar for another.
fn sugar(e : @parser.Expr) -> @parser.Expr? {
  match e {
    EIf(p, c, t, el) if has_is(c) =>
      Some(cond_expr(c, t, el.unwrap_or(ELit(p, LUnit))))
    EIs(p, _, _) | EBin(p, "&&", _, _) if has_is(e) =>
      Some(cond_expr(e, ELit(p, LBool(true)), ELit(p, LBool(false))))
    ETry(p, body, arms, Some(ok)) => Some(try_noraise(p, body, arms, ok))
    _ => None
  }
}

///|
/// Does a pattern contain an array or a range pattern?
fn has_special(p : @parser.Pat) -> Bool {
  match p {
    PArray(_, _, _, _) | PRange(_, _, _, _) => true
    PCon(_, _, i, e) =>
      i.unwrap_or([]).iter().any(has_special) || e.iter().any(has_special)
    PTuple(_, ps) => ps.iter().any(has_special)
    POr(_, a, b) => has_special(a) || has_special(b)
    PAs(_, q, _) => has_special(q)
    _ => false
  }
}

///|
/// Does a pattern contain an array pattern?
fn has_array(p : @parser.Pat) -> Bool {
  match p {
    PArray(_, _, _, _) => true
    PCon(_, _, i, e) =>
      i.unwrap_or([]).iter().any(has_array) || e.iter().any(has_array)
    PTuple(_, ps) => ps.iter().any(has_array)
    POr(_, a, b) => has_array(a) || has_array(b)
    PAs(_, q, _) => has_array(q)
    _ => false
  }
}

///|
/// Replace the array and range patterns in `p` by fresh variables, recorded
/// in `out` with the patterns they must match.
fn lift_special(
  p : @parser.Pat,
  out : Array[(String, @parser.Pat)],
) -> @parser.Pat {
  let go = (q : @parser.Pat) => lift_special(q, out)
  match p {
    PArray(q, _, _, _) | PRange(q, _, _, _) => {
      let x = fresh_name_gen("__pat")
      out.push((x, p))
      PVar(q, x)
    }
    PAs(q, PArray(_, _, _, _) as inner, x)
    | PAs(q, PRange(_, _, _, _) as inner, x) => {
      out.push((x, inner))
      PVar(q, x)
    }
    PCon(q, c, i, e) => PCon(q, c, i.map(xs => xs.map(go)), e.map(go))
    PTuple(q, ps) => PTuple(q, ps.map(go))
    PAs(q, inner, x) => PAs(q, go(inner), x)
    _ => p
  }
}

///|
fn and_all(p : Pos, cs : Array[@parser.Expr]) -> @parser.Expr {
  match cs {
    [] => ELit(p, LBool(true))
    [c, ..] => {
      let mut e = c
      for k = 1; k < cs.length(); k = k + 1 {
        e = EBin(p, "&&", e, cs[k])
      }
      e
    }
  }
}

///|
/// The tests that the variable `x` matches the array or range pattern `p`
/// (the elements of an array are tested with `is`; `..rest` is bound with
/// `slice`).
fn special_tests(x : String, p : @parser.Pat) -> Array[@parser.Expr] {
  match p {
    PRange(q, lo, hi, incl) => {
      let out : Array[@parser.Expr] = []
      if lo is Some(l) {
        out.push(EBin(q, ">=", EVar(q, x), ELit(q, l)))
      }
      if hi is Some(h) {
        out.push(EBin(q, if incl { "<=" } else { "<" }, EVar(q, x), ELit(q, h)))
      }
      out
    }
    PArray(q, before, rest, after) => {
      let len : @parser.Expr = EMethod(q, EVar(q, x), "length", None, [])
      let n = before.length() + after.length()
      let lit = (k : Int32) => @parser.ELit(q, LInt(k))
      let out : Array[@parser.Expr] = [
        EBin(q, if rest is None { "==" } else { ">=" }, len, lit(n)),
      ]
      let at = (i : @parser.Expr) => {
        @parser.EApp(q, EVar(q, x), Some([i]), None)
      }
      for k = 0; k < before.length(); k = k + 1 {
        if !(before[k] is PWild(_)) {
          out.push(EIs(q, at(lit(k)), before[k]))
        }
      }
      for k = 0; k < after.length(); k = k + 1 {
        if !(after[k] is PWild(_)) {
          let i : @parser.Expr = EBin(q, "-", len, lit(after.length() - k))
          out.push(EIs(q, at(i), after[k]))
        }
      }
      if rest is Some(Some(r)) {
        let slice : @parser.Expr = EMethod(q, EVar(q, x), "slice", None, [
          lit(before.length()),
          EBin(q, "-", len, lit(after.length())),
        ])
        out.push(EIs(q, slice, PVar(q, r)))
      }
      out
    }
    _ => []
  }
}

///|
/// A conjunct of a condition, with its array and range patterns turned into
/// tests.
fn expand_is(c : @parser.Expr, out : Array[@parser.Expr]) -> Unit {
  match c {
    EIs(q, e, p) if has_special(p) => {
      let lifted : Array[(String, @parser.Pat)] = []
      let p2 = lift_special(p, lifted)
      out.push(EIs(q, e, p2))
      for l in lifted {
        for t in special_tests(l.0, l.1) {
          expand_is(t, out)
        }
      }
    }
    _ => out.push(c)
  }
}

///|
/// Arms with array or range patterns, or `is` in their guards. Ranges only:
/// they become guards. Otherwise the whole match is a chain of tests, in
/// order (`None`: no such arm).
fn special_match(
  p : Pos,
  scr : @parser.Expr,
  arms : Array[@parser.Arm],
) -> Result[Array[@parser.Arm], @parser.Expr]? {
  let guard_is = (a : @parser.Arm) => a.cond.map(has_is).unwrap_or(false)
  if !arms.iter().any(a => has_special(a.pat) || guard_is(a)) {
    return None
  }
  if !arms.iter().any(a => has_array(a.pat) || guard_is(a)) {
    return Some(
      Ok(
        arms.map(a => {
          let lifted : Array[(String, @parser.Pat)] = []
          let pat = lift_special(a.pat, lifted)
          let tests : Array[@parser.Expr] = []
          for l in lifted {
            for t in special_tests(l.0, l.1) {
              tests.push(t)
            }
          }
          match a.cond {
            Some(g) => tests.push(g)
            None => ()
          }
          let cond = if tests.length() == 0 {
            None
          } else {
            Some(and_all(a.pos, tests))
          }
          { ..a, pat, cond, }
        }),
      ),
    )
  }
  // the chain: the first arm whose pattern and guard hold gives the value
  let s = fresh_name_gen("__scrut")
  let r = fresh_name_gen("__result")
  let stmts : Array[@parser.Stmt] = [
    SLet(p, PVar(p, s), None, scr),
    SLetMut(p, r, None, EVar(p, "Option::None")),
  ]
  for a in arms {
    guard a.rhs is Some(rhs) else { continue }
    let q = a.pos
    let check_arm = and_all(
      q,
      [
        EIs(q, EVar(q, r), PCon(q, "Option::None", None, [])),
        EIs(q, EVar(q, s), a.pat),
        ..a.cond.map(g => [g]).unwrap_or([]),
      ],
    )
    let set : @parser.Expr = EBlock(q, [
      SAssign(
        q,
        EVar(q, r),
        "=",
        EApp(q, EVar(q, "Option::Some"), None, Some([rhs])),
      ),
    ])
    stmts.push(SExpr(q, cond_expr(check_arm, set, ELit(q, LUnit))))
  }
  let v = fresh_name_gen("__v")
  stmts.push(
    SExpr(
      p,
      EMatch(p, EVar(p, r), None, [
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
          rhs: Some(
            EApp(
              p,
              EVar(p, "abort"),
              None,
              Some([ELit(p, LStr("no case of the match applies"))]),
            ),
          ),
        },
      ]),
    ),
  )
  Some(Err(EBlock(p, stmts)))
}
