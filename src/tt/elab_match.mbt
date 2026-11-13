///|
/// Dependent pattern matching.
priv struct PatOut {
  cxt : Cxt
  pat : CPat
  slot : Int32
  conflict : Bool
  /// For constructor patterns: the constructor's return type.
  ret_ty : Val?
}

///|
fn nat_pat(p : Pos, n : Int32) -> @parser.Pat {
  if n == 0 {
    PCon(p, "Nat::Z", None, [])
  } else {
    PCon(p, "Nat::S", None, [nat_pat(p, n - 1)])
  }
}

///|
/// Check a pattern against `ty`. The pattern's slot is defined as `scrut`
/// when given (variable patterns at the top of a match); for constructor
/// patterns `refine_scrut` additionally unifies the scrutinee with the
/// constructor value. `index_unify` unifies the indices of `ty` with those of
/// the constructor.
fn check_pat(
  cxt0 : Cxt,
  p : @parser.Pat,
  ty0 : Val,
  index_unify : Bool,
  scrut : Val?,
  refine_scrut : Bool,
  as_name~ : String = "_",
) -> PatOut raise ElabError {
  let cxt = cxt0.at(p.pos())
  let ty = force(cxt.subst(ty0))
  let simple = (x : String, cp : CPat) => {
    let c2 = match scrut {
      Some(v) => cxt.define_local(x, ty, v)
      None => cxt.bind(x, ty)
    }
    { cxt: c2, pat: cp, slot: cxt.lvl, conflict: false, ret_ty: None, }
  }
  match p {
    PVar(_, x) => simple(x, CPVar(x))
    PWild(_) => simple("_", CPWild)
    // `p as x`: `x` names the slot of `p` (variables are handled by
    // `expand_arms`)
    PAs(_, PWild(q), x) =>
      check_pat(cxt, PVar(q, x), ty, index_unify, scrut, refine_scrut)
    PAs(q, PVar(_, _) | PAs(_, _, _), _) =>
      cxt.at(q).fail("a variable cannot be named twice here")
    PAs(_, inner, x) =>
      check_pat(cxt, inner, ty, index_unify, scrut, refine_scrut, as_name=x)
    POr(q, _, _) => cxt.at(q).fail("an or-pattern cannot be used here")
    PLabel(q, _, _) =>
      cxt.at(q).fail("a labelled pattern is an argument of a constructor")
    PStruct(q, fields, open) =>
      match ty {
        VData(d, _) =>
          check_pat(
            cxt,
            struct_pattern(cxt.at(q), d, fields, open),
            ty,
            index_unify,
            scrut,
            refine_scrut,
            as_name~,
          )
        _ =>
          cxt
          .at(q)
          .fail("cannot match a struct pattern against " + cxt.show(ty))
      }
    PArray(q, _, _, _) | PRange(q, _, _, _) =>
      cxt
      .at(q)
      .fail("array and range patterns can only be used in `match` and `is`")
    PLit(q, LInt(n)) if head_name(ty) == Some("Nat") =>
      if n < 0 {
        cxt.fail("negative natural number")
      } else {
        check_pat(
          cxt,
          nat_pat(q, n),
          ty,
          index_unify,
          scrut,
          refine_scrut,
          as_name~,
        )
      }
    PLit(_, l) => {
      cxt.unify(ty, lit_type(l))
      let out = simple(as_name, CPLit(l))
      // in the clause, the scrutinee is the literal; so is the slot of a
      // sub-pattern, which later fields of the constructor may mention (as
      // for constructor patterns)
      let v = match scrut {
        Some(v) if refine_scrut && !is_mut_var(out.cxt, v) => Some(v)
        Some(_) => None
        None => Some(v_var(out.slot))
      }
      match v {
        Some(v) =>
          match out.cxt.refine([(v, VLit(l))]) {
            ROk(c2) => { ..out, cxt: c2, }
            RConflict => { ..out, pat: CPWild, conflict: true, }
            RStuck(_) => out
          }
        None => out
      }
    }
    PTuple(q, ps) =>
      check_pat(
        cxt,
        PCon(q, "Tuple" + ps.length().to_string() + "::mk", None, ps),
        ty,
        index_unify,
        scrut,
        refine_scrut,
        as_name~,
      )
    PCon(cpos, name, impl_ps, expl_ps) => {
      let (d, sp) = match ty {
        VData(d, sp) => (d, sp)
        _ =>
          cxt.fail(
            "cannot match constructor " + name + " against type " + cxt.show(ty),
          )
      }
      // the tuple struct `P(a, b)`
      let name = if name == d && tuple_structs.contains(d) {
        d + "::mk"
      } else {
        name
      }
      let c = resolve_name(cxt, name, false, Some(d))
      record_global(cpos, name, c)
      let ci = match con_info(c) {
        Some(ci) if ci.data == d => ci
        _ => cxt.fail(name + " is not a constructor of " + d)
      }
      let impl_ps = impl_ps.unwrap_or([])
      // `C(p, ..)`
      let open = expl_ps.iter().any(q => q is PLabel(_, "..", _))
      let expl_ps = expl_ps.filter(q => !(q is PLabel(_, "..", _)))
      // labelled fields go to their positions; omitted ones match anything
      let expl_ps = if expl_ps.iter().any(q => q is PLabel(_, _, _)) {
        let infos = st.labels.get(c).unwrap_or([])
        let positional = expl_ps.filter(q => !(q is PLabel(_, _, _)))
        let mut next = 0
        let out : Array[@parser.Pat] = []
        for info in infos {
          match info {
            LReq(l) | LOpt(l) | LDefault(l, _) =>
              out.push(
                match
                  expl_ps
                  .iter()
                  .find_first(q => q is PLabel(_, l2, _) && l2 == l) {
                  Some(PLabel(_, _, q)) => q
                  _ => PWild(cpos)
                },
              )
            LPos => {
              if next < positional.length() {
                out.push(positional[next])
              }
              next = next + 1
            }
          }
        }
        for q in expl_ps {
          if q is PLabel(lp, l, _) &&
            !infos
            .iter()
            .any(i => i is (LReq(l2) | LOpt(l2) | LDefault(l2, _)) && l2 == l) {
            cxt.at(lp).fail(name + " has no field labelled " + l)
          }
        }
        out
      } else {
        expl_ps
      }
      let expl_ps = if open && expl_ps.length() < ci.nargs - ci.nimpl {
        expl_ps +
        Array::make(ci.nargs - ci.nimpl - expl_ps.length(), PWild(cpos))
      } else {
        expl_ps
      }
      if impl_ps.length() > ci.nimpl {
        cxt.fail("too many implicit arguments in pattern " + name)
      }
      if expl_ps.length() != ci.nargs - ci.nimpl {
        cxt.fail(
          "constructor " +
          name +
          " takes " +
          (ci.nargs - ci.nimpl).to_string() +
          " argument(s)",
        )
      }
      let s = cxt.lvl
      let mut cur = cxt.bind(as_name, ty)
      let mut cty = global_entry(cxt, c).vty
      let args : Spine = []
      for k = 0; k < ci.nparams; k = k + 1 {
        match force(cty) {
          VPi(_, i, _, _, cl) => {
            args.push((sp[k].0, i))
            cty = inst(cl, sp[k].0)
          }
          _ => cxt.fail("bad constructor type")
        }
      }
      let subs = []
      for k = 0; k < ci.nargs; k = k + 1 {
        if k < ci.nimpl {
          subs.push(
            if k < impl_ps.length() {
              impl_ps[k]
            } else {
              PWild(p.pos())
            },
          )
        } else {
          subs.push(expl_ps[k - ci.nimpl])
        }
      }
      let cps : Array[CPat] = []
      for k = 0; k < ci.nargs; k = k + 1 {
        match force(cty) {
          VPi(_, i, _, a, cl) => {
            let out = check_pat(cur, subs[k], a, true, None, false)
            if out.conflict {
              return {
                cxt: out.cxt,
                pat: CPWild,
                slot: s,
                conflict: true,
                ret_ty: None,
              }
            }
            cur = out.cxt
            cps.push(out.pat)
            args.push((v_var(out.slot), i))
            cty = inst(cl, v_var(out.slot))
          }
          _ => cxt.fail("bad constructor type")
        }
      }
      let ret = force(cur.subst(cty))
      let cv = VCon(c, args)
      let eqs = [(v_var(s), cv)]
      if index_unify {
        match ret {
          VData(_, rsp) =>
            for k = ci.nparams; k < sp.length() && k < rsp.length(); k = k + 1 {
              eqs.push((sp[k].0, rsp[k].0))
            }
          _ => ()
        }
      }
      match cur.refine(eqs) {
        ROk(c2) => cur = c2
        RConflict =>
          return {
            cxt: cur,
            pat: CPWild,
            slot: s,
            conflict: true,
            ret_ty: None,
          }
        RStuck(msg) =>
          cxt.fail(
            "cannot decide whether " +
            name +
            " matches " +
            cxt.show(ty) +
            " (" +
            msg +
            "); use `match e as x in T return R`",
          )
      }
      if refine_scrut {
        match scrut {
          Some(v) if !is_mut_var(cur, v) =>
            match cur.refine([(v, v_var(s))]) {
              ROk(c2) => cur = c2
              RConflict =>
                return {
                  cxt: cur,
                  pat: CPWild,
                  slot: s,
                  conflict: true,
                  ret_ty: None,
                }
              RStuck(_) => ()
            }
          _ => ()
        }
      }
      {
        cxt: cur,
        pat: CPCon(c, cps),
        slot: s,
        conflict: false,
        ret_ty: Some(ret),
      }
    }
  }
}

///|
fn is_subsingleton(cxt : Cxt, d : String) -> Bool raise ElabError {
  let di = data_info(d).unwrap()
  if di.cons.length() > 1 {
    return false
  }
  for c in di.cons {
    let ci = con_info(c).unwrap()
    let mut ty = global_entry(cxt, c).vty
    let mut ts : LTypes = []
    for k = 0; k < ci.nparams + ci.nargs; k = k + 1 {
      match force(ty) {
        VPi(_, _, _, a, cl) => {
          if k >= ci.nparams && !is_prop_type(ts, a) {
            return false
          }
          let v = v_var(ts.length())
          ts = concat(ts, [Some(a)])
          ty = inst(cl, v)
        }
        _ => break
      }
    }
  }
  true
}

///|
/// Does a pattern look at the constructor of the value?
fn splits(p : @parser.Pat) -> Bool {
  match p {
    PCon(_, _, _, _) | PTuple(_, _) | PLit(_, _) => true
    PAs(_, q, _) => splits(q)
    PArray(_, _, _, _) | PRange(_, _, _, _) | PStruct(_, _, _) => true
    PLabel(_, _, q) => splits(q)
    POr(_, a, b) => splits(a) || splits(b)
    PVar(_, _) | PWild(_) => false
  }
}

///|
fn check_prop_elim(
  cxt : Cxt,
  tys : Array[Val],
  arms : Array[Array[@parser.Pat]],
  goal : Val,
) -> Unit raise ElabError {
  for k = 0; k < tys.length(); k = k + 1 {
    match force(tys[k]) {
      VData(d, _) =>
        match data_info(d) {
          Some(di) if di.is_prop => {
            let splits = arms.iter().any(ps => splits(ps[k]))
            if splits &&
              !is_prop_type(cxt.ltypes(), goal) &&
              !is_subsingleton(cxt, d) {
              cxt.fail(
                "cannot eliminate a proof of " +
                d +
                " into a type that is not a proposition",
              )
            }
          }
          _ => ()
        }
      _ => ()
    }
  }
}

///|
fn elab_match(
  cxt : Cxt,
  scr : @parser.Expr,
  ret : @parser.MatchRet?,
  arms0 : Array[@parser.Arm],
  goal : Val?,
  with_ok~ : Bool = true,
) -> (Tm, Val) raise ElabError {
  let arms = expand_arms(cxt, arms0)
  // array and range patterns, `is` in guards (see sugar.mbt)
  let arms = match special_match(cxt.pos, scr, arms) {
    None => arms
    Some(Ok(arms2)) => arms2
    Some(Err(chain)) =>
      if ret is Some(_) {
        cxt.fail("array patterns cannot be used with a `return` clause")
      } else {
        return match goal {
          Some(g) => (check(cxt, chain, g), g)
          None => infer(cxt, chain)
        }
      }
  }
  // `match (a, b) { (p, q) => ... }` matches on several scrutinees
  let scrs = match scr {
    ETuple(_, es) if ret is None &&
      arms
      .iter()
      .all(a => {
        match a.pat {
          PTuple(_, ps) => ps.length() == es.length()
          PWild(_) => true
          _ => false
        }
      }) => es
    _ => [scr]
  }
  let pats = arms.map(a => {
    match a.pat {
      PTuple(_, ps) if scrs.length() > 1 => ps
      PWild(q) if scrs.length() > 1 => scrs.map(_ => @parser.PWild(q))
      p => [p]
    }
  })
  match ret {
    Some(mr) => elab_match_ret(cxt, scr, mr, arms, goal)
    None => {
      let goal = match goal {
        Some(g) => g
        None => cxt.eval(cxt.fresh_meta())
      }
      let sts = scrs.map(s => infer_ins(cxt, s))
      // the instances of the scrutinees (`DecEq::deq(c, c)`), so that they
      // are found in the goal
      solve_pending(false)
      let svals = sts.map(x => cxt.eval(x.0))
      // a scrutinee that is not a variable but occurs in the goal (of a
      // proof): abstract it, and match on a variable instead (`with`)
      for i = 0; i < scrs.length() && with_ok; i = i + 1 {
        match with_motive(cxt, svals[i], goal) {
          Some((motive, hyps)) => {
            let w = "%with" + cxt.lvl.to_string()
            // the expression, then the hypotheses about it, abstracted (they
            // shadow the originals)
            let mut c2 = cxt.bind(w, sts[i].1)
            for j = 0; j < hyps.length(); j = j + 1 {
              let (l, hty) = hyps[j]
              c2 = c2.bind(cxt.names[l], c2.eval(tm_shift(hty, j, 0)))
            }
            let k = hyps.length()
            let new_scrs = scrs.mapi((n, e) => {
              if n == i {
                @parser.EVar(e.pos(), w)
              } else {
                e
              }
            })
            let scr2 = if new_scrs.length() > 1 {
              @parser.ETuple(scr.pos(), new_scrs)
            } else {
              new_scrs[0]
            }
            let snap = snapshot_metas()
            let res : Result[(Tm, Val), ElabError] = Ok(
              elab_match(
                c2,
                scr2,
                None,
                arms0,
                Some(c2.eval(tm_shift(motive, k, 0))),
              ),
            ) catch {
              e => Err(e)
            }
            match res {
              Ok((body, _)) => {
                let mut f = body
                for j = k - 1; j >= 0; j = j - 1 {
                  f = Lam(cxt.names[hyps[j].0], Expl, true, f)
                }
                f = App(Lam(w, Expl, true, f), sts[i].0, Expl)
                for h in hyps {
                  f = App(f, Var(cxt.lvl - 1 - h.0), Expl)
                }
                return (f, goal)
              }
              // without the abstraction
              Err(e) => {
                restore_metas(snap)
                return elab_match(
                  cxt,
                  scr,
                  None,
                  arms0,
                  Some(goal),
                  with_ok=false,
                ) catch {
                  _ => raise e
                }
              }
            }
          }
          None => ()
        }
      }
      let clauses : Array[Clause] = []
      for j = 0; j < arms.length(); j = j + 1 {
        let arm = arms[j]
        let mut cur = cxt.at(arm.pos)
        let cps : Array[CPat] = []
        let mut conflict = false
        for i = 0; i < scrs.length(); i = i + 1 {
          let out = check_pat(
            cur,
            pats[j][i],
            sts[i].1,
            true,
            Some(svals[i]),
            true,
          )
          cur = out.cxt
          if out.conflict {
            conflict = true
            break
          }
          cps.push(out.pat)
        }
        match (conflict, arm.rhs) {
          (true, _) => ()
          (false, None) =>
            if arm.cond is Some(_) {
              cur.fail("an impossible pattern cannot have a guard")
            } else if !has_empty_var(cur) {
              cur.fail("this pattern is not impossible")
            }
          (false, Some(rhs)) => {
            let cond = arm.cond.map(g => check(cur, g, bool_ty()))
            let body = check(cur, rhs, cur.subst(goal))
            clauses.push({ pats: cps, cond, body, })
          }
        }
      }
      check_prop_elim(cxt, sts.map(x => x.1), pats, goal)
      // coverage, generalising scrutinees that are not variables
      let mut cc = cxt
      let problem : Array[Val] = []
      for i = 0; i < scrs.length(); i = i + 1 {
        match force(cxt.subst(svals[i])) {
          VRigid(x, []) if cxt.bound[x] => problem.push(svals[i])
          // a known value (a refined variable): its clauses that cannot
          // match were dropped
          VLit(_) | VCon(_, _) as w => problem.push(w)
          _ => {
            problem.push(v_var(cc.lvl))
            cc = cc.bind("_", sts[i].1)
          }
        }
      }
      coverage(cc, problem, clauses)
      (Match(sts.map(x => x.0), clauses), goal)
    }
  }
}

///|
/// Flatten the arguments of `D[..](..)(..)` in order.
fn flat_args(e : @parser.Expr, out : Array[@parser.Expr]) -> Unit {
  match e {
    EApp(_, f, i, x) => {
      flat_args(f, out)
      match i {
        Some(xs) =>
          for a in xs {
            out.push(a)
          }
        None => ()
      }
      match x {
        Some(xs) =>
          for a in xs {
            out.push(a)
          }
        None => ()
      }
    }
    _ => ()
  }
}

///|
fn elab_match_ret(
  cxt : Cxt,
  scr : @parser.Expr,
  mr : @parser.MatchRet,
  arms : Array[@parser.Arm],
  goal : Val?,
) -> (Tm, Val) raise ElabError {
  let (ts, a) = infer_ins(cxt, scr)
  let sval = cxt.eval(ts)
  let (d, sp) = match force(a) {
    VData(d, sp) => (d, sp)
    other => cxt.fail("cannot match on a value of type " + cxt.show(other))
  }
  let di = data_info(d).unwrap()
  let np = di.nparams
  // index variables and the `as` variable
  let names : Array[String] = []
  match mr.in_ty {
    Some(t) => {
      let args = []
      flat_args(t, args)
      let k0 = args.length() - di.nindices
      if k0 < 0 {
        cxt.fail("the `in` clause must name all indices of " + d)
      }
      for k = k0; k < args.length(); k = k + 1 {
        names.push(
          match args[k] {
            EVar(_, x) => x
            _ => "_"
          },
        )
      }
    }
    None =>
      for _ in 0..<di.nindices {
        names.push("_")
      }
  }
  let mut cm = cxt
  let mut dty = global_entry(cxt, d).vty
  let tsp : Spine = []
  for k = 0; k < np + di.nindices; k = k + 1 {
    match force(dty) {
      VPi(_, i, _, dom, cl) =>
        if k < np {
          tsp.push((sp[k].0, i))
          dty = inst(cl, sp[k].0)
        } else {
          let v = v_var(cm.lvl)
          cm = cm.bind(names[k - np], dom)
          tsp.push((v, i))
          dty = inst(cl, v)
        }
      _ => cxt.fail("bad datatype")
    }
  }
  cm = cm.bind(mr.as_name.unwrap_or("_"), VData(d, tsp))
  let r = match (mr.ret, goal) {
    (Some(r), _) => check_type(cm, r)
    (None, Some(g)) => quote(cm.lvl, g)
    (None, None) =>
      cxt.fail("cannot infer the type of this match; add `return`")
  }
  let idx_scrut = sp[np:].to_owned().map(x => x.0)
  let res_ty = eval(concat(concat(cxt.env, idx_scrut), [sval]), r)
  match goal {
    Some(g) => cxt.unify(g, res_ty)
    None => ()
  }
  let clauses : Array[Clause] = []
  let arms = expand_arms(cxt, arms)
  for arm in arms {
    let out = check_pat(cxt.at(arm.pos), arm.pat, a, false, Some(sval), false)
    if out.conflict {
      continue
    }
    let rhs = match arm.rhs {
      Some(x) => x
      None => out.cxt.fail("this pattern is not impossible")
    }
    let (idx, xv) = match out.ret_ty {
      Some(VData(_, rsp)) =>
        (rsp[np:].to_owned().map(x => x.0), v_var(out.slot))
      _ => (idx_scrut, sval)
    }
    let env = concat(concat(out.cxt.env[0:cxt.lvl].to_owned(), idx), [xv])
    let g = out.cxt.subst(eval(env, r))
    let cond = arm.cond.map(e => check(out.cxt, e, bool_ty()))
    clauses.push({ pats: [out.pat], cond, body: check(out.cxt, rhs, g), })
  }
  check_prop_elim(cxt, [a], arms.map(x => [x.pat]), res_ty)
  // coverage over a generalised scrutinee
  let mut cc = cxt
  let gsp : Spine = []
  let mut dty = global_entry(cxt, d).vty
  for k = 0; k < np + di.nindices; k = k + 1 {
    match force(dty) {
      VPi(_, i, _, dom, cl) =>
        if k < np {
          gsp.push((sp[k].0, i))
          dty = inst(cl, sp[k].0)
        } else {
          let v = v_var(cc.lvl)
          cc = cc.bind("_", dom)
          gsp.push((v, i))
          dty = inst(cl, v)
        }
      _ => ()
    }
  }
  let x = v_var(cc.lvl)
  cc = cc.bind("_", VData(d, gsp))
  coverage(cc, [x], clauses)
  (Match([ts], clauses), res_ty)
}

// ---------------------------------------------------------------------------
// Coverage

///|
priv enum Cov {
  CYes
  CNo
  CBlocked(Int32)
  CUnknown
}

///|
fn cov_pat(cxt : Cxt, p : CPat, v : Val) -> Cov {
  let w = force(cxt.subst(v))
  match p {
    CPVar(_) | CPWild => CYes
    CPCon(c, ps) =>
      match w {
        VCon(c2, sp) => {
          if c2 != c {
            return CNo
          }
          let np = nparams_of(c)
          let rs : Array[Cov] = []
          for k = 0; k < ps.length() && np + k < sp.length(); k = k + 1 {
            rs.push(cov_pat(cxt, ps[k], sp[np + k].0))
          }
          cov_combine(rs)
        }
        VRigid(l, []) if cxt.bound[l] => CBlocked(l)
        _ => CUnknown
      }
    CPLit(l) =>
      match (w, l) {
        (VLit(l2), _) => if l == l2 { CYes } else { CNo }
        (_, LUnit) => CYes
        (VRigid(x, []), LBool(_)) if cxt.bound[x] => CBlocked(x)
        _ => CNo
      }
  }
}

///|
fn cov_combine(rs : Array[Cov]) -> Cov {
  if rs.iter().any(r => r is CNo) {
    return CNo
  }
  for r in rs {
    match r {
      CYes => ()
      other => return other
    }
  }
  CYes
}

///|
fn split_var(cxt : Cxt, l : Int32) -> Array[Cxt]? raise ElabError {
  let ty = force(cxt.subst(cxt.types[l]))
  match ty {
    VData("Bool", _) =>
      Some([
        cxt.define_var(l, VLit(LBool(true))),
        cxt.define_var(l, VLit(LBool(false))),
      ])
    VData(d, sp) =>
      match data_info(d) {
        Some(di) if !di.builtin => {
          let out : Array[Cxt] = []
          for c in di.cons {
            let ci = con_info(c).unwrap()
            let mut cty = global_entry(cxt, c).vty
            let args : Spine = []
            let mut cur = cxt
            for k = 0; k < ci.nparams + ci.nargs; k = k + 1 {
              match force(cty) {
                VPi(_, i, _, a, cl) =>
                  if k < ci.nparams {
                    args.push((sp[k].0, i))
                    cty = inst(cl, sp[k].0)
                  } else {
                    let v = v_var(cur.lvl)
                    cur = cur.bind("_", a)
                    args.push((v, i))
                    cty = inst(cl, v)
                  }
                _ => ()
              }
            }
            let cv = VCon(c, args)
            let eqs = [(v_var(l), cv)]
            match force(cur.subst(cty)) {
              VData(_, rsp) =>
                for k = ci.nparams
                    k < sp.length() && k < rsp.length()
                    k = k + 1 {
                  eqs.push((sp[k].0, rsp[k].0))
                }
              _ => ()
            }
            match cur.refine(eqs) {
              ROk(c2) => out.push(c2)
              RConflict => ()
              RStuck(_) =>
                match cur.refine([(v_var(l), cv)]) {
                  ROk(c2) => out.push(c2)
                  _ => ()
                }
            }
          }
          Some(out)
        }
        _ => None
      }
    _ => None
  }
}

///|
fn cover(
  cxt : Cxt,
  problem : Array[Val],
  clauses : Array[Clause],
  missing : Array[String],
  depth : Int32,
) -> Unit raise ElabError {
  let show_problem = () => {
    let s = problem.map(v => cxt.show(cxt.subst(v)))
    if s.length() == 1 {
      s[0]
    } else {
      "(" + s.join(", ") + ")"
    }
  }
  if depth > 64 {
    missing.push(show_problem() + " (too deep)")
    return
  }
  for cl in clauses {
    // a guarded clause may not match
    if cl.cond is Some(_) {
      continue
    }
    let rs : Array[Cov] = []
    for k = 0; k < problem.length(); k = k + 1 {
      rs.push(cov_pat(cxt, cl.pats[k], problem[k]))
    }
    match cov_combine(rs) {
      CYes => return
      CNo => continue
      CBlocked(l) =>
        match split_var(cxt, l) {
          Some(cases) => {
            for c2 in cases {
              cover(c2, problem, clauses, missing, depth + 1)
            }
            return
          }
          None => {
            missing.push(show_problem())
            return
          }
        }
      CUnknown => {
        missing.push(show_problem() + " (cannot decide)")
        return
      }
    }
  }
  if !has_empty_var(cxt) {
    missing.push(show_problem())
  }
}

///|
/// Does some bound variable have a type without possible constructors (like
/// `Fin(0)`)? Then the context is contradictory.
fn has_empty_var(cxt : Cxt) -> Bool raise ElabError {
  for l = 0; l < cxt.lvl; l = l + 1 {
    if cxt.bound[l] {
      match force(cxt.subst(cxt.types[l])) {
        VData(d, _) if d != "Bool" =>
          match split_var(cxt, l) {
            Some([]) => return true
            _ => ()
          }
        _ => ()
      }
    }
  }
  false
}

///|
fn coverage(
  cxt : Cxt,
  problem : Array[Val],
  clauses : Array[Clause],
) -> Unit raise ElabError {
  let missing : Array[String] = []
  cover(cxt, problem, clauses, missing, 0)
  if missing.length() > 0 {
    cxt.fail(
      "match is not exhaustive; missing case(s):\n  " + missing.join("\n  "),
    )
  }
}

// ---------------------------------------------------------------------------
// try / catch

///|
fn elab_try(
  cxt : Cxt,
  body : @parser.Expr,
  arms : Array[@parser.Arm],
  goal : Val?,
) -> (Tm, Val) raise ElabError {
  // handlers of effects (see effects.mbt)
  if arms.iter().any(a => arm_op(a) is Some(_)) {
    return elab_handle(cxt, cxt.pos, body, arms, goal)
  }
  let bc = { ..cxt, can_raise: true, }
  let (tb, ty) = match goal {
    Some(g) => (check(bc, body, g), g)
    None => infer_ins(bc, body)
  }
  let clauses : Array[Clause] = []
  for arm in expand_arms(cxt, arms) {
    let c = cxt.at(arm.pos)
    let mut head = arm.pat
    while head is PAs(_, q, _) {
      head = q
    }
    let ety = match head {
      PCon(_, name, _, _) => {
        let con = resolve_name(c, name, false, None)
        match con_info(con) {
          Some(ci) => VData(ci.data, [])
          None => c.fail(name + " is not an error constructor")
        }
      }
      _ => VData("Error", [])
    }
    let out = check_pat(c, arm.pat, ety, true, None, false)
    let rhs = match arm.rhs {
      Some(x) => x
      None => c.fail("missing handler body")
    }
    let cond = arm.cond.map(e => check(out.cxt, e, bool_ty()))
    clauses.push({ pats: [out.pat], cond, body: check(out.cxt, rhs, ty), })
  }
  (Try(tb, clauses), ty)
}

///|
/// When the scrutinee `sv` is not a variable and the goal is a proposition
/// where it occurs (possibly after unfolding a few definitions, even those
/// stuck on a `match`): the goal with it abstracted, under one more
/// variable. Matching on that variable then refines the goal, as Agda's
/// `with` does.
fn with_motive(cxt : Cxt, sv : Val, goal : Val) -> (Tm, Array[(Int32, Tm)])? {
  match force(sv) {
    VRigid(_, []) | VLit(_) | VCon(_, _) => return None
    _ => ()
  }
  let g0 = cxt.quote(goal)
  if !is_prop_head(g0) {
    return None
  }
  let a = tm_shift(cxt.quote(sv), 1, 0)
  // the depth exposing the most occurrences (the least one among those)
  let mut best : (Tm, Int32)? = None
  for depth = 0; depth <= 3; depth = depth + 1 {
    let gt = if depth == 0 { g0 } else { quote_open(cxt.lvl, goal, depth) }
    let (motive, found) = tm_abstract(tm_shift(gt, 1, 0), a, 0)
    if found {
      let n = var_count(motive, 0)
      match best {
        Some((_, m)) if m >= n => ()
        _ => best = Some((motive, n))
      }
    }
  }
  match best {
    None => None
    Some((motive, _)) => {
      // the hypotheses (bound variables) whose types mention it, abstracted
      // too, under the new variable
      let hyps : Array[(Int32, Tm)] = []
      for l = 0; l < cxt.lvl; l = l + 1 {
        if cxt.bound[l] && !cxt.muts[l] {
          let (t, found) = tm_abstract(
            tm_shift(cxt.quote(cxt.types[l]), 1, 0),
            a,
            0,
          )
          if found {
            hyps.push((l, t))
          }
        }
      }
      Some((motive, hyps))
    }
  }
}

///|
/// The occurrences of the variable `d` in `t`.
fn var_count(t : Tm, d : Int32) -> Int32 {
  let go = (x : Tm, k : Int32) => var_count(x, d + k)
  match t {
    Var(ix) => if ix == d { 1 } else { 0 }
    Lam(_, _, _, b) => go(b, 1)
    App(f, x, _) => go(f, 0) + go(x, 0)
    Pi(_, _, _, s, b) => go(s, 0) + go(b, 1)
    Let(_, s, v, b) => go(s, 0) + go(v, 0) + go(b, 1)
    Match(ss, cls) =>
      ss.fold(init=0, (n, x) => n + go(x, 0)) +
      cls.fold(init=0, (n, cl) => n + go(cl.body, pats_slots(cl.pats)))
    Raises(s, e) => go(s, 0) + go(e, 0)
    _ => 0
  }
}

///|
/// Quote `v`, unfolding global functions `depth` levels deep, even where
/// the result is stuck on a `match` (to find a term hidden in a definition).
fn quote_open(lvl : Int32, v : Val, depth : Int32) -> Tm {
  match force_meta(v) {
    VGlobal(n, sp) if depth > 0 =>
      match unfold(n, sp) {
        Some(w) => quote_open(lvl, w, depth - 1)
        None =>
          // a function that is run (`a; b`, ...): evaluate its body
          match globals.get(n) {
            Some({ kind: GFunc(Some(body), true, arity), .. }) if sp.length() >=
              arity &&
              can_unfold(n) =>
              quote_open(lvl, app_spine(eval([], body), sp), depth - 1)
            _ => quote(lvl, v)
          }
      }
    VMatch(env, vs, cls, sp) => {
      let cls2 = cls.map(cl => {
        let l2 = lvl + pats_slots(cl.pats)
        {
          pats: cl.pats,
          cond: clause_guard_val(env, lvl, cl).map(g => quote_open(l2, g, depth)),
          body: quote_open(l2, clause_body_val(env, lvl, cl), depth),
        }
      })
      let mut t = Match(vs.map(x => quote_open(lvl, x, depth)), cls2)
      for a in sp {
        t = App(t, quote_open(lvl, a.0, depth), a.1)
      }
      t
    }
    VData(n, sp) | VCon(n, sp) | VGlobal(n, sp) | VPrim(n, sp) => {
      let mut t = Global(n)
      for a in sp {
        t = App(t, quote_open(lvl, a.0, depth), a.1)
      }
      t
    }
    VRigid(l, sp) => {
      let mut t = Var(lvl - 1 - l)
      for a in sp {
        t = App(t, quote_open(lvl, a.0, depth), a.1)
      }
      t
    }
    _ => quote(lvl, v)
  }
}

///|
/// A `let mut` variable: it may be assigned later, so a clause does not
/// refine it.
fn is_mut_var(cxt : Cxt, v : Val) -> Bool {
  match force(cxt.subst(v)) {
    VRigid(l, []) => cxt.muts[l]
    _ => false
  }
}
