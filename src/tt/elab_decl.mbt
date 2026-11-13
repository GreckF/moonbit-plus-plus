///|
/// Top-level declarations.
fn register(name : String, ty : Tm, kind : GKind) -> Unit {
  globals.set(name, { name, ty, vty: eval([], ty), kind, })
}

///|
fn set_body(name : String, body : Tm, arity : Int32) -> Unit {
  match globals.get(name) {
    Some(g) => {
      note_unfold_helper(name)
      // the splices of code run when the code is made (staging.mbt); the
      // marks of effects are lowered (ctl.mbt)
      let body = lower_body(name, hoist_splices(body))
      g.kind = GFunc(Some(body), contains_imperative(body), arity)
    }
    None => ()
  }
}

///|
fn contains_imperative(t : Tm) -> Bool {
  match t {
    LetMut(_, _, _, _)
    | Assign(_, _)
    | While(_, _, _)
    | Break
    | Continue
    | Return(_)
    | Raise(_)
    | Try(_, _)
    | ArrayLit(_)
    | Seq(_, _)
    | Defer(_, _) => true
    // a fresh marker of a handler of `ctl` operations (run, see exec.mbt)
    App(Global("%effect_marker"), _, _) => true
    // quoted code is not run where it is written; its splices are
    // (staging.mbt)
    App(_, _, _) if quote_parts(t) is Some((_, s, _)) => contains_imperative(s)
    Lam(_, _, _, b) => contains_imperative(b)
    App(f, a, _) => contains_imperative(f) || contains_imperative(a)
    Pi(_, _, _, a, b) => contains_imperative(a) || contains_imperative(b)
    Let(_, a, v, b) =>
      contains_imperative(a) || contains_imperative(v) || contains_imperative(b)
    Match(ss, cls) =>
      ss.iter().any(contains_imperative) ||
      cls.iter().any(cl => contains_imperative(cl.body))
    Raises(a, e) => contains_imperative(a) || contains_imperative(e)
    _ => false
  }
}

///|
/// Replace solved metas.
fn zonk(lvl : Int32, t : Tm) -> Tm {
  let go = (x : Tm) => zonk(lvl, x)
  let solved_head = (h : Tm) => {
    match h {
      Meta(m) | InsertedMeta(m, _) => metas[m].sol is Some(_)
      _ => false
    }
  }
  match t {
    Meta(_) | InsertedMeta(_, _) =>
      if solved_head(t) {
        quote(lvl, eval(fresh_vars(0, lvl), t))
      } else {
        t
      }
    App(_, _, _) => {
      let (h, args) = flatten_app(t)
      if solved_head(h) {
        quote(lvl, eval(fresh_vars(0, lvl), t))
      } else {
        apps(go(h), args.map(a => (go(a.0), a.1)))
      }
    }
    Lam(x, i, g, b) => Lam(x, i, g, zonk(lvl + 1, b))
    Pi(x, i, g, a, b) => Pi(x, i, g, go(a), zonk(lvl + 1, b))
    Let(x, a, v, b) => Let(x, go(a), go(v), zonk(lvl + 1, b))
    LetMut(x, a, v, b) => LetMut(x, go(a), go(v), zonk(lvl + 1, b))
    Match(ss, cls) =>
      Match(
        ss.map(go),
        cls.map(cl => cl.map(b => zonk(lvl + pats_slots(cl.pats), b))),
      )
    Try(b, cls) =>
      Try(go(b), cls.map(cl => cl.map(b => zonk(lvl + pats_slots(cl.pats), b))))
    Raises(a, e) => Raises(go(a), go(e))
    Assign(ix, v) => Assign(ix, go(v))
    While(c, b, s) => While(go(c), go(b), go(s))
    Return(v) => Return(go(v))
    Raise(v) => Raise(go(v))
    ArrayLit(es) => ArrayLit(es.map(go))
    Seq(a, b) => Seq(go(a), go(b))
    Defer(a, b) => Defer(go(a), go(b))
    _ => t
  }
}

///|
fn has_metas(t : Tm) -> Bool {
  match t {
    Meta(_) | InsertedMeta(_, _) => true
    Lam(_, _, _, b) => has_metas(b)
    App(f, a, _) => has_metas(f) || has_metas(a)
    Pi(_, _, _, a, b) => has_metas(a) || has_metas(b)
    Let(_, a, v, b) | LetMut(_, a, v, b) =>
      has_metas(a) || has_metas(v) || has_metas(b)
    Match(ss, cls) =>
      ss.iter().any(has_metas) || cls.iter().any(cl => has_metas(cl.body))
    Try(b, cls) => has_metas(b) || cls.iter().any(cl => has_metas(cl.body))
    Raises(a, e) => has_metas(a) || has_metas(e)
    Assign(_, v) | Return(v) | Raise(v) => has_metas(v)
    While(c, b, s) => has_metas(c) || has_metas(b) || has_metas(s)
    ArrayLit(es) => es.iter().any(has_metas)
    Seq(a, b) | Defer(a, b) => has_metas(a) || has_metas(b)
    _ => false
  }
}

///|
/// Finish elaborating a definition: resolve instances, default the types of
/// unannotated implicit binders to `Type`, and zonk.
fn finish(
  cxt : Cxt,
  what : String,
  ts : Array[Tm],
  lvl~ : Int32 = 0,
) -> Array[Tm] raise ElabError {
  solve_pending(false)
  for d in st.type_defaults {
    let (m, n) = d
    if metas[m].sol is None {
      let mut t = U
      for _ in 0..<n {
        t = Lam("_", Expl, true, t)
      }
      metas[m].sol = Some(eval([], t))
    }
  }
  st.type_defaults.clear()
  close_open_rows()
  solve_pending(true)
  check_prop_args()
  let out = ts.map(t => zonk(lvl, t))
  for t in out {
    if has_metas(t) {
      cxt.fail("cannot infer all implicit arguments or types in " + what)
    }
  }
  register_lifted(cxt, what)
  out
}

///|
/// Context of the binders of a (closed) Pi type, and the remaining type.
fn telescope_cxt(
  cxt0 : Cxt,
  ty : Tm,
  n : Int32,
) -> (Cxt, Array[(String, Icit, Bool)], Val) {
  let mut cxt = cxt0
  let mut t = eval([], ty)
  let bs : Array[(String, Icit, Bool)] = []
  for _ in 0..<n {
    match force(t) {
      VPi(x, i, g, a, cl) => {
        let v = v_var(cxt.lvl)
        cxt = cxt.bind(x, a)
        bs.push((x, i, g))
        t = inst(cl, v)
      }
      _ => break
    }
  }
  (cxt, bs, t)
}

///|
fn wrap_lams(bs : Array[(String, Icit, Bool)], body : Tm) -> Tm {
  let mut t = body
  for k = bs.length() - 1; k >= 0; k = k - 1 {
    let (x, i, g) = bs[k]
    t = Lam(x, i, g, t)
  }
  t
}

// ---------------------------------------------------------------------------
// Functions

///|
fn elab_fn_sig(fd0 : @parser.FnDecl) -> Unit raise ElabError {
  // effect polymorphism without annotation (see effects.mbt)
  let fd = auto_effects(fd0)
  elab_fn_sig_of(
    fd,
    if fd.impl_params.length() != fd0.impl_params.length() {
      Some(fd0)
    } else {
      None
    },
  )
}

///|
/// The signature of `fd`; `plain` is the declaration without inferred effect
/// polymorphism, used if the function returns a proof (it has no effects).
fn elab_fn_sig_of(
  fd : @parser.FnDecl,
  plain : @parser.FnDecl?,
) -> Unit raise ElabError {
  let cxt = empty_cxt(fd.pos)
  let (c1, bs1) = elab_impl_binders(cxt, fd.impl_params)
  // the capabilities of the declared effects (see effects.mbt)
  let (c1, caps) = cap_binders(c1, fd.raises)
  let bs1 = concat(bs1, caps)
  let (c2, bs2) = match fd.params {
    Some(ps) => elab_expl_binders(c1, ps)
    None => (c1, [])
  }
  let (ret, ret_prop) = match fd.ret {
    Some(r) => check_type_sort(c2, r)
    None =>
      if fd.name == "main" || fd.body is BodyExtern(_) {
        (Global("Unit"), false)
      } else {
        (c2.fresh_meta(), false)
      }
  }
  match plain {
    Some(p) if ret_prop => return elab_fn_sig_of(p, None)
    _ => ()
  }
  let ret = raising_cod(c2, ret, ret_prop, fd.raises)
  let bs = concat(bs1, bs2)
  let ty = pis(bs, ret)
  match fd.params {
    Some(ps) if ps.iter().any(p => !(p.kind is Positional)) =>
      st.labels.set(fd.name, elab_tagged_params(fd.name, c1, bs1, bs2, ps))
    _ => ()
  }
  match fd.body {
    BodyExtern(p) => {
      let ty = finish(cxt, fd.name, [ty])[0]
      register(fd.name, ty, GPrim(p, bs.length()))
    }
    BodyExpr(_) => register(fd.name, ty, GFunc(None, false, bs.length()))
  }
}

///|
/// Label information of the explicit parameters of a top-level function.
/// Each default value `x~ : T = e` becomes a helper function
/// `f$default$x[impl](previous params, ())`, called at every call site that
/// omits `x` (so the default is evaluated each time, as in MoonBit).
fn elab_tagged_params(
  fname : String,
  c1 : Cxt,
  bs1 : Array[(String, Icit, Tm)],
  bs2 : Array[(String, Icit, Tm)],
  ps : Array[@parser.Binder],
) -> Array[LabelInfo] raise ElabError {
  let infos : Array[LabelInfo] = []
  let mut c = c1
  for k = 0; k < ps.length(); k = k + 1 {
    let p = ps[k]
    let info = match p.kind {
      Positional => LPos
      Optional => LOpt(p.name)
      Labelled(None) => LReq(p.name)
      Labelled(Some(e)) => {
        let helper = fname + "$default$" + p.name
        let unit_bs : Array[(String, Icit, Tm)] = [("_", Expl, Global("Unit"))]
        let hbs = concat(concat(bs1, bs2[0:k].to_array()), unit_bs)
        let cu = c.bind("_", VData("Unit", []))
        let t = check(cu.at(e.pos()), e, c.eval(bs2[k].2))
        let res = finish(c1, helper, [
          pis(hbs, tm_shift(bs2[k].2, 1, 0)),
          lams(hbs, t),
        ])
        register(helper, res[0], GFunc(None, false, hbs.length()))
        set_body(helper, res[1], hbs.length())
        LDefault(p.name, helper)
      }
    }
    infos.push(info)
    c = c.bind(p.name, c.eval(bs2[k].2))
  }
  infos
}

///|
fn elab_fn_body(fd : @parser.FnDecl) -> Unit raise ElabError {
  let body = match fd.body {
    BodyExpr(b) => b
    BodyExtern(_) => return
  }
  let g = globals.get(fd.name).unwrap()
  let n = match g.kind {
    GFunc(_, _, n) => n
    _ => 0
  }
  let cxt0 = empty_cxt(fd.pos)
  let (cxt, bs, rty) = telescope_cxt(cxt0, g.ty, n)
  let (body_ty, can_raise, can_async) = body_effects(rty)
  let bc = {
    ..cxt,
    can_raise,
    can_async,
    ret_ty: Some(body_ty),
    eff_row: codomain_row(rty),
    handled: [],
  }
  let t = mark_body(bc, check(bc, body, body_ty), codomain_row(rty))
  let res = finish(cxt, fd.name, [wrap_lams(bs, t), g.ty])
  globals.set(fd.name, {
    name: fd.name,
    ty: res[1],
    vty: eval([], res[1]),
    kind: g.kind,
  })
  set_body(fd.name, res[0], n)
  match ctl_error.val {
    Some(msg) => {
      ctl_error.val = None
      raise ElabError(fd.pos, msg)
    }
    None => ()
  }
}

///|
fn elab_def_sig(
  pos : Pos,
  name : String,
  impls : Array[@parser.Binder],
  ty : @parser.Expr?,
  body : @parser.Expr,
) -> Unit raise ElabError {
  let cxt = empty_cxt(pos)
  let (c1, bs) = elab_impl_binders(cxt, impls)
  match ty {
    Some(t) => {
      let tt = check_type(c1, t)
      register(name, pis(bs, tt), GFunc(None, false, bs.length()))
    }
    None => {
      let (t, a) = infer_ins(c1, body)
      let res = finish(cxt, name, [pis(bs, c1.quote(a)), lams(bs, t)])
      register(name, res[0], GFunc(None, false, bs.length()))
      set_body(name, res[1], bs.length())
    }
  }
}

///|
fn elab_def_body(
  pos : Pos,
  name : String,
  body : @parser.Expr,
) -> Unit raise ElabError {
  let g = globals.get(name).unwrap()
  if g.kind is GFunc(Some(_), _, _) {
    return
  }
  let n = match g.kind {
    GFunc(_, _, n) => n
    _ => 0
  }
  let (cxt, bs, rty) = telescope_cxt(empty_cxt(pos), g.ty, n)
  let t = check({ ..cxt, ret_ty: Some(rty), }, body, rty)
  let res = finish(cxt, name, [wrap_lams(bs, t)])
  set_body(name, res[0], n)
}

// ---------------------------------------------------------------------------
// Datatypes

///|
fn elab_data_header(
  pos : Pos,
  name : String,
  impls : Array[@parser.Binder],
  params : Array[@parser.Binder]?,
  sig : @parser.Expr?,
  cons : Array[String],
  fields : Array[String]?,
  is_trait : Bool,
  is_error : Bool,
) -> Unit raise ElabError {
  let cxt = empty_cxt(pos)
  let (c1, bs1) = elab_impl_binders(cxt, impls)
  let (c2, bs2) = match params {
    Some(ps) if ps.length() > 0 => elab_expl_binders(c1, ps)
    _ => (c1, [])
  }
  let (st_tm, nidx, is_prop) = match sig {
    Some(s) => {
      let t = check_type(c2, s)
      let mut cur = c2.eval(t)
      let mut l = c2.lvl
      let mut k = 0
      while force(cur) is VPi(_, _, _, _, cl) {
        cur = inst(cl, v_var(l))
        l = l + 1
        k = k + 1
      }
      match force(cur) {
        VU => (t, k, false)
        VProp => (t, k, true)
        _ => c2.fail("the type of " + name + " must end in Type or Prop")
      }
    }
    None => (U, 0, false)
  }
  let bs = concat(bs1, bs2)
  let ty = finish(cxt, name, [pis(bs, st_tm)])[0]
  register(
    name,
    ty,
    GData({
      name,
      nparams: bs.length(),
      nindices: nidx,
      cons,
      is_prop,
      fields,
      is_trait,
      is_error,
      builtin: false,
    }),
  )
}

///|
/// Context binding the parameters of datatype `d`, and their binders (all
/// implicit, for constructor types).
fn data_params_cxt(
  cxt0 : Cxt,
  d : String,
) -> (Cxt, Array[(String, Icit, Tm)]) raise ElabError {
  let g = global_entry(cxt0, d)
  let di = data_info(d).unwrap()
  let mut cxt = cxt0
  let bs : Array[(String, Icit, Tm)] = []
  let mut t = g.ty
  for _ in 0..<di.nparams {
    match t {
      Pi(x, _, _, a, b) => {
        bs.push((x, Impl, a))
        cxt = cxt.bind(x, cxt.eval(a))
        t = b
      }
      _ => break
    }
  }
  (cxt, bs)
}

///|
/// `D` applied to its parameters, in a context whose first variables are
/// the parameters.
fn data_self(cxt : Cxt, d : String) -> Tm {
  let g = globals.get(d).unwrap()
  let di = data_info(d).unwrap()
  let mut t = Global(d)
  let mut ty = g.ty
  for k = 0; k < di.nparams; k = k + 1 {
    match ty {
      Pi(_, i, _, _, b) => {
        t = App(t, Var(cxt.lvl - 1 - k), i)
        ty = b
      }
      _ => ()
    }
  }
  t
}

///|
fn elab_con(
  d : String,
  cd : @parser.ConDecl,
  is_error : Bool,
) -> Unit raise ElabError {
  let cxt0 = empty_cxt(cd.pos)
  let (pc, pbs) = data_params_cxt(cxt0, d)
  let di = data_info(d).unwrap()
  let (c1, ibs) = elab_impl_binders(pc, cd.impl_params)
  let (c2, ebs) = if cd.params.length() > 0 {
    elab_expl_binders(c1, cd.params)
  } else {
    (c1, [])
  }
  // labelled fields `C(x~ : Int)`: built with `C(x=e)`
  if cd.params.iter().any(p => !(p.kind is Positional)) {
    st.labels.set(
      d + "::" + cd.name,
      cd.params.map(p => {
        match p.kind {
          Positional => LPos
          _ => LReq(p.name)
        }
      }),
    )
  }
  let ret = match cd.ret {
    Some(r) => {
      let rt = check_type(c2, r)
      match force(c2.eval(rt)) {
        VData(d2, sp) if d2 == d => {
          for k = 0; k < di.nparams; k = k + 1 {
            if !c2.try_unify(sp[k].0, v_var(k)) {
              c2.fail(
                "constructor " +
                cd.name +
                " must return " +
                d +
                " applied to its parameters",
              )
            }
          }
          rt
        }
        _ => c2.fail("constructor " + cd.name + " must return " + d)
      }
    }
    None => {
      if di.nindices > 0 {
        c2.fail("constructor " + cd.name + " needs a return type")
      }
      data_self(c2, d)
    }
  }
  let name = d + "::" + cd.name
  let ty = finish(cxt0, name, [pis(concat(concat(pbs, ibs), ebs), ret)])[0]
  ignore(is_error)
  register(
    name,
    ty,
    GCon({
      name,
      data: d,
      nparams: di.nparams,
      nargs: ibs.length() + ebs.length(),
      nimpl: ibs.length(),
    }),
  )
}

///|
fn elab_struct_decl(sd : @parser.StructDecl) -> Unit raise ElabError {
  let d = sd.name
  let fnames = sd.fields.map(f => f.1)
  elab_data_header(
    sd.pos,
    d,
    sd.impl_params,
    sd.params,
    None,
    [d + "::mk"],
    Some(fnames),
    false,
    false,
  )
  let cxt0 = empty_cxt(sd.pos)
  let (pc, pbs) = data_params_cxt(cxt0, d)
  let np = pbs.length()
  // the constructor
  let mut c = pc
  let fbs : Array[(String, Icit, Tm)] = []
  if sd.fields.length() > 0 &&
    sd.fields.iter().all(f => f.1.iter().all(ch => ch >= '0' && ch <= '9')) {
    tuple_structs.set(d, true)
  }
  for f in sd.fields {
    // a `mut` field is a box, unless the struct is MoonBit's
    let (fty0, is_mut) = unmark_mut(f.2)
    let fty0 = if is_mut && !mbt_types.contains(d) {
      mut_fields.set(d + "::" + f.1, true)
      @parser.EApp(f.0, EVar(f.0, "Array"), Some([fty0]), None)
    } else {
      fty0
    }
    let ft = check_type(c.at(f.0), fty0)
    fbs.push((f.1, Expl, ft))
    c = c.bind(f.1, c.eval(ft))
  }
  let con_ty = finish(cxt0, d, [pis(concat(pbs, fbs), data_self(c, d))])[0]
  register(
    d + "::mk",
    con_ty,
    GCon({
      name: d + "::mk",
      data: d,
      nparams: np,
      nargs: fbs.length(),
      nimpl: 0,
    }),
  )
  // projections
  let n = fbs.length()
  let (pcx, pbs2) = data_params_cxt(cxt0, d)
  let self_ty = data_self(pcx, d)
  let sc = pcx.bind("self", pcx.eval(self_ty))
  let mut cty = global_entry(cxt0, d + "::mk").vty
  for k = 0; k < np; k = k + 1 {
    match force(cty) {
      VPi(_, _, _, _, cl) => cty = inst(cl, v_var(k))
      _ => ()
    }
  }
  for k = 0; k < n; k = k + 1 {
    let fname = d + "::" + fnames[k]
    let fty = match force(cty) {
      VPi(_, _, _, a, _) => a
      _ => VU
    }
    let pty = pis(concat(pbs2, [("self", Expl, self_ty)]), sc.quote(fty))
    let vars = fnames.map(x => CPVar(x))
    let body = lams(
      concat(pbs2, [("self", Expl, self_ty)]),
      Match([Var(0)], [
        { pats: [CPCon(d + "::mk", vars)], cond: None, body: Var(n - 1 - k), },
      ]),
    )
    register(fname, pty, GFunc(Some(body), false, np + 1))
    // later fields see this field as its projection
    let pv = app_spine(
      VGlobal(fname, []),
      concat(fresh_vars(0, np).map(v => (v, Impl)), [(v_var(np), Expl)]),
    )
    match force(cty) {
      VPi(_, _, _, _, cl) => cty = inst(cl, pv)
      _ => ()
    }
  }
}

///|
fn elab_enum(ed : @parser.EnumDecl) -> Unit raise ElabError {
  let cons = ed.cons.map(c => ed.name + "::" + c.name)
  elab_data_header(
    ed.pos,
    ed.name,
    ed.impl_params,
    ed.params,
    ed.sig,
    cons,
    None,
    false,
    ed.is_error,
  )
}

// ---------------------------------------------------------------------------
// Traits and instances

///|
fn elab_trait(td : @parser.TraitDecl) -> Unit raise ElabError {
  let tr = td.name
  let cxt0 = empty_cxt(td.pos)
  let kind = match td.self_kind {
    Some(k) => finish(cxt0, tr, [check_type(cxt0, k)])[0]
    None => U
  }
  let fields = concat(
    td.supers.map(s => "super$" + s),
    td.methods.map(m => m.name),
  )
  register(
    tr,
    Pi("Self", Expl, true, kind, U),
    GData({
      name: tr,
      nparams: 1,
      nindices: 0,
      cons: [tr + "::mk"],
      is_prop: false,
      fields: Some(fields),
      is_trait: true,
      is_error: false,
      builtin: false,
    }),
  )
  st.traits.set(tr, {
    kind,
    supers: td.supers,
    methods: td.methods.map(m => m.name),
  })
  // field types, in the context [Self]
  let sc = cxt0.bind("Self", cxt0.eval(kind))
  let ftys : Array[Tm] = []
  for s in td.supers {
    ensure(cxt0, s)
    ftys.push(App(Global(s), Var(0), Expl))
  }
  for m in td.methods {
    let (c1, bs1) = elab_impl_binders(sc.at(m.pos), m.impl_params)
    let (c2, bs2) = elab_expl_binders(c1, m.params)
    let (r, r_prop) = check_type_sort(c2, m.ret)
    let r = raising_cod(c2, r, r_prop, m.raises)
    ftys.push(
      finish(sc, tr + "::" + m.name, [pis(concat(bs1, bs2), r)], lvl=1)[0],
    )
  }
  let fbs = fields.mapi((k, f) => (f, Expl, tm_shift(ftys[k], k, 0)))
  let con_ty = Pi(
    "Self",
    Impl,
    false,
    kind,
    pis(fbs, tm_shift(App(Global(tr), Var(0), Expl), fields.length(), 0)),
  )
  register(
    tr + "::mk",
    con_ty,
    GCon({
      name: tr + "::mk",
      data: tr,
      nparams: 1,
      nargs: fields.length(),
      nimpl: 0,
    }),
  )
  let n = fields.length()
  for k = 0; k < n; k = k + 1 {
    // [Self : K, inst : Tr(Self)] -> field type
    let aty = Pi(
      "Self",
      Impl,
      false,
      kind,
      Pi(
        "inst",
        Inst,
        false,
        App(Global(tr), Var(0), Expl),
        tm_shift(ftys[k], 1, 0),
      ),
    )
    let vars = fields.map(x => CPVar(x))
    let body = Lam(
      "Self",
      Impl,
      false,
      Lam(
        "inst",
        Inst,
        false,
        Match([Var(0)], [
          {
            pats: [CPCon(tr + "::mk", vars)],
            cond: None,
            body: Var(n - 1 - k),
          },
        ]),
      ),
    )
    register(tr + "::" + fields[k], aty, GFunc(Some(body), false, 2))
  }
}

///|
fn impl_head(e : @parser.Expr) -> String {
  match e {
    EVar(_, n) => n
    EApp(_, f, _, _) => impl_head(f)
    EType(_) => "Type"
    _ => "?"
  }
}

///|
fn elab_impl_sig(name : String, d : @parser.ImplDecl) -> Unit raise ElabError {
  let cxt = empty_cxt(d.pos)
  ensure(cxt, d.trait_name)
  if !st.traits.contains(d.trait_name) {
    cxt.fail(d.trait_name + " is not a trait")
  }
  let (c1, bs) = elab_impl_binders(cxt, d.impl_params)
  let kind = st.traits.get(d.trait_name).unwrap().kind
  let ty = check(c1.at(d.for_ty.pos()), d.for_ty, eval([], kind))
  let ity = finish(cxt, name, [pis(bs, App(Global(d.trait_name), ty, Expl))])[0]
  register(name, ity, GFunc(None, false, bs.length()))
  map_push(st.instances, d.trait_name, name)
}

///|
fn elab_impl_body(
  name : String,
  ds : Array[@parser.ImplDecl],
) -> Unit raise ElabError {
  let d0 = ds[0]
  let tr = d0.trait_name
  let g = globals.get(name).unwrap()
  let n = match g.kind {
    GFunc(_, _, n) => n
    _ => 0
  }
  let (cxt, bs, rty) = telescope_cxt(empty_cxt(d0.pos), g.ty, n)
  let self_v = match force(rty) {
    VData(_, [(s, _)]) => s
    _ => cxt.fail("bad instance type")
  }
  let info = st.traits.get(tr).unwrap()
  let fields = data_info(tr).unwrap().fields.unwrap()
  let mut cty = global_entry(cxt, tr + "::mk").vty
  match force(cty) {
    VPi(_, _, _, _, cl) => cty = inst(cl, self_v)
    _ => ()
  }
  let args : Array[(Tm, Icit)] = [(cxt.quote(self_v), Impl)]
  for d in ds {
    if d.meth != "" && !info.methods.contains(d.meth) {
      cxt.at(d.pos).fail(d.meth + " is not a method of " + tr)
    }
  }
  for f in fields {
    let fty = match force(cty) {
      VPi(_, _, _, a, _) => a
      _ => cxt.fail("bad trait constructor")
    }
    let arg = if f.has_prefix("super$") {
      match search_instance(cxt, fty, 0) {
        Some(t) => t
        None =>
          cxt.fail("missing instance " + cxt.show(fty) + " required by " + tr)
      }
    } else {
      let own = ds.iter().find_first(d => d.meth == f)
      match
        (if own is None { trait_defaults.get(tr + "::" + f) } else { own }) {
        Some(d) => {
          let lam : @parser.Expr = ELam(d.pos, [], d.params, None, d.body)
          check(cxt.at(d.pos), lam, fty)
        }
        None => cxt.fail("missing method " + f + " in impl of " + tr)
      }
    }
    args.push((arg, Expl))
    match force(cty) {
      VPi(_, _, _, _, cl) => cty = inst(cl, cxt.eval(arg))
      _ => ()
    }
  }
  let body = wrap_lams(bs, apps(Global(tr + "::mk"), args))
  let res = finish(cxt, name, [body])
  set_body(name, res[0], n)
}

// ---------------------------------------------------------------------------
// Programs

///|
fn add_thunk(name : String, th : () -> Unit raise ElabError) -> Unit {
  st.thunks.set(name, () => with_time_limit(name, () => with_no_unfolding(th)))
}

///|
/// A thunk shared by several names, run at most once.
fn shared_thunk(names : Array[String], th : () -> Unit raise ElabError) -> Unit {
  let done = Ref(false)
  let f = () => {
    if !done.val {
      done.val = true
      th()
    }
  }
  for n in names {
    add_thunk(n, f)
  }
}

///|
/// With `lenient` (used for imported interfaces), declarations whose names
/// are already taken, or that fail to elaborate, are skipped and their names
/// added to `skipped`.
pub fn check_decls(
  decls0 : Array[@parser.Decl],
  lenient~ : Bool = false,
  skipped~ : Array[String] = [],
) -> Unit raise ElabError {
  // `#mbt` marks are recorded first, so that the declarations see each other
  let marked : Array[(Pos, String)] = []
  let mbt_fn_decls : Array[(Pos, String)] = []
  let mbt_impls : Array[(Pos, String, String)] = []
  let decls : Array[@parser.Decl] = []
  let decls0 = expand_effects(
    expand_derives(decls0.map(d => strip_unfold_attrs(strip_limits(d)))),
  )
  if !lenient {
    for d in decls0 {
      record_decl_pos(d.inner())
      // a declaration without `#mbt` that takes the name of a `#mbt` one
      // (an `enum Sub` replacing the Prelude's trait) is not `#mbt`
      if !(d is DMbt(_, _, _, _)) {
        for n in decl_global_names(d) {
          mbt_types.remove(n)
        }
      }
    }
  }
  for d in decls0 {
    match d {
      DPub(inner) => {
        if !lenient {
          match inner {
            DEnum({ is_error: false, name, pos, .. })
            | DStruct({ name, pos, .. })
            | DTrait({ name, pos, .. })
            | DFn({ is_lemma: false, name, pos, .. }) =>
              pub_decls.push((pos, name, inner is DFn(_)))
            _ => ()
          }
        }
        decls.push(inner)
      }
      DMbt(pos, mbt_name, read_only, inner) => {
        let inner = inner.inner()
        let n = match inner {
          DEnum(ed) => ed.name
          DStruct(sd) => sd.name
          DTrait(td) => td.name
          DFn(fd) => {
            mbt_fns.set(fd.name, mbt_name.unwrap_or(fd.name))
            mbt_fn_decls.push((pos, fd.name))
            decls.push(inner)
            continue
          }
          _ => continue
        }
        if lenient && (globals.contains(n) || st.thunks.contains(n)) {
          decls.push(inner)
          continue
        }
        mbt_types.set(n, {
          name: mbt_name.unwrap_or(n),
          defined: mbt_name is None,
          read_only,
        })
        marked.push((pos, n))
        decls.push(inner)
      }
      _ => decls.push(d)
    }
  }
  // Datatypes first; then, in source order, each function's signature
  // directly followed by its body, so that later signatures can compute with
  // earlier functions. Forward references get their signatures on demand.
  let types : Array[String] = []
  let steps : Array[() -> Unit raise ElabError] = []
  let impl_groups : Map[String, Array[@parser.ImplDecl]] = Map([])
  let nowhere = empty_cxt({ line: 0, col: 0, })
  let taken = (n : String) => globals.contains(n) || st.thunks.contains(n)
  for d in decls {
    if lenient {
      let name = match d {
        DFn(fd) => fd.name
        DDef(_, n, _, _, _) | DOpaque(_, n, _) => n
        DEnum(ed) => ed.name
        DStruct(sd) => sd.name
        DTrait(td) => td.name
        DImpl(id) => "impl$" + id.trait_name + "$" + impl_head(id.for_ty)
        DMbt(_, _, _, _)
        | DPub(_)
        | DDerive(_, _)
        | DLimit(_, _, _)
        | DUnfoldAttr(_, _, _)
        | DEffect(_) => continue
      }
      if taken(name) && !(d is DImpl(_) && impl_groups.contains(name)) {
        skipped.push(name)
        continue
      }
    }
    match d {
      // effects are structs by now (expand_effects)
      DMbt(_, _, _, _)
      | DPub(_)
      | DDerive(_, _)
      | DLimit(_, _, _)
      | DUnfoldAttr(_, _, _)
      | DEffect(_) => ()
      DOpaque(_, name, k) => {
        add_thunk(name, () => {
          let mut ty = U
          for _ in 0..<k {
            ty = Pi("T", Impl, false, U, ty)
          }
          builtin_data(name, ty, k, false)
        })
        types.push(name)
      }
      DFn(fd) => {
        add_thunk(fd.name, () => elab_fn_sig(fd))
        steps.push(() => {
          ensure(nowhere, fd.name)
          with_time_limit(fd.name, () => {
            with_unfolding(fd.name, () => elab_fn_body(fd))
          })
        })
      }
      DDef(pos, name, impls, ty, body) => {
        add_thunk(name, () => elab_def_sig(pos, name, impls, ty, body))
        steps.push(() => {
          ensure(nowhere, name)
          with_time_limit(name, () => {
            with_unfolding(name, () => elab_def_body(pos, name, body))
          })
        })
      }
      DEnum(ed) => {
        let names = ed.cons.map(c => ed.name + "::" + c.name)
        for k = 0; k < names.length(); k = k + 1 {
          map_push(st.cons_by_short, ed.cons[k].name, names[k])
        }
        add_thunk(ed.name, () => elab_enum(ed))
        shared_thunk(names, () => {
          ensure(empty_cxt(ed.pos), ed.name)
          for c in ed.cons {
            elab_con(ed.name, c, ed.is_error)
          }
        })
        types.push(ed.name)
        for n in names {
          types.push(n)
        }
      }
      DStruct(sd) => {
        let names = [
          sd.name,
          sd.name + "::mk",
          ..sd.fields.map(f => sd.name + "::" + f.1),
        ]
        shared_thunk(names, () => elab_struct_decl(sd))
        types.push(sd.name)
      }
      DTrait(td) => {
        for m in td.methods {
          map_push(st.trait_methods, m.name, td.name)
        }
        let names = [
          td.name,
          td.name + "::mk",
          ..td.methods.map(m => td.name + "::" + m.name),
          ..td.supers.map(s => td.name + "::super$" + s),
        ]
        shared_thunk(names, () => elab_trait(td))
        types.push(td.name)
      }
      // the default of a method
      DImpl({ for_ty: EVar(_, "%Default"), .. } as id) =>
        trait_defaults.set(id.trait_name + "::" + id.meth, id)
      DImpl(id) => {
        let h = impl_head(id.for_ty)
        let key = "impl$" + id.trait_name + "$" + h
        match impl_groups.get(key) {
          Some(g) => {
            // MoonBit rejects two impls of a method for the same type
            if g.iter().any(o => o.meth == id.meth) {
              raise ElabError(
                id.pos,
                "duplicate impl of " +
                id.trait_name +
                "::" +
                id.meth +
                " for " +
                h,
              )
            }
            g.push(id)
          }
          None => {
            impl_groups.set(key, [id])
            mbt_impls.push((id.pos, key, id.trait_name))
            map_push(st.instance_heads, id.trait_name, h)
            map_push(st.impl_sigs, id.trait_name, key)
            add_thunk(key, () => elab_impl_sig(key, id))
            steps.push(() => {
              ensure(nowhere, key)
              with_time_limit(key, () => {
                with_unfolding(key, () => {
                  elab_impl_body(key, impl_groups.get(key).unwrap())
                })
              })
            })
          }
        }
      }
    }
  }
  for name in types {
    unfolded_too_early.clear()
    blocked_opaque.clear()
    if lenient {
      ensure(nowhere, name) catch {
        _ => skipped.push(name)
      }
    } else {
      ensure(nowhere, name)
    }
  }
  check_mbt_decls(marked, lenient)
  for k = 0; k < steps.length(); k = k + 1 {
    unfolded_too_early.clear()
    blocked_opaque.clear()
    if lenient {
      let npending = st.pending.length()
      steps[k]() catch {
        ElabError(_, msg) => {
          // drop what the failed declaration left behind
          while st.pending.length() > npending {
            ignore(st.pending.pop())
          }
          st.type_defaults.clear()
          skipped.push(msg)
        }
      }
    } else {
      steps[k]()
    }
  }
  check_mbt_impls(mbt_impls, lenient)
  check_mbt_fns(mbt_fn_decls)
  // the splices of stage 0 are run now (staging.mbt)
  if !lenient {
    unstage_all()
  }
}

///|
/// Where the globals of a declaration are declared (for go to definition).
fn record_decl_pos(d : @parser.Decl) -> Unit {
  let set = (n : String, p : Pos, kind : String) => {
    if in_package(p) {
      decl_pos.set(n, p)
      decl_kinds.set(n, kind)
    }
  }
  match d {
    DFn(fd) => set(fd.name, fd.pos, if fd.is_lemma { "lemma" } else { "fn" })
    DDef(p, n, _, _, _) => set(n, p, "let")
    DOpaque(p, n, _) => set(n, p, "type")
    DEnum(ed) => {
      set(ed.name, ed.pos, "enum")
      for c in ed.cons {
        set(ed.name + "::" + c.name, c.pos, "constructor")
      }
    }
    DStruct(sd) => {
      set(sd.name, sd.pos, "struct")
      for f in sd.fields {
        set(sd.name + "::" + f.1, f.0, "field")
      }
    }
    DTrait(td) => {
      set(td.name, td.pos, "trait")
      for m in td.methods {
        set(td.name + "::" + m.name, m.pos, "method")
      }
    }
    DEffect(ed) => {
      set(ed.name, ed.pos, "effect")
      for o in ed.ops {
        set(o.name, o.pos, "operation")
      }
    }
    DImpl(_)
    | DMbt(_, _, _, _)
    | DPub(_)
    | DDerive(_, _)
    | DLimit(_, _, _)
    | DUnfoldAttr(_, _, _) => ()
  }
}
