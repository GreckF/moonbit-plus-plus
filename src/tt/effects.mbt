///|
/// Algebraic effects (see doc/mbtpp/effects.md).
///
/// An effect `effect E[T] { Op(A) -> R }` is a struct `E[T]` with one field
/// per operation, the capability: `Op : (A) -> R` for an operation whose
/// handlers resume in tail position. A `try` with arms for the operations of
/// `E` binds a capability `%cap:E` around its body, whose fields run the
/// arms (the tail `resume(v)` returns `v`); `perform Op(x)` calls the field
/// of the innermost capability. A top-level function whose type has the
/// effect `!E[T]` takes the capability as an instance argument, found at
/// each call among the capabilities in scope. Lambdas capture the
/// capabilities in scope: handlers are lexically scoped.
///
/// In a codomain, effects are kept with the errors: `T!E1 + E2 + e raise
/// Err` is `T raise %Effs[%Row[E1, %Row[E2, e]], Err]` (`%NoRaise` without
/// errors, `%RowNil` at the end of a row without an effect variable).

///|
priv struct OpInfo {
  eff : String
  ctl : Bool
  nparams : Int32
}

///|
/// Operation name -> its effect.
let effect_ops : Map[String, OpInfo] = {}

///|
/// Effect name -> its operations, in order.
let effect_decls : Map[String, Array[String]] = {}

///|
fn reset_effects() -> Unit {
  effect_ops.clear()
  effect_decls.clear()
  // the calls of `resume` in the arms of `ctl` operations (ctl.mbt)
  effect_decls.set("%Resume", [])
  // errors and async, in rows (they keep their own translation)
  effect_decls.set("%Exn", [])
  effect_decls.set("%AsyncE", [])
  open_rows.clear()
  exec_depth.val = 0
  reset_ctl()
}

///|
pub fn is_effect(name : String) -> Bool {
  effect_decls.contains(name)
}

///|
/// The name of the capability of the effect `eff` in a context.
fn cap_name(eff : String) -> String {
  "%cap:" + eff
}

///|
/// Replace the effect declarations by their capability structs.
fn expand_effects(
  decls : Array[@parser.Decl],
) -> Array[@parser.Decl] raise ElabError {
  decls.map(d => expand_effect(d))
}

///|
fn expand_effect(d : @parser.Decl) -> @parser.Decl raise ElabError {
  match d {
    DPub(inner) => DPub(expand_effect(inner))
    DMbt(p, n, ro, inner) => DMbt(p, n, ro, expand_effect(inner))
    DLimit(p, n, inner) => DLimit(p, n, expand_effect(inner))
    DEffect(ed) => {
      let ops : Array[String] = []
      for op in ed.ops {
        if effect_ops.contains(op.name) {
          raise ElabError(
            op.pos,
            "the operation " +
            op.name +
            " is already declared by the effect " +
            effect_ops[op.name].eff,
          )
        }
        effect_ops.set(op.name, {
          eff: ed.name,
          ctl: op.ctl,
          nparams: op.params.length(),
        })
        ops.push(op.name)
      }
      effect_decls.set(ed.name, ops)
      // a `ctl` operation's field returns its computation (ctl.mbt); the
      // marker identifies the handler
      let fields = ed.ops.map(op => {
        (
          op.pos,
          op.name,
          @parser.EPi(op.pos, [], Some(op.params), op.ret, None),
        )
      })
      if ed.ops.iter().any(op => op.ctl) {
        fields.push((ed.pos, "%marker", EVar(ed.pos, "Int")))
      }
      DStruct({
        pos: ed.pos,
        name: ed.name,
        impl_params: ed.params,
        params: None,
        fields,
      })
    }
    _ => d
  }
}

// ---------------------------------------------------------------------------
// Rows

///|
/// The items of a row in a surface type `%Row[E1, %Row[E2, tail]]`, and its
/// tail.
fn row_exprs(row : @parser.Expr) -> (Array[@parser.Expr], @parser.Expr) {
  let items : Array[@parser.Expr] = []
  let mut r = row
  while r is EApp(_, EVar(_, "%Row"), Some([item, rest]), _) {
    items.push(item)
    r = rest
  }
  (items, r)
}

///|
/// The effects (without the effect variable) of a surface codomain effect
/// `%Effs[row, err]`.
fn declared_effects(raises : @parser.Expr?) -> Array[@parser.Expr] {
  match raises {
    Some(EApp(_, EVar(_, "%Effs"), Some([row, _]), _)) => row_exprs(row).0
    _ => []
  }
}

///|
/// The name of an effect in a row.
fn effect_head(e : @parser.Expr) -> String? {
  match e {
    EVar(_, n) | EApp(_, EVar(_, n), _, _) => Some(n)
    _ => None
  }
}

///|
/// The instance parameters of a top-level function for the effects declared
/// in its type (elaborated in `cxt`, where its implicit parameters are
/// bound).
fn cap_binders(
  cxt : Cxt,
  raises : @parser.Expr?,
) -> (Cxt, Array[(String, Icit, Tm)]) raise ElabError {
  let mut c = cxt
  let bs : Array[(String, Icit, Tm)] = []
  for item in declared_effects(raises) {
    let n = match effect_head(item) {
      Some(n) if is_effect(n) => n
      _ => c.at(item.pos()).fail("not an effect: " + show_expr_head(item))
    }
    let ty = check_type(c.at(item.pos()), item)
    bs.push((cap_name(n), Inst, ty))
    c = c.bind(cap_name(n), c.eval(ty))
  }
  (c, bs)
}

///|
fn show_expr_head(e : @parser.Expr) -> String {
  effect_head(e).unwrap_or("this type")
}

///|
/// The level of the innermost variable named `x`.
fn lookup_level(cxt : Cxt, x : String) -> Int32? {
  for l = cxt.lvl - 1; l >= 0; l = l - 1 {
    if cxt.names[l] == x {
      return Some(l)
    }
  }
  None
}

///|
/// Solve an instance argument whose type is the capability of an effect:
/// the innermost capability in scope.
fn solve_cap(p : PendingInst, eff : String, goal : Val) -> Bool raise ElabError {
  let cxt = p.cxt
  match lookup_level(cxt, cap_name(eff)) {
    Some(l) => {
      cxt.unify(goal, cxt.types[l])
      cxt.unify(cxt.eval(p.meta), v_var(l))
      true
    }
    None =>
      cxt.fail(
        "this call performs the effect " +
        eff +
        ", which no enclosing `try` handles and the function does not declare",
      )
  }
}

// ---------------------------------------------------------------------------
// perform

///|
fn elab_perform(
  cxt : Cxt,
  pos : Pos,
  op : String,
  args : Array[@parser.Expr],
) -> (Tm, Val) raise ElabError {
  let info = match effect_ops.get(op) {
    Some(i) => i
    None => cxt.fail(op + " is not an operation of an effect")
  }
  if args.length() != info.nparams {
    cxt.fail(
      op +
      " takes " +
      info.nparams.to_string() +
      " argument(s), got " +
      args.length().to_string(),
    )
  }
  let l = match lookup_level(cxt, cap_name(info.eff)) {
    Some(l) => l
    None =>
      cxt.fail(
        "perform " +
        op +
        ": no enclosing `try` handles the effect " +
        info.eff +
        " and the function does not declare it",
      )
  }
  require_effect(cxt, cxt.types[l])
  let (t, ty) = infer(
    cxt,
    EApp(pos, EField(pos, EVar(pos, cap_name(info.eff)), op), None, Some(args)),
  )
  if info.ctl {
    // the call returns the computation of the operation (ctl.mbt)
    ensure_ctl_runtime()
    (mark_call(cxt, t, row_cons(cxt.types[l], row_nil())), ty)
  } else {
    (t, ty)
  }
}

///|
/// The operation an arm of a `try` handles, if any.
fn arm_op(arm : @parser.Arm) -> (String, Array[@parser.Pat])? {
  let mut p = arm.pat
  while p is PAs(_, q, _) {
    p = q
  }
  match p {
    PCon(_, name, _, args) if effect_ops.contains(name) => Some((name, args))
    _ => None
  }
}

///|
/// Rewrite the tail `resume(v)` of the arm of a tail-resumptive operation
/// into `v`. Every path must end with `resume`.
fn tail_resume(e : @parser.Expr) -> @parser.Expr raise ElabError {
  let no_resume = (p : Pos) => {
    raise ElabError(
      p, "the handler of this operation must end with `resume(...)` (declare the operation with `ctl` to resume elsewhere, or not at all)",
    )
  }
  match e {
    EApp(p, EVar(_, "resume"), None, Some(args)) =>
      match args.length() {
        0 => ELit(p, LUnit)
        1 => args[0]
        _ => ETuple(p, args)
      }
    EBlock(p, stmts) =>
      match stmts.last() {
        Some(SExpr(sp, last)) => {
          let out = stmts.copy()
          out[out.length() - 1] = SExpr(sp, tail_resume(last))
          EBlock(p, out)
        }
        _ => no_resume(p)
      }
    EIf(p, c, t, Some(f)) => EIf(p, c, tail_resume(t), Some(tail_resume(f)))
    EMatch(p, s, r, arms) =>
      EMatch(
        p,
        s,
        r,
        arms.map(a => { ..a, rhs: a.rhs.map(x => tail_resume(x)), }),
      )
    _ => no_resume(e.pos())
  }
}

///|
/// `try body catch { arms }` where some arms handle operations: the
/// capabilities of the handled effects are bound around the body. The other
/// arms handle errors.
fn elab_handle(
  cxt : Cxt,
  pos : Pos,
  body : @parser.Expr,
  arms : Array[@parser.Arm],
  goal : Val?,
) -> (Tm, Val) raise ElabError {
  // the handled effects, in order, and the arms of each operation
  let effs : Array[String] = []
  let op_arms : Map[String, Array[@parser.Arm]] = {}
  let err_arms : Array[@parser.Arm] = []
  for arm in arms {
    match arm_op(arm) {
      Some((op, _)) => {
        let e = effect_ops[op].eff
        if !effs.contains(e) {
          effs.push(e)
        }
        map_push(op_arms, op, arm)
      }
      None => err_arms.push(arm)
    }
  }
  // the capabilities' types; their parameters are found from the body
  let cap_tys : Array[Val] = []
  let mut bc = cxt
  for e in effs {
    let nparams = match globals.get(e) {
      Some(_) => type_arity(e)
      None => {
        ensure(cxt, e)
        type_arity(e)
      }
    }
    let ty_e : @parser.Expr = if nparams == 0 {
      EVar(pos, e)
    } else {
      EApp(pos, EVar(pos, e), Some(Array::make(nparams, EHole(pos))), None)
    }
    let ty = cxt.eval(check_type(cxt, ty_e))
    cap_tys.push(ty)
    bc = bc.bind(cap_name(e), ty)
  }
  bc = { ..bc, handled: [..cxt.handled, ..effs], }
  // the body, then the error arms
  let inner = if err_arms.length() > 0 {
    @parser.ETry(pos, body, err_arms, None)
  } else {
    body
  }
  let (tb, ty) = match goal {
    Some(g) => (check(bc, inner, g), g)
    None => infer_ins(bc, inner)
  }
  // handlers are lexical: a function performing a handled effect cannot
  // leave the `try` (it would use this handler after it is gone)
  let rty = bc.quote(ty)
  for e in effs {
    if mentions_global(rty, e) {
      cxt
      .at(pos)
      .fail(
        "the result of this try has the type " +
        bc.show(ty) +
        ", which performs " +
        e +
        ": a function performing an effect cannot leave the try that handles it",
      )
    }
  }
  // the capabilities, in the context outside of the body: an operation in
  // an arm goes to an outer handler
  let caps : Array[Tm] = []
  let dispatches : Array[Tm?] = []
  for k = 0; k < effs.length(); k = k + 1 {
    let e = effs[k]
    let ops = effect_decls[e]
    let has_ctl = ops.iter().any(op => effect_ops[op].ctl)
    let ctl_ops = ops.filter(op => effect_ops[op].ctl && op_arms.contains(op))
    if ctl_ops.length() > 0 {
      ensure_ctl_runtime()
      if err_arms.length() > 0 {
        cxt.fail(
          "a `try` cannot handle errors and `ctl` operations together yet; use two `try`s",
        )
      }
    }
    // the marker and the fields of the ctl operations are bound around the
    // capability
    let mut ccx = cxt
    if has_ctl {
      ccx = ccx.bind("%m", VData("Int", []))
    }
    let ctl_tys : Array[Val] = []
    for op in ctl_ops {
      let (_, fty) = infer(bc, EField(pos, EVar(pos, cap_name(e)), op))
      ctl_tys.push(fty)
      ccx = ccx.bind("%ctl$" + op, fty)
    }
    let fields : Array[(String, @parser.Expr)] = []
    for op in ops {
      let f = if ctl_ops.contains(op) {
        @parser.EVar(pos, "%ctl$" + op)
      } else {
        match op_arms.get(op) {
          Some(oas) => op_closure(cxt, pos, op, oas)
          // not handled here: an outer handler's
          None =>
            match lookup_level(cxt, cap_name(e)) {
              Some(_) => EField(pos, EVar(pos, cap_name(e)), op)
              None =>
                cxt.fail(
                  "this handler of " +
                  e +
                  " does not handle " +
                  op +
                  ", and no outer handler does",
                )
            }
        }
      }
      fields.push((op, f))
    }
    if has_ctl {
      // without ctl arms here, the operations go to the outer handler
      let m : @parser.Expr = if ctl_ops.length() == 0 &&
        lookup_level(cxt, cap_name(e)) is Some(_) {
        EField(pos, EVar(pos, cap_name(e)), "%marker")
      } else {
        EVar(pos, "%m")
      }
      fields.push(("%marker", m))
    }
    let mut capv = check(
      { ..ccx, arm_lams: true, },
      EStruct(pos, fields),
      cap_tys[k],
    )
    let scope = if has_ctl { ["%m"] } else { [] }
    let closures : Array[Tm] = []
    for op in ctl_ops {
      closures.push(ctl_field(e, op, scope))
      scope.push("%ctl$" + op)
    }
    for j = ctl_ops.length() - 1; j >= 0; j = j - 1 {
      capv = Let("%ctl$" + ctl_ops[j], any_ty(), closures[j], capv)
    }
    if has_ctl {
      capv = Let(
        "%m",
        Global("Int"),
        App(Global("%effect_marker"), Lit(LUnit), Expl),
        capv,
      )
    }
    // the capability is under the previous ones
    caps.push(shift_tm(capv, k, 0))
    if ctl_ops.length() > 0 {
      let arm_tms : Array[Tm] = []
      for j = 0; j < ctl_ops.length(); j = j + 1 {
        arm_tms.push(
          ctl_arm(cxt, pos, ctl_ops[j], op_arms[ctl_ops[j]], ctl_tys[j], ty),
        )
      }
      dispatches.push(Some(dispatch_tm(e, ctl_ops, arm_tms)))
    } else {
      dispatches.push(None)
    }
  }
  let mut t = tb
  for k = effs.length() - 1; k >= 0; k = k - 1 {
    match dispatches[k] {
      Some(d) => {
        // the marker of this capability (variable 0)
        let mut marker = Global(effs[k] + "::%marker")
        for _ in 0..<type_arity(effs[k]) {
          marker = App(marker, any_ty(), Impl)
        }
        marker = App(marker, Var(0), Expl)
        t = App(
          App(App(Global("%handle"), marker, Expl), shift_tm(d, k + 1, 0), Expl),
          t,
          Expl,
        )
      }
      None => ()
    }
    t = Let(cap_name(effs[k]), quote(cxt.lvl + k, cap_tys[k]), caps[k], t)
  }
  (t, ty)
}

///|
/// The number of (implicit) type parameters of a struct.
fn type_arity(name : String) -> Int32 {
  match globals.get(name) {
    Some(g) => {
      let mut n = 0
      let mut t = g.ty
      while t is Pi(_, _, _, _, b) {
        n = n + 1
        t = b
      }
      n
    }
    None => 0
  }
}

///|
/// The field of a capability for the operation `op`, from its arms: a
/// function of the operation's arguments that matches them against the
/// arms' patterns.
fn op_closure(
  cxt : Cxt,
  pos : Pos,
  op : String,
  oas : Array[@parser.Arm],
) -> @parser.Expr raise ElabError {
  let info = effect_ops[op]
  if info.ctl {
    cxt.at(oas[0].pos).fail("`ctl` operations are not supported yet")
  }
  let params : Array[@parser.Binder] = []
  let xs : Array[@parser.Expr] = []
  for k = 0; k < info.nparams; k = k + 1 {
    let x = "%arg" + k.to_string()
    params.push({ pos, name: x, ty: None, kind: Positional, })
    xs.push(EVar(pos, x))
  }
  let arms2 : Array[@parser.Arm] = []
  for a in oas {
    let rhs = match a.rhs {
      Some(r) => tail_resume(r)
      None => cxt.at(a.pos).fail("missing handler body")
    }
    if mentions(rhs, "resume") {
      cxt
      .at(a.pos)
      .fail(
        "`resume` can only be the last step of the handler of this operation (declare it with `ctl` to resume elsewhere)",
      )
    }
    let args = match arm_op(a) {
      Some((_, ps)) => ps
      None => []
    }
    if args.length() != info.nparams {
      cxt
      .at(a.pos)
      .fail(
        op +
        " takes " +
        info.nparams.to_string() +
        " argument(s), got " +
        args.length().to_string(),
      )
    }
    // `Op(p) as x`: `x` is not useful for an operation; keep the pattern
    let pat : @parser.Pat = match args.length() {
      0 => PWild(a.pos)
      1 => args[0]
      _ => PTuple(a.pos, args)
    }
    arms2.push({ pos: a.pos, pat, cond: a.cond, rhs: Some(rhs), })
  }
  let scrut : @parser.Expr = match xs.length() {
    0 => ELit(pos, LUnit)
    1 => xs[0]
    _ => ETuple(pos, xs)
  }
  ELam(pos, [], params, None, EMatch(pos, scrut, None, arms2))
}

// ---------------------------------------------------------------------------
// Effect rows: checking what code may perform

///|
fn row_nil() -> Val {
  VData("%RowNil", [])
}

///|
fn row_cons(item : Val, rest : Val) -> Val {
  VData("%Row", [(item, Impl), (rest, Impl)])
}

///|
/// The items of a row, and its tail (`%RowNil`, or an effect variable).
fn row_flat(row : Val) -> (Array[Val], Val) {
  let items : Array[Val] = []
  let mut r = force(row)
  while r is VData("%Row", [(item, _), (rest, _)]) {
    items.push(item)
    r = force(rest)
  }
  (items, r)
}

///|
/// The effect row of a codomain (`%RowNil` without effects).
fn codomain_row(ty : Val) -> Val {
  match force(ty) {
    VRaises(_, e) =>
      match force(e) {
        VData("%Effs", [(row, _), (err, _)]) =>
          match force(err) {
            VData("%NoRaise", _) => row
            _ => row_cons(exn_item(err), row)
          }
        VData("%Async", [(err, _)]) =>
          row_cons(
            VData("%AsyncE", []),
            match force(err) {
              VData("%NoRaise", _) => row_nil()
              _ => row_cons(exn_item(err), row_nil())
            },
          )
        // `raise E`
        _ => row_cons(exn_item(e), row_nil())
      }
    _ => row_nil()
  }
}

///|
/// The errors `E` as a row item: `raise E` is `!Raise[E]`.
fn exn_item(err : Val) -> Val {
  VData("%Exn", [(err, Impl)])
}

///|
/// The effect name of a row item (`None` for an effect variable).
fn item_effect(item : Val) -> String? {
  match force(item) {
    VData(n, _) if is_effect(n) => Some(n)
    _ => None
  }
}

///|
/// The code being checked performs `item` (an effect, or an effect
/// variable): it must be handled by an enclosing `try` of the same function,
/// or be in the row of the function. A row ending with a meta (a lambda
/// whose type is being inferred) is extended.
fn require_effect(cxt : Cxt, item : Val) -> Unit raise ElabError {
  let item = force(item)
  if cxt.in_fun_arm && item_effect(item) is Some(n) && is_ctl_effect(n) {
    cxt.fail(
      "the handler of a tail-resumptive operation cannot perform `ctl` operations",
    )
  }
  if item is VData("%RowNil", _) {
    return
  }
  if item is VFlex(_, _) {
    // an effect variable nothing constrains: no effect
    cxt.unify(item, row_nil())
    return
  }
  let name = item_effect(item)
  match name {
    Some(n) if cxt.handled.contains(n) => return
    Some("%Exn") if cxt.can_raise => return
    Some("%AsyncE") if cxt.can_async => return
    _ => ()
  }
  let (items, tail) = row_flat(cxt.eff_row)
  for it in items {
    if item_effect(it) == name && cxt.try_unify(it, item) {
      return
    }
  }
  if name is None && cxt.try_unify(tail, item) {
    return
  }
  // the new tail lives where the old one does: same arguments
  if tail is VFlex(_, sp) {
    let m = new_meta()
    open_rows.push((m, sp.length()))
    cxt.unify(tail, row_cons(item, VFlex(m, sp)))
    return
  }
  match name {
    Some("%Exn") =>
      cxt.fail(
        "this call may raise an error; use it inside `try` or in a function declared with `raise`" +
        cxt.splice_note,
      )
    Some("%AsyncE") =>
      cxt.fail(
        "this calls an async function, which can only be done in an async function",
      )
    _ => ()
  }
  cxt.fail(
    "this performs " +
    cxt.show(item) +
    ", which is not handled here and not in the effects of the function (add `!" +
    cxt.show(item) +
    "` to its type)" +
    cxt.splice_note,
  )
}

///|
/// Tails of rows extended by `require_effect`: when nothing else is found,
/// they end the row (`finish`). The meta and its number of arguments.
let open_rows : Array[(Int32, Int32)] = []

///|
/// End the rows that are still open.
fn close_open_rows() -> Unit {
  for r in open_rows {
    let (m, n) = r
    if metas[m].sol is None {
      let mut t = Global("%RowNil")
      for _ in 0..<n {
        t = Lam("_", Expl, true, t)
      }
      metas[m].sol = Some(eval([], t))
    }
  }
  open_rows.clear()
}

///|
/// `require_row` where anything may be called (in a type): only the rows of
/// lambdas are extended.
fn require_row_lenient(cxt : Cxt, row : Val) -> Unit {
  let (items, tail) = row_flat(row)
  for it in [..items, tail] {
    require_effect(cxt, it) catch {
      _ => ()
    }
  }
}

///|
/// The code being checked calls a function with the effects `row`.
fn require_row(cxt : Cxt, row : Val) -> Unit raise ElabError {
  let (items, tail) = row_flat(row)
  for it in items {
    require_effect(cxt, it)
  }
  require_effect(cxt, tail)
}

///|
/// Unify two effect rows, as sets: the items of the same effect are unified,
/// and the rest goes to the other row's tail when it is a meta.
fn unify_rows(ts : LTypes, r1 : Val, r2 : Val) -> Unit raise UnifyError {
  let (items1, tail1) = row_flat(r1)
  let (items2, tail2) = row_flat(r2)
  let used = Array::make(items2.length(), false)
  let left1 : Array[Val] = []
  for a in items1 {
    let mut found = false
    for k = 0; k < items2.length(); k = k + 1 {
      if !used[k] && item_effect(a) == item_effect(items2[k]) {
        // the types of errors are not compared (as for `raise`)
        if item_effect(a) == Some("%Exn") {
          unify(ts, a, items2[k]) catch {
            _ => ()
          }
        } else {
          unify(ts, a, items2[k])
        }
        used[k] = true
        found = true
        break
      }
    }
    if !found {
      left1.push(a)
    }
  }
  let left2 : Array[Val] = []
  for k = 0; k < items2.length(); k = k + 1 {
    if !used[k] {
      left2.push(items2[k])
    }
  }
  let build = (xs : Array[Val], tail : Val) => {
    let mut r = tail
    for i = xs.length() - 1; i >= 0; i = i - 1 {
      r = row_cons(xs[i], r)
    }
    r
  }
  if left1.length() == 0 && left2.length() == 0 {
    // tails are `%RowNil`, effect variables or metas
    match (tail1, tail2) {
      (VData("%RowNil", _), VData("%RowNil", _)) => ()
      (VData("%RowNil", _), VRigid(_, _))
      | (VRigid(_, _), VData("%RowNil", _)) =>
        raise UnifyError("different effects")
      _ => unify(ts, tail1, tail2)
    }
  } else if left1.length() == 0 && tail1 is VFlex(_, _) {
    unify(ts, tail1, build(left2, tail2))
  } else if left2.length() == 0 && tail2 is VFlex(_, _) {
    unify(ts, tail2, build(left1, tail1))
  } else {
    raise UnifyError("different effects")
  }
}

///|
fn is_row(v : Val) -> Bool {
  v is VData("%Row" | "%RowNil", _)
}

// ---------------------------------------------------------------------------
// Effect polymorphism without annotation

///|
/// A function parameter `f : (A) -> B` without effects that does not escape
/// the call (the body only calls it, or passes it, or a lambda that only does
/// so, directly as an argument) may have any effects: the function gets an
/// effect variable `e`, added to the parameter's type and to its own. The
/// signature with `e` is the function's type.
fn auto_effects(fd : @parser.FnDecl) -> @parser.FnDecl {
  if fd.is_lemma {
    return fd
  }
  let body = match fd.body {
    BodyExpr(b) => b
    BodyExtern(_) => return fd
  }
  let params = match fd.params {
    Some(ps) => ps
    None => return fd
  }
  // not for async functions, and only when the function has no effect
  // variable of its own
  match fd.raises {
    Some(EApp(_, EVar(_, "%Async"), _, _)) => return fd
    Some(EApp(_, EVar(_, "%Effs"), Some([row, _]), _)) =>
      if !(row_exprs(row).1 is EVar(_, "%RowNil")) {
        return fd
      }
    _ => ()
  }
  let transparent = params.map(p => {
    match p.ty {
      Some(EPi(_, _, _, _, raises)) =>
        !(raises is Some(EApp(_, EVar(_, "%Effs" | "%Async"), _, _))) &&
        !escapes(body, p.name)
      _ => false
    }
  })
  if !transparent.iter().any(b => b) {
    return fd
  }
  let mut e = "e"
  let mut k = 1
  while fd.impl_params.iter().any(b => b.name == e) ||
        params.iter().any(b => b.name == e) {
    e = "e" + k.to_string()
    k = k + 1
  }
  let pos = fd.pos
  let with_e = (raises : @parser.Expr?) => {
    let err : @parser.Expr = match raises {
      Some(EApp(_, EVar(_, "%Effs"), Some([_, err]), _)) => err
      Some(err) => err
      None => EVar(pos, "%NoRaise")
    }
    let row : @parser.Expr = match raises {
      Some(EApp(_, EVar(_, "%Effs"), Some([row, _]), _)) => {
        let (items, _) = row_exprs(row)
        let mut r : @parser.Expr = EVar(pos, e)
        for i = items.length() - 1; i >= 0; i = i - 1 {
          r = EApp(pos, EVar(pos, "%Row"), Some([items[i], r]), None)
        }
        r
      }
      _ => EVar(pos, e)
    }
    Some(@parser.EApp(pos, EVar(pos, "%Effs"), Some([row, err]), None))
  }
  let params2 = params.mapi((i, p) => {
    if transparent[i] {
      match p.ty {
        Some(EPi(pp, impls, expl, cod, raises)) =>
          { ..p, ty: Some(EPi(pp, impls, expl, cod, with_e(raises))), }
        _ => p
      }
    } else {
      p
    }
  })
  {
    ..fd,
    impl_params: [
      ..fd.impl_params,
      { pos, name: e, ty: None, kind: Positional, },
    ],
    params: Some(params2),
    raises: with_e(fd.raises),
  }
}

///|
/// Does the parameter `x` (a function) escape in `e`: is it used other than
/// called, or passed directly as an argument (alone, or in a lambda that is
/// itself such an argument)?
fn escapes(e : @parser.Expr, x : String) -> Bool {
  let arg_escapes = (a : @parser.Expr) => {
    match a {
      EVar(_, y) if y == x => false
      ELam(_, _, ps, _, b) => !ps.iter().any(p => p.name == x) && escapes(b, x)
      _ => escapes(a, x)
    }
  }
  match e {
    EVar(_, y) => y == x
    // code outlives the call that makes it, but its splices run in the call
    // (staging.mbt)
    EApp(_, EVar(_, "%quote"), None, Some([ELam(_, _, _, _, b)])) =>
      code_mentions(b, x)
    EApp(_, EVar(_, "%splice"), None, Some([a])) => escapes(a, x)
    EApp(_, EVar(_, y), _, args) if y == x =>
      args.unwrap_or([]).iter().any(arg_escapes)
    EApp(_, f, impls, args) =>
      escapes(f, x) ||
      impls.unwrap_or([]).iter().any(a => escapes(a, x)) ||
      args.unwrap_or([]).iter().any(arg_escapes)
    EMethod(_, recv, _, _, args) =>
      escapes(recv, x) || args.iter().any(arg_escapes)
    EBlock(_, stmts) => stmts.iter().any(s => stmt_escapes(s, x))
    EIf(_, c, t, f) =>
      escapes(c, x) ||
      escapes(t, x) ||
      f.map(g => escapes(g, x)).unwrap_or(false)
    EMatch(_, s, _, arms) => escapes(s, x) || arms_escape(arms, x)
    ETry(_, b, arms, ok) =>
      escapes(b, x) ||
      arms_escape(arms, x) ||
      ok.map(o => arms_escape(o, x)).unwrap_or(false)
    EBin(_, _, a, b) => escapes(a, x) || escapes(b, x)
    EUn(_, _, a) | EAnn(_, a, _) | EField(_, a, _) | EUnfold(_, _, a) =>
      escapes(a, x)
    EReturn(_, v) => v.map(a => escapes(a, x)).unwrap_or(false)
    ELit(_, _) | EHole(_) | EType(_) | EProp(_) => false
    // anything else: any use is an escape
    _ => mentions(e, x)
  }
}

///|
fn arms_escape(arms : Array[@parser.Arm], x : String) -> Bool {
  arms
  .iter()
  .any(a => {
    a.cond.map(c => escapes(c, x)).unwrap_or(false) ||
    a.rhs.map(r => escapes(r, x)).unwrap_or(false)
  })
}

///|
fn stmt_escapes(s : @parser.Stmt, x : String) -> Bool {
  match s {
    SExpr(_, e) | SDefer(_, e) => escapes(e, x)
    SLet(_, _, _, v) | SLetMut(_, _, _, v) => escapes(v, x)
    SWhile(_, c, b) => escapes(c, x) || escapes(b, x)
    SForIn(_, _, it, b) => escapes(it, x) || escapes(b, x)
    SFor(_, inits, c, steps, b) =>
      inits.iter().any(i => escapes(i.1, x)) ||
      c.map(g => escapes(g, x)).unwrap_or(false) ||
      steps.iter().any(i => escapes(i.1, x)) ||
      escapes(b, x)
    SLoopX(_, _, inner, nb) =>
      stmt_escapes(inner, x) || nb.map(g => escapes(g, x)).unwrap_or(false)
    SGuard(_, c, el) =>
      escapes(c, x) || el.map(g => escapes(g, x)).unwrap_or(false)
    SAssign(_, _, _, v) => escapes(v, x)
    _ => mention_walk_stmt(s, x)
  }
}

///|
fn mention_walk_stmt(s : @parser.Stmt, x : String) -> Bool {
  let found = Ref::new(false)
  mention_walk_s(s, x, found)
  found.val
}

///|
/// Is the variable bound by `Pi(x, _, _, _, b)` only used in effect rows of
/// `b` (an effect variable)? It is erased by the native code.
pub fn only_in_rows(b : Tm) -> Bool {
  !used_outside_rows(b, 0)
}

///|
fn used_outside_rows(t : Tm, ix : Int32) -> Bool {
  match t {
    Var(j) => j == ix
    Raises(a, App(App(Global("%Effs"), _, _), err, _)) =>
      used_outside_rows(a, ix) || used_outside_rows(err, ix)
    App(f, a, _) => used_outside_rows(f, ix) || used_outside_rows(a, ix)
    Pi(_, _, _, a, b) =>
      used_outside_rows(a, ix) || used_outside_rows(b, ix + 1)
    Lam(_, _, _, b) => used_outside_rows(b, ix + 1)
    Let(_, a, v, b) =>
      used_outside_rows(a, ix) ||
      used_outside_rows(v, ix) ||
      used_outside_rows(b, ix + 1)
    Raises(a, e) => used_outside_rows(a, ix) || used_outside_rows(e, ix)
    // anything else: a use, to be safe
    Global(_) | U | PropU | Lit(_) => false
    _ => true
  }
}

///|
/// The field of a `ctl` operation in a capability: a function of the
/// operation's arguments returning the computation that performs it. `scope`
/// names the variables it is under (the marker `%m` first).
fn ctl_field(eff : String, op : String, scope : Array[String]) -> Tm {
  let n = effect_ops[op].nparams
  let args = if n == 0 {
    ["%u"]
  } else {
    Array::makei(n, k => "%a" + k.to_string())
  }
  let idx = effect_decls[eff].search(op).unwrap()
  n_tm(
    NLam(
      args,
      NCon("Op", [
        NV("%m"),
        NLit(LInt(idx)),
        NLam(["%g"], NApp(NV("%g"), args.map(a => NV(a)))),
        NLam(["%v"], NCon("Pure", [NV("%v")])),
      ]),
    ),
    scope,
  )
}

///|
/// The arms of a `ctl` operation: a function of its arguments, then of
/// `resume : (R) -> A`, whose body is translated (it calls `resume`, of the
/// effect `%Resume`). `fty` is the type of the operation's field; `ans` the
/// type of the `try`.
fn ctl_arm(
  cxt : Cxt,
  pos : Pos,
  op : String,
  oas : Array[@parser.Arm],
  fty : Val,
  ans : Val,
) -> Tm raise ElabError {
  let mut c = cxt
  let mut t = force(fty)
  let names : Array[String] = []
  while t is VPi(_, Expl, g, a, cl) && (names.length() == 0 || !g) {
    let x = "%a" + names.length().to_string()
    names.push(x)
    let v = v_var(c.lvl)
    c = c.bind(x, a)
    t = force(inst(cl, v))
  }
  let resume_row = App(
    App(
      Global("%Effs"),
      App(App(Global("%Row"), Global("%Resume"), Impl), Global("%RowNil"), Impl),
      Impl,
    ),
    Global("%NoRaise"),
    Impl,
  )
  let rty = VPi("v", Expl, true, t, {
    env: c.env,
    body: Raises(quote(c.lvl + 1, ans), resume_row),
  })
  let c2 = {
    ..c.bind("resume", rty),
    handled: [..cxt.handled, "%Resume"],
    arm_lams: false,
    in_fun_arm: false,
  }
  let n = effect_ops[op].nparams
  let arms2 : Array[@parser.Arm] = []
  for a in oas {
    let args = match arm_op(a) {
      Some((_, ps)) => ps
      None => []
    }
    if args.length() != n {
      c
      .at(a.pos)
      .fail(
        op +
        " takes " +
        n.to_string() +
        " argument(s), got " +
        args.length().to_string(),
      )
    }
    let pat : @parser.Pat = match args.length() {
      0 => PWild(a.pos)
      1 => args[0]
      _ => PTuple(a.pos, args)
    }
    let rhs = match a.rhs {
      Some(r) => r
      None => c.at(a.pos).fail("missing handler body")
    }
    arms2.push({ pos: a.pos, pat, cond: a.cond, rhs: Some(rhs), })
  }
  let scrut : @parser.Expr = match n {
    0 => ELit(pos, LUnit)
    1 => EVar(pos, names[0])
    _ => ETuple(pos, names.map(x => @parser.EVar(pos, x)))
  }
  let body = check(c2, EMatch(pos, scrut, None, arms2), ans)
  let row = App(
    App(Global("%Row"), Global("%Resume"), Impl),
    Global("%RowNil"),
    Impl,
  )
  // not a function frame: `return` in an arm leaves the enclosing function
  let mut out = Lam("resume", Expl, true, mark("%marm", row, body))
  for k = names.length() - 1; k >= 0; k = k - 1 {
    out = Lam(names[k], Expl, true, out)
  }
  out
}

///|
/// `(i, p, resume) => match i { k => p(arm_k)(resume) }` (in the context of
/// the arms).
fn dispatch_tm(eff : String, ops : Array[String], arms : Array[Tm]) -> Tm {
  let cls : Array[Clause] = []
  for j = 0; j < ops.length(); j = j + 1 {
    let idx = effect_decls[eff].search(ops[j]).unwrap()
    // under i, p, resume and the pattern's slot
    cls.push({
      pats: [CPLit(LInt(idx))],
      cond: None,
      body: App(App(Var(2), shift_tm(arms[j], 4, 0), Expl), Var(1), Expl),
    })
  }
  cls.push({
    pats: [CPWild],
    cond: None,
    body: App(
      App(Global("abort"), any_ty(), Impl),
      Lit(LStr("unknown operation")),
      Expl,
    ),
  })
  Lam(
    "i",
    Expl,
    true,
    Lam("p", Expl, true, Lam("resume", Expl, true, Match([Var(2)], cls))),
  )
}

///|
/// Does `t` mention the global `g`?
fn mentions_global(t : Tm, g : String) -> Bool {
  let go = (x : Tm) => mentions_global(x, g)
  match t {
    Global(n) => n == g
    Lam(_, _, _, b) => go(b)
    App(f, a, _) => go(f) || go(a)
    Pi(_, _, _, a, b) => go(a) || go(b)
    Let(_, a, v, b) => go(a) || go(v) || go(b)
    Raises(a, e) => go(a) || go(e)
    Match(ss, cls) => ss.iter().any(go) || cls.iter().any(c => go(c.body))
    _ => false
  }
}
