///|
pub suberror ElabError {
  ElabError(Pos, String)
}

///|
/// Elaboration context. Variables are either bound (`bound[l]`, the value
/// is the variable itself) or defined (by `let` or by pattern refinement,
/// the value is their definition, which only mentions bound variables).
pub(all) struct Cxt {
  env : Env
  names : Array[String]
  types : Array[Val]
  bound : Array[Bool]
  muts : Array[Bool]
  lvl : Int32
  pos : Pos
  can_raise : Bool
  /// In an async function: async functions can be called.
  can_async : Bool
  ret_ty : Val?
  in_loop : Bool
  /// In a type: calls that raise and `raise e` stand for their values (see
  /// raise.mbt), since a type is not run.
  in_type : Bool
  /// The effects the code may perform (see effects.mbt): the row of the
  /// enclosing function, and the effects handled by the enclosing `try`s of
  /// the same function.
  eff_row : Val
  handled : Array[String]
  /// The lambdas being checked are handler arms: they perform their effects
  /// where the handler is, and keep its effects.
  arm_lams : Bool
  /// In the arm of a tail-resumptive operation: no `ctl` operation.
  in_fun_arm : Bool
  /// The stage of the code being checked (see staging.mbt): `code { }`
  /// raises it, `${ }` lowers it; a declaration is at stage 0.
  stage : Int32
  /// Where the stage changed: the variables from level `l` on (up to the
  /// next mark) are bound at stage `s`, for each `(l, s)`.
  stage_marks : Array[(Int32, Int32)]
  /// In `code { }`: the context where the innermost one is written (its
  /// splices that do not depend on the code are run there).
  quote_cxt : Cxt?
}

///|
pub fn empty_cxt(pos : Pos) -> Cxt {
  {
    env: [],
    names: [],
    types: [],
    bound: [],
    muts: [],
    lvl: 0,
    pos,
    can_raise: false,
    can_async: false,
    ret_ty: None,
    in_loop: false,
    in_type: false,
    eff_row: VData("%RowNil", []),
    handled: [],
    arm_lams: false,
    in_fun_arm: false,
    stage: 0,
    stage_marks: [],
    quote_cxt: None,
  }
}

///|
fn[T] push1(xs : Array[T], x : T) -> Array[T] {
  let r = xs.copy()
  r.push(x)
  r
}

///|
pub fn Cxt::bind(self : Cxt, x : String, ty : Val) -> Cxt {
  {
    ..self,
    env: push1(self.env, v_var(self.lvl)),
    names: push1(self.names, x),
    types: push1(self.types, ty),
    bound: push1(self.bound, true),
    muts: push1(self.muts, false),
    lvl: self.lvl + 1,
  }
}

///|
pub fn Cxt::bind_mut(self : Cxt, x : String, ty : Val) -> Cxt {
  let c = self.bind(x, ty)
  let muts = c.muts.copy()
  muts[c.lvl - 1] = true
  { ..c, muts, }
}

///|
pub fn Cxt::define_local(self : Cxt, x : String, ty : Val, v : Val) -> Cxt {
  {
    ..self,
    env: push1(self.env, v),
    names: push1(self.names, x),
    types: push1(self.types, ty),
    bound: push1(self.bound, false),
    muts: push1(self.muts, false),
    lvl: self.lvl + 1,
  }
}

///|
pub fn Cxt::at(self : Cxt, pos : Pos) -> Cxt {
  { ..self, pos, }
}

///|
pub fn Cxt::ltypes(self : Cxt) -> LTypes {
  self.types.map(t => Some(t))
}

///|
pub fn Cxt::eval(self : Cxt, t : Tm) -> Val {
  eval(self.env, t)
}

///|
pub fn Cxt::quote(self : Cxt, v : Val) -> Tm {
  quote(self.lvl, v)
}

///|
/// Re-evaluate a value in this context (after refinement).
pub fn Cxt::subst(self : Cxt, v : Val) -> Val {
  eval(self.env, quote(self.lvl, v))
}

///|
pub fn Cxt::lookup(self : Cxt, x : String) -> Int32? {
  for l = self.lvl - 1; l >= 0; l = l - 1 {
    if self.names[l] == x {
      return Some(l)
    }
  }
  None
}

///|
pub fn[T] Cxt::fail(self : Cxt, msg : String) -> T raise ElabError {
  raise ElabError(self.pos, msg)
}

///|
pub fn Cxt::fresh_meta(self : Cxt) -> Tm {
  InsertedMeta(new_meta(), self.bound.copy())
}

///|
pub fn Cxt::show(self : Cxt, v : Val) -> String {
  show_tm(self.names, self.quote(v))
}

///|
pub fn Cxt::unify(
  self : Cxt,
  expected : Val,
  actual : Val,
) -> Unit raise ElabError {
  // the hint about opaque functions is about the failing unification
  blocked_opaque.clear()
  unify(self.ltypes(), expected, actual) catch {
    UnifyError(_) =>
      self.fail(
        "type mismatch\n  expected: " +
        self.show(expected) +
        "\n  actual:   " +
        self.show(actual),
      )
  }
  blocked_opaque.clear()
}

///|
pub fn Cxt::try_unify(self : Cxt, a : Val, b : Val) -> Bool {
  let snap = snapshot_metas()
  try {
    unify(self.ltypes(), a, b)
    true
  } catch {
    _ => {
      restore_metas(snap)
      false
    }
  }
}

///|
/// Define a bound variable (pattern refinement) and re-substitute the
/// context.
pub fn Cxt::define_var(self : Cxt, x : Int32, v : Val) -> Cxt {
  let env = self.env.copy()
  env[x] = v
  let lvl = self.lvl
  let env2 = env.map(e => eval(env, quote(lvl, e)))
  let bound = self.bound.copy()
  bound[x] = false
  let types = self.types.map(t => eval(env2, quote(lvl, t)))
  { ..self, env: env2, bound, types, }
}

///|
fn occurs(lvl : Int32, x : Int32, v : Val) -> Bool {
  fn sp_occ(sp : Spine) -> Bool {
    sp.iter().any(a => occurs(lvl, x, a.0))
  }

  match force_meta(v) {
    VRigid(y, sp) => y == x || sp_occ(sp)
    VFlex(_, sp)
    | VGlobal(_, sp)
    | VData(_, sp)
    | VCon(_, sp)
    | VPrim(_, sp)
    | VStuck(_, _, sp) => sp_occ(sp)
    VArrLit(vs) => vs.iter().any(a => occurs(lvl, x, a))
    VLam(_, _, _, cl) => occurs(lvl + 1, x, inst(cl, v_var(lvl)))
    VPi(_, _, _, a, cl) =>
      occurs(lvl, x, a) || occurs(lvl + 1, x, inst(cl, v_var(lvl)))
    VMatch(_, vs, _, sp) => vs.iter().any(a => occurs(lvl, x, a)) || sp_occ(sp)
    VRaises(a, b) => occurs(lvl, x, a) || occurs(lvl, x, b)
    VU | VProp | VLit(_) => false
  }
}

///|
pub(all) enum Refined {
  ROk(Cxt)
  RConflict
  RStuck(String)
}

///|
/// Solve equations between values by refining bound variables (dependent
/// pattern matching unification).
pub fn Cxt::refine(self : Cxt, eqs0 : Array[(Val, Val)]) -> Refined {
  let eqs = eqs0.copy()
  let mut cur = self
  while eqs.length() > 0 {
    let (a0, b0) = eqs.remove(0)
    let a = force(cur.subst(a0))
    let b = force(cur.subst(b0))
    match (a, b) {
      (VRigid(x, []), VRigid(y, [])) if x == y => continue
      (VRigid(x, []), VRigid(y, [])) if cur.bound[x] && cur.bound[y] =>
        cur = if x > y { cur.define_var(x, b) } else { cur.define_var(y, a) }
      (VRigid(x, []), other) | (other, VRigid(x, [])) if cur.bound[x] =>
        if occurs(cur.lvl, x, other) {
          if other is VCon(_, _) {
            return RConflict
          }
          return RStuck("cyclic equation")
        } else {
          cur = cur.define_var(x, other)
        }
      (VCon(c1, sp1), VCon(c2, sp2)) => {
        if c1 != c2 {
          return RConflict
        }
        if sp1.length() != sp2.length() {
          return RStuck("constructor arity")
        }
        for k = 0; k < sp1.length(); k = k + 1 {
          eqs.push((sp1[k].0, sp2[k].0))
        }
      }
      (VLit(l1), VLit(l2)) => if !lit_same(l1, l2) { return RConflict }
      (VLit(_), VCon(_, _)) | (VCon(_, _), VLit(_)) => return RConflict
      // an error is not a value, and errors are equal when they are the same
      // error (see raise.mbt)
      (VPrim("%raise", [(e1, _), ..]), VPrim("%raise", [(e2, _), ..])) =>
        eqs.push((e1, e2))
      (VPrim("%raise", _), VLit(_) | VCon(_, _))
      | (VLit(_) | VCon(_, _), VPrim("%raise", _)) => return RConflict
      _ =>
        if !cur.try_unify(a, b) {
          return RStuck(cur.show(a) + " = " + cur.show(b))
        }
    }
  }
  ROk(cur)
}
