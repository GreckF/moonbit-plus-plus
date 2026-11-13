///|
/// Core terms and semantic values.
pub(all) enum Icit {
  Expl
  Impl
  /// An instance argument, filled in by instance search.
  Inst
} derive(Eq, Debug)

///|
pub type Lit = @parser.Lit

///|
pub type Pos = @parser.Pos

///|
/// Core patterns. Every node of a pattern occupies one variable slot (the
/// value it matches); a constructor pattern is followed by the slots of its
/// arguments (the constructor's own arguments, without the datatype
/// parameters).
pub(all) enum CPat {
  CPVar(String)
  CPWild
  CPCon(String, Array[CPat])
  CPLit(Lit)
} derive(Debug)

///|
pub(all) struct Clause {
  pats : Array[CPat]
  /// `p if cond => ...`: the clause is skipped when the condition is false.
  /// Like the body, it is under the slots of the patterns.
  cond : Tm?
  body : Tm
} derive(Debug)

///|
/// Apply `f` to the guard and the body of a clause.
pub fn Clause::map(self : Clause, f : (Tm) -> Tm) -> Clause {
  { pats: self.pats, cond: self.cond.map(f), body: f(self.body), }
}

///|
pub(all) enum Tm {
  Var(Int32)
  Global(String)
  Meta(Int32)
  InsertedMeta(Int32, Array[Bool])
  /// Name, icitness, whether this explicit binder starts a new argument group.
  Lam(String, Icit, Bool, Tm)
  App(Tm, Tm, Icit)
  Pi(String, Icit, Bool, Tm, Tm)
  Let(String, Tm, Tm, Tm)
  U
  PropU
  Lit(Lit)
  Match(Array[Tm], Array[Clause])
  /// `T raise E` in the codomain of a function type.
  Raises(Tm, Tm)
  LetMut(String, Tm, Tm, Tm)
  Assign(Int32, Tm)
  /// Condition, body, step (run after the body and on `continue`).
  While(Tm, Tm, Tm)
  Break
  Continue
  Return(Tm)
  Raise(Tm)
  Try(Tm, Array[Clause])
  ArrayLit(Array[Tm])
  Seq(Tm, Tm)
  /// `defer e; body`: `e` runs when `body` is left (normally, by `return`,
  /// `break`, `continue` or an error).
  Defer(Tm, Tm)
} derive(Debug)

///|
pub type Env = Array[Val]

///|
pub type Spine = Array[(Val, Icit)]

///|
pub(all) struct Closure {
  env : Env
  body : Tm
}

///|
pub(all) enum Val {
  VRigid(Int32, Spine)
  VFlex(Int32, Spine)
  /// A function application that is kept folded (see `force`).
  VGlobal(String, Spine)
  VData(String, Spine)
  VCon(String, Spine)
  VPrim(String, Spine)
  VLam(String, Icit, Bool, Closure)
  VPi(String, Icit, Bool, Val, Closure)
  VU
  VProp
  VLit(Lit)
  VRaises(Val, Val)
  /// A match blocked on its scrutinees, applied to a spine.
  VMatch(Env, Array[Val], Array[Clause], Spine)
  /// An imperative construct; never reduces during type checking.
  VStuck(Env, Tm, Spine)
  /// An array literal (arrays are mutable, so nothing reduces on it).
  VArrLit(Array[Val])
}

///|
pub fn v_var(l : Int32) -> Val {
  VRigid(l, [])
}

///|
pub fn env_push(env : Env, v : Val) -> Env {
  let e = env.copy()
  e.push(v)
  e
}

///|
/// Number of variable slots bound by a pattern.
pub fn pat_slots(p : CPat) -> Int32 {
  match p {
    CPCon(_, ps) => {
      let mut n = 1
      for q in ps {
        n = n + pat_slots(q)
      }
      n
    }
    _ => 1
  }
}

///|
pub fn pats_slots(ps : Array[CPat]) -> Int32 {
  let mut n = 0
  for p in ps {
    n = n + pat_slots(p)
  }
  n
}

///|
pub fn apps(t : Tm, args : Array[(Tm, Icit)]) -> Tm {
  let mut r = t
  for a in args {
    r = App(r, a.0, a.1)
  }
  r
}

// ---------------------------------------------------------------------------
// Global definitions

///|
pub(all) struct DataInfo {
  name : String
  /// Number of parameter binders (all leading binders of the type that are
  /// not indices).
  nparams : Int32
  nindices : Int32
  cons : Array[String]
  mut is_prop : Bool
  /// Field names, for structs and traits.
  fields : Array[String]?
  is_trait : Bool
  is_error : Bool
  /// Built-in types (`Int`, `Array`, ...) have no constructors but are not
  /// empty.
  builtin : Bool
}

///|
pub(all) struct ConInfo {
  name : String
  data : String
  nparams : Int32
  /// Own arguments (implicit and explicit).
  nargs : Int32
  nimpl : Int32
}

///|
pub(all) enum GKind {
  /// Body (None while it is being elaborated), opaque, number of leading
  /// lambdas.
  GFunc(Tm?, Bool, Int32)
  GData(DataInfo)
  GCon(ConInfo)
  /// Primitive name, number of arguments.
  GPrim(String, Int32)
}

///|
pub(all) struct GEntry {
  name : String
  ty : Tm
  vty : Val
  mut kind : GKind
}

///|
pub let globals : Map[String, GEntry] = Map([])

///|
/// The source file of each global defined by a program (`"<prelude>"` for
/// the prelude; imported items are not recorded).
pub let global_files : Map[String, String] = Map([])

///|
/// The source files of the last checked package, in order.
pub let source_files : Array[String] = []

///|
pub fn lookup_global(name : String) -> GEntry? {
  globals.get(name)
}

///|
pub fn data_info(name : String) -> DataInfo? {
  match globals.get(name) {
    Some({ kind: GData(d), .. }) => Some(d)
    _ => None
  }
}

///|
pub fn con_info(name : String) -> ConInfo? {
  match globals.get(name) {
    Some({ kind: GCon(c), .. }) => Some(c)
    _ => None
  }
}

// ---------------------------------------------------------------------------
// Metavariables

///|
pub(all) struct MetaEntry {
  mut sol : Val?
  /// May be solved with a value that may raise (see raise.mbt): an implicit
  /// argument of a constructor or of a datatype, which assume nothing of it.
  mut lax : Bool
}

///|
pub let metas : Array[MetaEntry] = []

///|
pub fn new_meta() -> Int32 {
  metas.push({ sol: None, lax: false, })
  metas.length() - 1
}

///|
pub fn meta_sol(m : Int32) -> Val? {
  metas[m].sol
}

///|
pub fn snapshot_metas() -> Array[Val?] {
  metas.map(e => e.sol)
}

///|
pub fn restore_metas(s : Array[Val?]) -> Unit {
  for i = 0; i < metas.length(); i = i + 1 {
    metas[i].sol = if i < s.length() { s[i] } else { None }
  }
}

///|
/// Was no meta solved since the snapshot `s`?
pub fn metas_unchanged(s : Array[Val?]) -> Bool {
  for i = 0; i < metas.length(); i = i + 1 {
    let before = if i < s.length() { s[i] } else { None }
    if before is None && metas[i].sol is Some(_) {
      return false
    }
  }
  true
}

///|
pub fn reset_state() -> Unit {
  globals.clear()
  global_files.clear()
  source_files.clear()
  pub_decls.clear()
  clear_infos()
  external_instances.clear()
  mbt_derives.clear()
  mbt_types.clear()
  mbt_fns.clear()
  metas.clear()
  reset_time_limits()
  reset_unfolding()
  lifted.clear()
  lifted_count.val = 0
  raises_cache.clear()
  reset_structs()
  reset_staging()
}

///|
pub fn[T] concat(a : Array[T], b : Array[T]) -> Array[T] {
  let r = a.copy()
  for x in b {
    r.push(x)
  }
  r
}
