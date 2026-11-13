///|
/// Surface syntax of MoonBit++.
pub(all) struct Pos {
  line : Int32
  col : Int32
} derive(Debug, Eq)

///|
pub fn Pos::to_string(self : Pos) -> String {
  self.line.to_string() + ":" + self.col.to_string()
}

///|
pub(all) enum Lit {
  LInt(Int32)
  LStr(String)
  LChar(Char)
  LBool(Bool)
  LUnit
  LDouble(Double)
  /// `1L`
  LInt64(Int64)
  /// `1U`
  LUInt(UInt32)
  /// `1UL`
  LUInt64(UInt64)
  /// `b'a'`
  LByte(Byte)
  /// `1.5F`
  LFloat(Float)
} derive(Debug, Eq)

///|
/// A binder `x`, `x : A` or (in parameter lists) an anonymous type `A`.
pub(all) struct Binder {
  pos : Pos
  name : String
  ty : Expr?
  kind : ParamKind
} derive(Debug)

///|
/// How a function parameter is passed (MoonBit's tagged arguments).
pub(all) enum ParamKind {
  /// `x : T`
  Positional
  /// `x~ : T`, or `x~ : T = default`
  Labelled(Expr?)
  /// `x? : T`: the parameter has type `T?` and defaults to `None`
  Optional
} derive(Debug)

///|
pub(all) enum InterpPart {
  IStr(String)
  IExpr(Expr)
} derive(Debug)

///|
pub(all) enum Expr {
  EVar(Pos, String)
  EHole(Pos)
  EType(Pos)
  EProp(Pos)
  ELit(Pos, Lit)
  EInterp(Pos, Array[InterpPart])
  /// `f[impl](expl)`; either list may be absent.
  EApp(Pos, Expr, Array[Expr]?, Array[Expr]?)
  /// `[impl](expl) -> cod raise err`
  EPi(Pos, Array[Binder], Array[Binder]?, Expr, Expr?)
  /// `fn[impl](params) -> ret { body }` or an arrow function.
  ELam(Pos, Array[Binder], Array[Binder], Expr?, Expr)
  EBlock(Pos, Array[Stmt])
  EIf(Pos, Expr, Expr, Expr?)
  EMatch(Pos, Expr, MatchRet?, Array[Arm])
  EAnn(Pos, Expr, Expr)
  /// `e.f` (field access).
  EField(Pos, Expr, String)
  /// `e.m[impl](args)`
  EMethod(Pos, Expr, String, Array[Expr]?, Array[Expr])
  EBin(Pos, String, Expr, Expr)
  EUn(Pos, String, Expr)
  ETuple(Pos, Array[Expr])
  EArray(Pos, Array[Expr])
  EStruct(Pos, Array[(String, Expr)])
  /// `try e catch { arms } noraise { arms }` (also `e catch { arms }`).
  ETry(Pos, Expr, Array[Arm], Array[Arm]?)
  ETryQ(Pos, Expr)
  ERaise(Pos, Expr)
  /// `perform Op(args)`: an operation of an effect (see doc/mbtpp/effects.md)
  EPerform(Pos, String, Array[Expr])
  EMonad(Pos, Expr)
  /// `<- e` inside a monad block.
  EBind(Pos, Expr)
  EProof(Pos, Array[Tactic])
  /// `unfold(f, g) { e }`: `f` and `g` may be unfolded while checking `e`
  /// (see doc/mbtpp/unfolding.md).
  EUnfold(Pos, Array[(Pos, String)], Expr)
  EReturn(Pos, Expr?)
  /// `break`, `break label~`, `break e`
  EBreak(Pos, String?, Expr?)
  /// `continue`, `continue label~`, `continue a, b` (in a `loop`)
  EContinue(Pos, String?, Array[Expr])
  /// `loop a, b { p, q => ... }` (with its label)
  ELoop(Pos, String?, Array[Expr], Array[Arm])
  /// `a..<b` / `a..=b`
  ERange(Pos, Expr, Expr, Bool)
  /// A tagged call argument `label=e` (`label?=e` when the flag is set).
  ETagged(Pos, String, Expr, Bool)
  /// `e is p`: whether `e` matches `p`. In the condition of an `if`,
  /// `while` or `guard`, the variables of `p` are bound in the rest of a
  /// `&&` chain and in the branch taken on success.
  EIs(Pos, Expr, Pat)
  /// `T raise E` as the result type of a lambda.
  EEff(Pos, Expr, Expr)
} derive(Debug)

///|
pub(all) struct MatchRet {
  as_name : String?
  in_ty : Expr?
  ret : Expr?
} derive(Debug)

///|
pub(all) struct Arm {
  pos : Pos
  pat : Pat
  /// `p if cond => ...`
  cond : Expr?
  rhs : Expr?
} derive(Debug)

///|
pub(all) enum Pat {
  PVar(Pos, String)
  PWild(Pos)
  /// `C[impl](expl)`
  PCon(Pos, String, Array[Pat]?, Array[Pat])
  PLit(Pos, Lit)
  PTuple(Pos, Array[Pat])
  /// `p | q`
  POr(Pos, Pat, Pat)
  /// `p as x`
  PAs(Pos, Pat, String)
  /// `[p, q, ..rest, r]`: the patterns before the `..`, the `..` (with the
  /// name of the rest, if any) and the patterns after it.
  PArray(Pos, Array[Pat], String??, Array[Pat])
  /// `lo..=hi`, `lo..<hi` (`_` for an open bound); the flag: inclusive.
  PRange(Pos, Lit?, Lit?, Bool)
  /// `{ x, y: p, .. }`: fields and their patterns (`x` alone is `x: x`);
  /// the flag: other fields are allowed (`..`).
  PStruct(Pos, Array[(String, Pat)], Bool)
  /// `x~` or `x=p` among the arguments of a constructor pattern: the field
  /// labelled `x`.
  PLabel(Pos, String, Pat)
} derive(Debug)

///|
pub(all) enum Stmt {
  SLet(Pos, Pat, Expr?, Expr)
  SLetMut(Pos, String, Expr?, Expr)
  /// `let x <- m` inside a monad block.
  SLetBind(Pos, Pat, Expr)
  SFn(Pos, FnDecl)
  SAssign(Pos, Expr, String, Expr)
  SWhile(Pos, Expr, Expr)
  /// `for x = a, y = b; cond; x = e, y = e { body }`
  SFor(Pos, Array[(String, Expr)], Expr?, Array[(String, Expr)], Expr)
  /// `for x in e { }` or `for i, x in e { }`
  SForIn(Pos, Array[String], Expr, Expr)
  /// A `while` or `for` loop with a label (`label~: while ...`) and/or a
  /// `nobreak { e }` block.
  SLoopX(Pos, String?, Stmt, Expr?)
  SExpr(Pos, Expr)
  /// `guard cond else { e }` (without `else`: a panic).
  SGuard(Pos, Expr, Expr?)
  /// `defer e`
  SDefer(Pos, Expr)
} derive(Debug)

///|
pub(all) enum Tactic {
  TIntros(Pos, Array[String])
  TExact(Pos, Expr)
  TRfl(Pos)
  TDestruct(Pos, String)
  TRewrite(Pos, Expr, Bool)
  TApply(Pos, Expr)
  TAssume(Pos, String, Expr)
  /// `unfold f, g`: `f` and `g` may be unfolded in the rest of the proof.
  TUnfold(Pos, Array[(Pos, String)])
} derive(Debug)

///|
pub(all) enum FnBody {
  BodyExpr(Expr)
  BodyExtern(String)
} derive(Debug)

///|
pub(all) struct FnDecl {
  pos : Pos
  name : String
  impl_params : Array[Binder]
  params : Array[Binder]?
  ret : Expr?
  raises : Expr?
  body : FnBody
  is_lemma : Bool
} derive(Debug)

///|
/// An operation of an effect: `Op(params) -> ret`, or `ctl Op(params) -> ret`
/// when its handlers may resume any number of times.
pub(all) struct EffOpDecl {
  pos : Pos
  name : String
  params : Array[Binder]
  ret : Expr
  ctl : Bool
} derive(Debug)

///|
/// `effect Name[params] { ops }`
pub(all) struct EffectDecl {
  pos : Pos
  name : String
  params : Array[Binder]
  ops : Array[EffOpDecl]
} derive(Debug)

///|
pub(all) struct ConDecl {
  pos : Pos
  name : String
  impl_params : Array[Binder]
  params : Array[Binder]
  ret : Expr?
} derive(Debug)

///|
pub(all) struct EnumDecl {
  pos : Pos
  name : String
  impl_params : Array[Binder]
  params : Array[Binder]?
  sig : Expr?
  cons : Array[ConDecl]
  is_error : Bool
} derive(Debug)

///|
pub(all) struct StructDecl {
  pos : Pos
  name : String
  impl_params : Array[Binder]
  params : Array[Binder]?
  fields : Array[(Pos, String, Expr)]
} derive(Debug)

///|
pub(all) struct TraitMethod {
  pos : Pos
  name : String
  impl_params : Array[Binder]
  params : Array[Binder]
  ret : Expr
  raises : Expr?
} derive(Debug)

///|
pub(all) struct TraitDecl {
  pos : Pos
  name : String
  self_kind : Expr?
  supers : Array[String]
  methods : Array[TraitMethod]
} derive(Debug)

///|
pub(all) struct ImplDecl {
  pos : Pos
  impl_params : Array[Binder]
  trait_name : String
  for_ty : Expr
  meth : String
  params : Array[Binder]
  body : Expr
} derive(Debug)

///|
pub(all) enum Decl {
  DFn(FnDecl)
  /// `lemma name[impl] : ty = e` / `let name : ty = e`
  DDef(Pos, String, Array[Binder], Expr?, Expr)
  DEnum(EnumDecl)
  DStruct(StructDecl)
  DTrait(TraitDecl)
  DImpl(ImplDecl)
  DEffect(EffectDecl)
  /// An opaque type with the given number of (implicit) parameters, e.g. a
  /// type imported from MoonBit whose definition is not visible.
  DOpaque(Pos, String, Int32)
  /// `#mbt` / `#mbt("name")` on an enum, struct or trait: it translates to
  /// the MoonBit type (trait) of the given name (`None`: a MoonBit type of
  /// the same name, generated by the compiler). The flag marks a read-only
  /// MoonBit type (it cannot be constructed, or the trait implemented).
  /// On a function: it is compiled to a public MoonBit function of that
  /// name.
  DMbt(Pos, String?, Bool, Decl)
  /// A declaration written with `pub` (`pub(all)`, ...). The visibility has
  /// no meaning in MoonBit++; it marks what may be worth exporting to
  /// MoonBit (see the `#mbt` hints).
  DPub(Decl)
  /// `derive(Show, Eq)` after an enum or struct: the traits (with their
  /// positions) whose instances the checker generates.
  DDerive(Array[(Pos, String)], Decl)
  /// `#timelimit(n)` (seconds) or `#timelimit(none)` (`None`): the time the
  /// checker may spend on the declaration.
  DLimit(Pos, Int32?, Decl)
  /// `#opaque`, `#opaque(sealed)` or `#unfold(f, g)` on a function (see
  /// doc/mbtpp/unfolding.md).
  DUnfoldAttr(Pos, UnfoldAttr, Decl)
} derive(Debug)

///|
pub(all) enum UnfoldAttr {
  /// `#opaque`: not unfolded during type checking, except where unfolded
  Opaque
  /// `#opaque(sealed)`: never unfolded outside its own definition
  Sealed
  /// `#unfold(f, g)`: `f` and `g` may be unfolded in the definition
  Unfolds(Array[(Pos, String)])
} derive(Debug)

///|
/// The declaration under its attributes.
pub fn Decl::inner(self : Decl) -> Decl {
  match self {
    DMbt(_, _, _, d)
    | DPub(d)
    | DDerive(_, d)
    | DLimit(_, _, d)
    | DUnfoldAttr(_, _, d) => d.inner()
    d => d
  }
}

///|
pub fn Expr::pos(self : Expr) -> Pos {
  match self {
    EVar(p, _)
    | EHole(p)
    | EType(p)
    | EProp(p)
    | ELit(p, _)
    | EInterp(p, _)
    | EApp(p, _, _, _)
    | EPi(p, _, _, _, _)
    | ELam(p, _, _, _, _)
    | EBlock(p, _)
    | EIf(p, _, _, _)
    | EMatch(p, _, _, _)
    | EAnn(p, _, _)
    | EField(p, _, _)
    | EMethod(p, _, _, _, _)
    | EBin(p, _, _, _)
    | EUn(p, _, _)
    | ETuple(p, _)
    | EArray(p, _)
    | EStruct(p, _)
    | ETry(p, _, _, _)
    | ETryQ(p, _)
    | ERaise(p, _)
    | EPerform(p, _, _)
    | EMonad(p, _)
    | EUnfold(p, _, _)
    | EBind(p, _)
    | EProof(p, _)
    | EReturn(p, _)
    | EBreak(p, _, _)
    | EContinue(p, _, _)
    | ELoop(p, _, _, _)
    | ERange(p, _, _, _)
    | ETagged(p, _, _, _)
    | EIs(p, _, _)
    | EEff(p, _, _) => p
  }
}

///|
pub fn Pat::pos(self : Pat) -> Pos {
  match self {
    PVar(p, _)
    | PWild(p)
    | PCon(p, _, _, _)
    | PLit(p, _)
    | PTuple(p, _)
    | POr(p, _, _)
    | PAs(p, _, _)
    | PArray(p, _, _, _)
    | PRange(p, _, _, _)
    | PStruct(p, _, _)
    | PLabel(p, _, _) => p
  }
}
