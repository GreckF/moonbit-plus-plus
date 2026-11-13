///|
/// `#mbt` types and traits: declarations that translate trivially to a
/// MoonBit type (trait), so compiled code uses the MoonBit type itself and
/// MoonBit functions over it can be called without conversion.
///
/// A `#mbt` datatype has only type parameters, no indices, no implicit
/// fields, and fields whose types are again translatable: `Int`, `Double`,
/// `Bool`, `Char`, `String`, `Unit`, type parameters, `#mbt` types and
/// (non-dependent) functions between them. A `#mbt` trait has `Self : Type`,
/// `#mbt` supertraits and non-generic methods over translatable types (with
/// `Self` among the type parameters). An `impl` of a `#mbt` trait is for a
/// translatable type, with type parameters and `#mbt` bounds only.
pub(all) struct MbtInfo {
  /// The MoonBit name (`T`, `@pkg.T`).
  name : String
  /// Whether the compiler generates the MoonBit declaration (otherwise it
  /// is an existing MoonBit type or trait).
  defined : Bool
  /// A read-only type cannot be constructed (`pub enum`), a read-only trait
  /// cannot be implemented (`pub trait`), outside its package.
  read_only : Bool
}

///|
/// `#mbt` datatypes and traits, by MoonBit++ name.
pub let mbt_types : Map[String, MbtInfo] = Map([])

///|
pub fn mbt_info(name : String) -> MbtInfo? {
  mbt_types.get(name)
}

///|
/// Names that a generated MoonBit declaration may not take.
let mbt_reserved : Array[String] = [
  "Value", "Ctl", "Foreign", "Pat", "Int", "Double", "Bool", "Char", "String", "Unit",
  "Array", "Option", "Result", "Map", "Error", "Ref", "Iter", "Show", "Eq", "Compare",
  "Hash", "Default", "Logger", "Self",
]

///|
let mbt_scalars : Array[String] = [
  "Int", "Double", "Bool", "Char", "String", "Unit",
]

///|
fn is_mbt_trait(n : String) -> Bool {
  mbt_types.contains(n) && data_info(n) is Some({ is_trait: true, .. })
}

///|
/// Does the type `t` translate to a MoonBit type? `ctx[i]` says whether the
/// variable of level `i` is a type parameter.
fn mbt_ty_ok(ctx : Array[Bool], t : Tm) -> Bool {
  match t {
    Var(ix) => {
      let i = ctx.length() - 1 - ix
      i >= 0 && ctx[i]
    }
    Global(n) if mbt_scalars.contains(n) => true
    Pi(_, Expl, true, _, _) => {
      // one argument group; the result does not depend on the arguments
      let c = ctx.copy()
      let mut cur = t
      let mut first = true
      while cur is Pi(_, Expl, g, a, b) && (first || !g) {
        first = false
        if !mbt_ty_ok(c, a) {
          return false
        }
        c.push(false)
        cur = b
      }
      match cur {
        Raises(r, _) => mbt_ty_ok(c, r)
        _ => mbt_ty_ok(c, cur)
      }
    }
    _ => {
      let args : Array[Tm] = []
      let mut h = t
      while h is App(f, a, _) {
        args.push(a)
        h = f
      }
      match h {
        // MoonBit's arrays (native code uses them)
        Global("Array") if args.length() == 1 => mbt_ty_ok(ctx, args[0])
        Global(d) if is_foreign_type(d) =>
          args.iter().all(a => mbt_ty_ok(ctx, a))
        Global(d) if mbt_types.contains(d) && !is_mbt_trait(d) =>
          match data_info(d) {
            Some(di) =>
              args.length() == di.nparams &&
              args.iter().all(a => mbt_ty_ok(ctx, a))
            None => false
          }
        _ => false
      }
    }
  }
}

///|
/// Is `d` an opaque MoonBit type (imported, like `@bigint.BigInt` or
/// `@hashmap.HashMap`, or the Prelude's `Json`)? It is the MoonBit type of the
/// same name.
pub fn is_foreign_type(d : String) -> Bool {
  match data_info(d) {
    Some(di) =>
      di.builtin &&
      !di.is_trait &&
      ![
        "Int", "Double", "Bool", "Char", "String", "Unit", "Array", "Error", "Type",
      ].contains(d)
    None => false
  }
}

///|
/// The end of the message about a type `shown` that does not translate.
fn no_mbt_type_note(shown : String) -> String {
  if shown.contains("Array[") {
    ", which does not translate to MoonBit (arrays are not supported yet)"
  } else {
    ", which has no MoonBit type"
  }
}

///|
fn starts_upper(s : String) -> Bool {
  match s.get_char(0) {
    Some(c) => c >= 'A' && c <= 'Z'
    None => false
  }
}

///|
/// Why the `#mbt` datatype `d` is not translatable (`None`: it is).
fn mbt_data_problem(d : String) -> String? {
  let di = match data_info(d) {
    Some(di) => di
    None => return Some("unknown type")
  }
  let info = mbt_types.get(d).unwrap()
  if info.defined &&
    (mbt_reserved.contains(d) || !starts_upper(d) || d.contains(".")) {
    return Some(
      d +
      " cannot be the name of a generated MoonBit type (use #mbt(\"name\") for an existing one)",
    )
  }
  if di.is_error {
    return Some("error types are not supported")
  }
  if di.is_prop {
    return Some("propositions have no MoonBit type")
  }
  if di.nindices > 0 {
    return Some("indexed types have no MoonBit type")
  }
  let mut t = globals.get(d).unwrap().ty
  for _ in 0..<di.nparams {
    match t {
      Pi(_, _, _, U, b) => t = b
      _ => return Some("only type parameters are allowed")
    }
  }
  for c in di.cons {
    let ci = con_info(c).unwrap()
    if ci.nimpl > 0 {
      return Some("constructor " + c + " has implicit fields")
    }
    if info.defined && di.fields is None && !starts_upper(short_name(c)) {
      return Some("constructor " + c + " must start with an upper case letter")
    }
    let ctx : Array[Bool] = []
    let mut ct = globals.get(c).unwrap().ty
    for _ in 0..<ci.nparams {
      match ct {
        Pi(_, _, _, _, b) => {
          ctx.push(true)
          ct = b
        }
        _ => ()
      }
    }
    for _ in 0..<ci.nargs {
      match ct {
        Pi(x, _, _, a, b) => {
          if !mbt_ty_ok(ctx, a) {
            return Some(
              "the field " +
              x +
              " of " +
              c +
              " has type " +
              show_tm(ctx.map(_ => "_"), a) +
              no_mbt_type_note(show_tm(ctx.map(_ => "_"), a)),
            )
          }
          ctx.push(false)
          ct = b
        }
        _ => ()
      }
    }
  }
  None
}

///|
/// The method fields of trait `tr` (not the supertraits).
pub fn trait_method_names(tr : String) -> Array[String] {
  match data_info(tr) {
    Some({ fields: Some(fs), .. }) => fs.filter(f => !f.has_prefix("super$"))
    _ => []
  }
}

///|
/// The supertraits of trait `tr`.
pub fn trait_supers(tr : String) -> Array[String] {
  match data_info(tr) {
    Some({ fields: Some(fs), .. }) =>
      fs
      .filter(f => f.has_prefix("super$"))
      .map(f => f.unsafe_substring(start=6, end=f.length()))
    _ => []
  }
}

///|
/// The type of method `m` of trait `tr`, in the context `[Self, inst]`.
pub fn trait_method_type(tr : String, m : String) -> Tm? {
  match globals.get(tr + "::" + m) {
    Some({ ty: Pi(_, Impl, _, _, Pi(_, Inst, _, _, fty)), .. }) => Some(fty)
    _ => None
  }
}

///|
/// Why the `#mbt` trait `tr` is not translatable.
fn mbt_trait_problem(tr : String) -> String? {
  let info = mbt_types.get(tr).unwrap()
  if info.defined &&
    (mbt_reserved.contains(tr) || !starts_upper(tr) || tr.contains(".")) {
    return Some(
      tr +
      " cannot be the name of a generated MoonBit trait (use #mbt(\"name\") for an existing one)",
    )
  }
  match globals.get(tr) {
    Some({ ty: Pi(_, _, _, U, _), .. }) => ()
    _ => return Some("Self must be a type")
  }
  for s in trait_supers(tr) {
    if !is_mbt_trait(s) {
      return Some("the supertrait " + s + " is not #mbt")
    }
  }
  for m in trait_method_names(tr) {
    match trait_method_type(tr, m) {
      Some(Pi(_, Impl, _, _, _)) =>
        return Some("the method " + m + " is generic")
      Some(Pi(_, Expl, _, _, _) as fty) if mbt_ty_ok([true, false], fty) => ()
      _ => return Some("the method " + m + " has a type with no MoonBit type")
    }
  }
  None
}

///|
/// Why the instance `name` of the `#mbt` trait `tr` cannot be a MoonBit
/// `impl`.
fn mbt_impl_problem(name : String, tr : String) -> String? {
  let info = mbt_types.get(tr).unwrap()
  if info.read_only {
    return Some(
      "the MoonBit trait " +
      info.name +
      " cannot be implemented outside its package (it is not pub(open))",
    )
  }
  let ctx : Array[Bool] = []
  let mut t = globals.get(name).unwrap().ty
  while t is Pi(_, icit, _, a, b) {
    match (icit, a) {
      (Impl, U) => ctx.push(true)
      (Inst, App(Global(tr2), Var(ix), _)) if is_mbt_trait(tr2) &&
        ix < ctx.length() &&
        ctx[ctx.length() - 1 - ix] => ctx.push(false)
      _ =>
        return Some(
          "an impl of a #mbt trait may only have type parameters with #mbt bounds",
        )
    }
    t = b
  }
  let self_ty = match t {
    App(Global(_), s, _) => s
    _ => return Some("bad instance type")
  }
  if self_ty is Var(_) || !mbt_ty_ok(ctx, self_ty) {
    return Some(
      "the type " + show_tm(ctx.map(_ => "_"), self_ty) + " has no MoonBit type",
    )
  }
  // MoonBit's orphan rule: the trait or the type must be generated here
  if !info.defined {
    let mut h = self_ty
    while h is App(f, _, _) {
      h = f
    }
    let is_local = match h {
      Global(d) =>
        match mbt_types.get(d) {
          Some(di) => di.defined
          None => false
        }
      _ => false
    }
    if !is_local {
      return Some(
        "MoonBit does not allow implementing the existing trait " +
        info.name +
        " for a type that is not generated by this program",
      )
    }
  }
  None
}

///|
/// The instances of trait `tr` (global names).
pub fn instances_of(tr : String) -> Array[String] {
  st.instances.get(tr).unwrap_or([])
}

///|
/// Constructing a value of a read-only MoonBit type is not allowed.
fn check_constructible(cxt : Cxt, name : String) -> Unit raise ElabError {
  match con_info(name) {
    Some(ci) =>
      match mbt_types.get(ci.data) {
        Some({ read_only: true, name: mn, .. }) =>
          cxt.fail(
            "cannot construct a value of the MoonBit type " +
            mn +
            " outside its package (it is not pub(all))",
          )
        _ => ()
      }
    None => ()
  }
}

///|
/// Check the `#mbt` declarations `marked` (positions and names) and the
/// instances `impls` (global name and trait). With `lenient` (imports), the
/// marks that do not hold are dropped instead of being errors.
fn check_mbt_decls(
  marked : Array[(Pos, String)],
  lenient : Bool,
) -> Unit raise ElabError {
  // dropping a mark may invalidate others: repeat until nothing changes
  let mut changed = true
  while changed {
    changed = false
    for m in marked {
      let (pos, n) = m
      if !mbt_types.contains(n) ||
        !globals.contains(n) ||
        mbt_builtin_traits.contains(n) {
        continue
      }
      let problem = if is_mbt_trait(n) {
        mbt_trait_problem(n)
      } else {
        mbt_data_problem(n)
      }
      match problem {
        Some(why) =>
          if lenient {
            mbt_types.remove(n)
            changed = true
          } else {
            empty_cxt(pos).fail("#mbt " + n + ": " + why)
          }
        None => ()
      }
    }
  }
}

///|
fn check_mbt_impls(
  impls : Array[(Pos, String, String)],
  lenient : Bool,
) -> Unit raise ElabError {
  for i in impls {
    let (pos, name, tr) = i
    if lenient ||
      !is_mbt_trait(tr) ||
      !globals.contains(name) ||
      mbt_builtin_traits.contains(tr) {
      continue
    }
    match mbt_impl_problem(name, tr) {
      Some(why) => empty_cxt(pos).fail("impl of #mbt trait " + tr + ": " + why)
      None => ()
    }
  }
}

///|
/// `#mbt` functions: MoonBit++ name -> MoonBit name. They are compiled to
/// public MoonBit functions; their signatures must translate (checked
/// here), their bodies must be in the native fragment (checked by the
/// compiler).
pub let mbt_fns : Map[String, String] = Map([])

///|
fn is_mbt_ident(s : String) -> Bool {
  match s.get_char(0) {
    Some(c) if (c >= 'a' && c <= 'z') || c == '_' =>
      s
      .iter()
      .all(c => {
        (c >= 'a' && c <= 'z') ||
        (c >= 'A' && c <= 'Z') ||
        (c >= '0' && c <= '9') ||
        c == '_'
      })
    _ => false
  }
}

///|
/// Why the `#mbt` function `f` cannot be a MoonBit function.
fn mbt_fn_problem(f : String) -> String? {
  let g = match globals.get(f) {
    Some(g) => g
    None => return Some("unknown function")
  }
  let arity = match g.kind {
    GFunc(Some(_), _, n) => n
    _ => return Some("only functions with a body can be #mbt")
  }
  let mname = mbt_fns.get(f).unwrap()
  if f == "main" {
    return Some("main cannot be #mbt")
  }
  match mname.find("::") {
    Some(i) => {
      // a method: MoonBit only allows methods of types of the package
      let ty = mname.unsafe_substring(start=0, end=i)
      let m = mname.unsafe_substring(start=i + 2, end=mname.length())
      match mbt_types.get(ty) {
        Some({ defined: true, .. }) if !is_mbt_trait(ty) => ()
        _ =>
          return Some(
            "a method must belong to a type generated by this program (a #mbt type without a name)",
          )
      }
      if !is_mbt_ident(m) {
        return Some(m + " is not a MoonBit function name")
      }
    }
    None =>
      if !is_mbt_ident(mname) {
        return Some(mname + " is not a MoonBit function name")
      }
  }
  match st.labels.get(f) {
    Some(ls) if ls.iter().any(l => l is LDefault(_, _)) =>
      return Some("default arguments are not supported")
    _ => ()
  }
  let ctx : Array[Bool] = []
  let names : Array[String] = []
  let mut t = g.ty
  for _ in 0..<arity {
    guard t is Pi(x, icit, _, a, b) else { break }
    match (icit, a) {
      (Impl, U) => ctx.push(true)
      // a value: erased, or an ordinary parameter of the MoonBit function
      // (then of a MoonBit type: checked by the code generator, which knows
      // what is erased)
      (Impl, _) => ctx.push(false)
      (Inst, App(Global(tr), Var(ix), _)) if is_mbt_trait(tr) &&
        ix < ctx.length() &&
        ctx[ctx.length() - 1 - ix] => ctx.push(false)
      (Inst, _) =>
        return Some(
          "the bound " +
          show_tm(names, a) +
          " is not a #mbt trait bound of a type parameter",
        )
      // a proof is erased: not a parameter of the MoonBit function
      (Expl, _) if is_prop_head(a) => ctx.push(false)
      (Expl, _) => {
        if !mbt_ty_ok(ctx, a) {
          return Some(
            "the parameter " +
            x +
            " has type " +
            show_tm(names, a) +
            no_mbt_type_note(show_tm(names, a)),
          )
        }
        ctx.push(false)
      }
    }
    names.push(x)
    t = b
  }
  let r = match t {
    Raises(r, _) => r
    _ => t
  }
  if !mbt_ty_ok(ctx, r) {
    return Some("the result type " + show_tm(names, r) + " has no MoonBit type")
  }
  None
}

///|
fn check_mbt_fns(fns : Array[(Pos, String)]) -> Unit raise ElabError {
  for x in fns {
    let (pos, f) = x
    match mbt_fn_problem(f) {
      Some(why) => empty_cxt(pos).fail("#mbt fn " + f + ": " + why)
      None => ()
    }
  }
}

///|
/// Declarations written with `pub` and without `#mbt` (position, name,
/// whether it is a function): candidates for a `#mbt` hint.
pub let pub_decls : Array[(Pos, String, Bool)] = []

///|
/// A `pub` declaration that could be `#mbt`.
pub(all) struct MbtHint {
  /// The source file and line of the declaration.
  file : String
  line : Int32
  name : String
  /// "type", "trait" or "fn".
  kind : String
}

///|
/// The `pub` declarations of the checked package that could be marked
/// `#mbt`. Datatypes and traits are found together (marking one may allow
/// another): all candidates are marked tentatively, and those that do not
/// hold are dropped until nothing changes. Functions are then those whose
/// signatures translate, assuming these marks, and that `native_fns` (the
/// compiler) accepts. The tentative marks are removed afterwards.
pub fn mbt_hints(
  native_fns : (Array[String]) -> Array[String],
) -> Array[MbtHint] {
  let in_package = (n : String) => {
    match global_files.get(n) {
      Some(f) => source_files.contains(f)
      None => false
    }
  }
  let types : Array[(Pos, String)] = []
  let fns : Array[(Pos, String)] = []
  for d in pub_decls {
    let (pos, n, is_fn) = d
    if !globals.contains(n) || !in_package(n) {
      continue
    }
    if is_fn {
      if !mbt_fns.contains(n) {
        fns.push((pos, n))
      }
    } else if !mbt_types.contains(n) {
      types.push((pos, n))
    }
  }
  for t in types {
    mbt_types.set(t.1, { name: t.1, defined: true, read_only: false, })
  }
  let mut changed = true
  while changed {
    changed = false
    for t in types {
      let n = t.1
      if !mbt_types.contains(n) {
        continue
      }
      let problem = if is_mbt_trait(n) {
        mbt_trait_problem(n)
      } else {
        mbt_data_problem(n)
      }
      if problem is Some(_) {
        mbt_types.remove(n)
        changed = true
      }
    }
  }
  let ok_types = types.filter(t => mbt_types.contains(t.1))
  for f in fns {
    mbt_fns.set(f.1, f.1)
  }
  let sig_ok = fns.filter(f => mbt_fn_problem(f.1) is None).map(f => f.1)
  let native = native_fns(sig_ok)
  let ok_fns = fns.filter(f => native.contains(f.1))
  // undo the tentative marks
  for f in fns {
    mbt_fns.remove(f.1)
  }
  for t in ok_types {
    mbt_types.remove(t.1)
  }
  let hint = (p : Pos, n : String, kind : String) => {
    file: global_files.get(n).unwrap(),
    line: p.line % file_stride,
    name: n,
    kind,
  }
  [
    ..ok_types.map(t => {
      hint(t.0, t.1, if is_trait_name(t.1) { "trait" } else { "type" })
    }),
    ..ok_fns.map(f => hint(f.0, f.1, "fn")),
  ]
}

///|
fn is_trait_name(n : String) -> Bool {
  data_info(n) is Some({ is_trait: true, .. })
}

///|
/// Prelude traits that are MoonBit's own traits: trait -> (MoonBit++
/// method -> MoonBit method). Unlike other `#mbt` traits, their instances
/// need not be MoonBit impls: those for `#mbt` types of the program become
/// impls of the MoonBit trait, the others are only used by the uniform
/// code (and MoonBit already has the instances for its own types).
pub let mbt_builtin_traits : Map[String, Map[String, String]] = {
  "Show": { "to_string": "to_string" },
  "Eq": { "op_equal": "equal" },
  "Compare": { "compare": "compare" },
  "Add": { "op_add": "add" },
  "Sub": { "op_sub": "sub" },
  "Mul": { "op_mul": "mul" },
  "Div": { "op_div": "div" },
  "Mod": { "op_mod": "mod" },
  "Neg": { "op_neg": "neg" },
  "Default": { "default": "default" },
  "BitAnd": { "op_land": "land" },
  "BitOr": { "op_lor": "lor" },
  "BitXOr": { "op_lxor": "lxor" },
  "Shl": { "op_shl": "shl" },
  "Shr": { "op_shr": "shr" },
  "Hash": { "hash": "hash" },
  "ToJson": { "to_json": "to_json" },
}

///|
/// The MoonBit name of method `m` of the `#mbt` trait `tr`.
pub fn mbt_method_name(tr : String, m : String) -> String {
  match mbt_builtin_traits.get(tr) {
    Some(ms) => ms.get(m).unwrap_or(m)
    None => m
  }
}
