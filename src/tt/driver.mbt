///|
/// Entry points of the type checker.
fn builtin_data(
  name : String,
  ty : Tm,
  nparams : Int32,
  is_error : Bool,
) -> Unit {
  register(
    name,
    ty,
    GData({
      name,
      nparams,
      nindices: 0,
      cons: [],
      is_prop: false,
      fields: None,
      is_trait: false,
      is_error,
      builtin: true,
    }),
  )
}

///|
/// Reset all state and install the built-in types.
pub fn setup() -> Unit {
  reset_state()
  reset_elab()
  for
    n in [
      "Int", "String", "Char", "Bool", "Unit", "Double", "Int64", "UInt", "UInt64",
      "Byte", "Float", "BigInt",
    ] {
    builtin_data(n, U, 0, false)
  }
  builtin_data("Error", U, 0, true)
  builtin_data("Array", Pi("T", Impl, false, U, U), 1, false)
  setup_staging()
}

///|
pub suberror CheckError {
  CheckError(String)
}

///|
fn format_pos(file : String, p : Pos) -> String {
  file + ":" + p.line.to_string() + ":" + p.col.to_string()
}

///|
/// The globals a declaration defines.
fn decl_global_names(d : @parser.Decl) -> Array[String] {
  match d {
    DMbt(_, _, _, inner)
    | DPub(inner)
    | DDerive(_, inner)
    | DLimit(_, _, inner)
    | DUnfoldAttr(_, _, inner) => decl_global_names(inner)
    DFn(fd) => [fd.name]
    DDef(_, n, _, _, _) | DOpaque(_, n, _) => [n]
    DEnum(ed) => [ed.name, ..ed.cons.map(c => ed.name + "::" + c.name)]
    DStruct(sd) =>
      [sd.name, sd.name + "::mk", ..sd.fields.map(f => sd.name + "::" + f.1)]
    DTrait(td) =>
      [
        td.name,
        td.name + "::mk",
        ..td.methods.map(m => td.name + "::" + m.name),
        ..td.supers.map(s => td.name + "::super$" + s),
      ]
    DImpl(id) => ["impl$" + id.trait_name + "$" + impl_head(id.for_ty)]
    DEffect(ed) =>
      [ed.name, ed.name + "::mk", ..ed.ops.map(o => ed.name + "::" + o.name)]
  }
}

///|
/// Remember that the declarations come from `file`.
fn record_file(decls : Array[@parser.Decl], file : String) -> Unit {
  for d in decls {
    for n in decl_global_names(d) {
      global_files.set(n, file)
    }
  }
}

///|
fn check_src(file : String, src : String) -> Unit raise CheckError {
  let decls = @parser.parse_program(src) catch {
    @parser.ParseError(p, msg) =>
      raise CheckError(format_pos(file, p) + ": parse error: " + msg)
  }
  // MoonBit's `Json` is an opaque type of the Prelude; `%Async[E]` and
  // `%NoRaise` are the effects of async functions (see async.mbt)
  let decls = if file == "<prelude>" {
    [
      @parser.DOpaque({ line: 0, col: 0, }, "Json", 0),
      @parser.DOpaque({ line: 0, col: 0, }, "%Async", 1),
      @parser.DOpaque({ line: 0, col: 0, }, "%NoRaise", 0),
      // effect rows (see effects.mbt)
      @parser.DOpaque({ line: 0, col: 0, }, "%Effs", 2),
      @parser.DOpaque({ line: 0, col: 0, }, "%Row", 2),
      @parser.DOpaque({ line: 0, col: 0, }, "%RowNil", 0),
      // `ctl` operations (see ctl.mbt)
      @parser.DOpaque({ line: 0, col: 0, }, "%Any", 0),
      @parser.DOpaque({ line: 0, col: 0, }, "%Resume", 0),
      // errors and async as items of effect rows (effects.mbt)
      @parser.DOpaque({ line: 0, col: 0, }, "%Exn", 1),
      @parser.DOpaque({ line: 0, col: 0, }, "%AsyncE", 0),
      comp_decl(),
      ..decls,
    ]
  } else {
    decls
  }
  record_file(decls, file)
  check_decls(decls) catch {
    ElabError(p, msg) =>
      raise CheckError(format_pos(file, p) + ": error: " + msg)
  }
}

///|
/// An imported MoonBit package: the alias it is referred to with
/// (`@alias.name`), its path, and the text of its `.mbti` interface.
pub(all) struct Import {
  alias : String
  path : String
  mbti : String
}

///|
/// Interface items that could not be imported by the last `check_program`.
pub let import_skipped : Array[String] = []

///|
/// Types of imported packages that are other types (`@bigint.BigInt` is
/// MoonBit++'s `BigInt`).
let import_type_aliases : Map[String, String] = Map([])

///|
/// Type check a program (after the prelude and the imported interfaces).
pub fn check_program(
  file : String,
  src : String,
  prelude~ : Bool = true,
  imports~ : Array[Import] = [],
) -> Unit raise CheckError {
  check_package([(file, src)], prelude~, imports~)
}

///|
/// Lines of the k-th file of a package are numbered from `(k + 1) * stride`,
/// so that a position tells which file it is in.
let file_stride : Int32 = 1000000

///|
fn package_pos(files : Array[(String, String)], p : Pos) -> String {
  let k = p.line / file_stride - 1
  if k >= 0 && k < files.length() {
    format_pos(files[k].0, { line: p.line % file_stride, col: p.col, })
  } else {
    format_pos("<unknown>", p)
  }
}

///|
/// Type check a package: several files (name, source) sharing one scope, as
/// in MoonBit.
pub fn check_package(
  files : Array[(String, String)],
  prelude~ : Bool = true,
  imports~ : Array[Import] = [],
) -> Unit raise CheckError {
  setup()
  last_error.clear()
  prelude_nat.val = true
  if prelude {
    check_src("<prelude>", prelude_src)
  }
  import_skipped.clear()
  import_type_aliases.clear()
  load_imports(imports)
  let decls : Array[@parser.Decl] = []
  for k = 0; k < files.length(); k = k + 1 {
    let (file, src) = files[k]
    source_files.push(file)
    let ds = @parser.parse_program(src, line0=(k + 1) * file_stride + 1) catch {
      @parser.ParseError(p, msg) => {
        last_error.push((p, "parse error: " + msg))
        raise CheckError(package_pos(files, p) + ": parse error: " + msg)
      }
    }
    record_file(ds, file)
    for d in ds {
      decls.push(d)
    }
  }
  if prelude {
    prune_prelude(decls)
  }
  check_decls(decls) catch {
    ElabError(p, msg) => {
      let hints = order_hint(files, p) + opaque_hint()
      last_error.push((p, msg + hints))
      raise CheckError(package_pos(files, p) + ": error: " + msg + hints)
    }
  }
}

///|
/// The position and message of the error of the last `check_package` (for
/// editors).
pub let last_error : Array[(Pos, String)] = []

///|
/// When an error in file k may come from a function of a later file whose
/// body was not available yet (files are checked one after the other), a
/// hint to change the order.
fn order_hint(files : Array[(String, String)], p : Pos) -> String {
  let k = p.line / file_stride - 1
  if k < 0 || k >= files.length() {
    return ""
  }
  for n in unfolded_too_early {
    match global_files.get(n) {
      Some(f) =>
        match files.search_by(x => x.0 == f) {
          Some(j) if j > k =>
            return "\nhint: " +
              n +
              " is defined in " +
              f +
              ", which is checked after " +
              files[k].0 +
              ", so its definition could not be used here; the error may come from that. Files are checked in dictionary order; to check " +
              base_name(f) +
              " first, list it in the package's moon.pkg: options(\"mbtpp-order\": [ \"" +
              base_name(f) +
              "\", ... ])"
          _ => ()
        }
      None => ()
    }
  }
  ""
}

///|
fn base_name(path : String) -> String {
  let mut b = path
  for sep in ["/", "\\"] {
    match b.rev_find(sep) {
      Some(i) => b = b.unsafe_substring(start=i + 1, end=b.length())
      None => ()
    }
  }
  b
}

///|
fn is_type_like(n : String) -> Bool {
  let base = match n.rev_find(".") {
    Some(k) if n.has_prefix("@") =>
      n.unsafe_substring(start=k + 1, end=n.length())
    _ => n
  }
  match base.get_char(0) {
    Some(c) => c >= 'A' && c <= 'Z' && !base.contains("::")
    None => false
  }
}

///|
fn load_imports(imports : Array[Import]) -> Unit raise CheckError {
  if imports.length() == 0 {
    return
  }
  let aliases : Map[String, String] = Map([])
  for im in imports {
    aliases.set(im.path, im.alias)
  }
  let decls : Array[@parser.Decl] = []
  // Views are taken to be the containers themselves (MoonBit converts a
  // string literal to a `StringView`, for example).
  let p0 : Pos = { line: 0, col: 0, }
  let view_aliases : Array[@parser.Decl] = [
    DDef(p0, "StringView", [], Some(EType(p0)), EVar(p0, "String")),
    DDef(
      p0,
      "ArrayView",
      [{ pos: p0, name: "T", ty: None, kind: Positional, }],
      Some(EType(p0)),
      EApp(p0, EVar(p0, "Array"), Some([EVar(p0, "T")]), None),
    ),
  ]
  for d in view_aliases {
    match d {
      DDef(_, n, _, _, _) if !globals.contains(n) => decls.push(d)
      _ => ()
    }
  }
  let impls : Array[@parser.MbtiImpl] = []
  let usings : Array[@parser.MbtiUsing] = []
  for im in imports {
    let r = @parser.parse_mbti(im.mbti, im.alias, im.path, aliases)
    for d in r.decls {
      decls.push(d)
      // `@bigint.BigInt` is `BigInt`: `@bigint.BigInt::m` is `BigInt::m`
      if d is DDef(_, n, [], Some(EType(_)), EVar(_, t)) {
        import_type_aliases.set(n, t)
      }
    }
    for s in r.skipped {
      import_skipped.push(s)
    }
    for i in r.impls {
      impls.push(i)
    }
    for u in r.usings {
      usings.push(u)
    }
  }
  reexports(usings, decls)
  // the impls, as instances of the Prelude's traits and the imported ones
  let traits : Map[String, @parser.TraitDecl] = Map([])
  let prelude_decls = @parser.parse_program(prelude_src) catch { _ => [] }
  for d in [..prelude_decls, ..decls] {
    if d.inner() is DTrait(td) {
      traits.set(td.name, td)
    }
  }
  let (ext_decls, ext_skipped) = @parser.external_impls(impls, traits, (tr, m) => {
    if mbt_builtin_traits.contains(tr) {
      Some((tr, mbt_method_name(tr, m)))
    } else if tr.has_prefix("@") {
      Some((tr, m))
    } else {
      None
    }
  })
  for d in ext_decls {
    decls.push(d)
  }
  for s in ext_skipped {
    import_skipped.push(s)
  }
  // Types that the interfaces mention but nobody defines (e.g. `Int64`,
  // `Map`, or types of packages that are not imported) become opaque.
  let declared : Array[String] = []
  for d in decls {
    match d.inner() {
      DEnum(ed) => declared.push(ed.name)
      DStruct(sd) => declared.push(sd.name)
      DTrait(td) => declared.push(td.name)
      DOpaque(_, n, _) | DDef(_, n, _, _, _) => declared.push(n)
      _ => ()
    }
  }
  // unknown traits used as bounds become opaque traits
  let bounds : Array[String] = []
  for d in decls {
    for n in @parser.decl_bound_names(d) {
      if !declared.contains(n) && !globals.contains(n) && !bounds.contains(n) {
        bounds.push(n)
      }
    }
  }
  let trait_stubs : Array[@parser.Decl] = bounds.map(n => {
    @parser.DTrait({
      pos: { line: 0, col: 0, },
      name: n,
      self_kind: None,
      supers: [],
      methods: [],
    })
  })
  for n in bounds {
    declared.push(n)
    st.opaque_traits.push(n)
  }
  let needed : Map[String, Int32] = Map([])
  for d in decls {
    for n, k in @parser.decl_type_names(d) {
      if is_type_like(n) && !declared.contains(n) && !globals.contains(n) {
        let k0 = needed.get(n).unwrap_or(0)
        needed.set(n, if k > k0 { k } else { k0 })
      }
    }
  }
  let stubs : Array[@parser.Decl] = []
  for n, k in needed {
    stubs.push(DOpaque({ line: 0, col: 0, }, n, k))
  }
  check_decls(
    concat(concat(trait_stubs, stubs), decls),
    lenient=true,
    skipped=import_skipped,
  ) catch {
    ElabError(p, msg) =>
      raise CheckError("<import>:" + p.to_string() + ": error: " + msg)
  }
  for d in ext_decls {
    if d is DImpl(id) {
      let key = "impl$" + id.trait_name + "$" + impl_head(id.for_ty)
      if globals.contains(key) && !external_instances.contains(key) {
        external_instances.push(key)
      }
    }
  }
}

///|
/// Re-exported items (`pub using`): a type becomes an alias with as many
/// parameters as its target, a function a copy of the target's declaration
/// (compiled code calls the target).
fn reexports(
  usings : Array[@parser.MbtiUsing],
  decls : Array[@parser.Decl],
) -> Unit {
  let by_name : Map[String, @parser.Decl] = Map([])
  for d in decls {
    match d.inner() {
      DEnum({ name, .. })
      | DStruct({ name, .. })
      | DFn({ name, .. })
      | DDef(_, name, _, _, _)
      | DOpaque(_, name, _) => by_name.set(name, d.inner())
      _ => ()
    }
  }
  for u in usings {
    let p = u.pos
    if u.is_type {
      let arity = match by_name.get(u.target) {
        Some(DEnum(ed)) => Some(ed.impl_params.length())
        Some(DStruct(sd)) => Some(sd.impl_params.length())
        Some(DOpaque(_, _, k)) => Some(k)
        Some(DDef(_, _, bs, _, _)) => Some(bs.length())
        _ =>
          match globals.get(u.target) {
            Some(g) => {
              let mut k = 0
              let mut t = g.ty
              while t is Pi(_, Impl, _, _, b) {
                k = k + 1
                t = b
              }
              Some(k)
            }
            None => None
          }
      }
      match arity {
        Some(k) => {
          let bs : Array[@parser.Binder] = Array::makei(k, i => {
            pos: p,
            name: "T" + i.to_string(),
            ty: None,
            kind: Positional,
          })
          let body : @parser.Expr = if k == 0 {
            EVar(p, u.target)
          } else {
            EApp(p, EVar(p, u.target), Some(bs.map(b => EVar(p, b.name))), None)
          }
          decls.push(DDef(p, u.name, bs, Some(EType(p)), body))
        }
        None => ()
      }
    } else {
      match by_name.get(u.target) {
        Some(DFn(fd)) => decls.push(DFn({ ..fd, name: u.name, }))
        _ => import_skipped.push("pub using " + u.target + " as " + u.name)
      }
    }
  }
}

///|
/// Instances of imported impls: MoonBit has them, the compiler does not
/// generate them.
pub let external_instances : Array[String] = []

///|
/// Pretty-print the type of a global.
pub fn show_global_type(name : String) -> String? {
  match globals.get(name) {
    Some(g) => Some(show_tm([], g.ty))
    None => None
  }
}

///|
/// Body of a global function, if it has one.
pub fn global_body(name : String) -> Tm? {
  match globals.get(name) {
    Some({ kind: GFunc(b, _, _), .. }) => b
    _ => None
  }
}

///|
/// Normal form of a closed term, for tests.
pub fn normalize(t : Tm) -> String {
  show_tm([], nf([], t))
}

///|
/// Tagged parameters of a top-level function, one per explicit parameter:
/// `None` for a positional one, `Some((label, optional))` for `label~` /
/// `label?` (`optional` is true for `label?`).
pub fn param_labels(name : String) -> Array[(String, Bool)?]? {
  match st.labels.get(name) {
    Some(infos) =>
      Some(
        infos.map(i => {
          match i {
            LPos => None
            LReq(l) | LDefault(l, _) => Some((l, false))
            LOpt(l) => Some((l, true))
          }
        }),
      )
    None => None
  }
}

///|
/// Names of the traits whose instances are taken for granted (unknown
/// traits of imported packages).
pub fn is_opaque_trait(name : String) -> Bool {
  st.opaque_traits.contains(name)
}

///|
/// `enum %Comp[A, B, C, D] { Pure(A); Op(Int, Int, B, C); Ret(D); Brk; Cont }`:
/// the computations of code with `ctl` operations (see ctl.mbt).
fn comp_decl() -> @parser.Decl {
  let p : Pos = { line: 0, col: 0, }
  let b = (x : String, t : String) => {
    (
      { pos: p, name: x, ty: Some(EVar(p, t)), kind: Positional, } :
      @parser.Binder)
  }
  let con = (n : String, ps : Array[@parser.Binder]) => {
    (
      { pos: p, name: n, impl_params: [], params: ps, ret: None, } :
      @parser.ConDecl)
  }
  DEnum({
    pos: p,
    name: "%Comp",
    impl_params: ["A", "B", "C", "D"].map(x => {
      (
        { pos: p, name: x, ty: Some(EType(p)), kind: Positional, } :
        @parser.Binder)
    }),
    params: None,
    sig: None,
    cons: [
      con("Pure", [b("v", "A")]),
      con("Op", [b("m", "Int"), b("i", "Int"), b("p", "B"), b("k", "C")]),
      con("Ret", [b("v", "D")]),
      con("Brk", []),
      con("Cont", []),
    ],
    is_error: false,
  })
}
