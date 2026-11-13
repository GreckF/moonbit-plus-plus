///|
/// Import of MoonBit package interfaces (`.mbti` files).
///
/// Each item of the interface becomes a MoonBit++ declaration whose
/// functions are external (`"@mbt:<package>.<name>"`): they have a type but
/// no definition, so they never reduce during type checking. Names of the
/// package are qualified as `@alias.name`; methods of types from other
/// packages (e.g. `Array::all`) keep their `Type::method` name.
pub(all) struct MbtiResult {
  decls : Array[Decl]
  /// Items that could not be translated (first line of each).
  skipped : Array[String]
  /// The impls of the interface, resolved by `external_impls` once the
  /// traits of all imported packages are known.
  impls : Array[MbtiImpl]
  /// Re-exported items (`pub using`), resolved like the impls.
  usings : Array[MbtiUsing]
}

///|
/// `pub using @q {type T as U}`: `name` (`@alias.U`) is `target` (`@q.T`,
/// or `T` for `@builtin`).
pub(all) struct MbtiUsing {
  pos : Pos
  name : String
  target : String
  is_type : Bool
}

///|
/// `impl[K : Show] Show for Map[K]` of an interface, with qualified names.
pub(all) struct MbtiImpl {
  pos : Pos
  params : Array[Binder]
  trait_name : String
  for_ty : Expr
  /// The first line of the item (for the list of skipped items).
  text : String
}

///|
priv struct MbtiItem {
  line : Int32
  text : String
  attrs : Array[String]
}

///|
/// Split an interface into top-level items: an item starts at column 1 and
/// continues over indented lines and closing braces. Attribute lines
/// (`#deprecated`, ...) are attached to the following item.
fn mbti_items(src : String) -> (Array[String], Array[MbtiItem]) {
  let lines = src
    .split("\n")
    .map(l => l.to_owned().trim_end(chars="\r").to_owned())
    .to_array()
  let imports : Array[String] = []
  let items : Array[MbtiItem] = []
  let mut attrs : Array[String] = []
  let mut i = 0
  while i < lines.length() {
    let line = lines[i]
    let t = line.trim(chars=" \t").to_owned()
    if t == "" || t.has_prefix("//") || t.has_prefix("package ") {
      i = i + 1
      continue
    }
    if t.has_prefix("#") {
      attrs.push(t)
      i = i + 1
      continue
    }
    // `import( ... )`, or `import { ... }` in newer interfaces
    if t.has_prefix("import(") || t.has_prefix("import {") {
      let close = if t.has_prefix("import(") { ")" } else { "}" }
      i = i + 1
      while i < lines.length() &&
            lines[i].trim(chars=" \t").to_owned() != close {
        let q = lines[i].trim(chars=" \t\",").to_owned()
        // `"path" @alias` is possible; keep the path
        let path = match q.find("\"") {
          Some(k) => q.unsafe_substring(start=0, end=k)
          None => q
        }
        if path != "" {
          imports.push(path)
        }
        i = i + 1
      }
      i = i + 1
      continue
    }
    let start = i
    let buf = StringBuilder()
    buf.write_string(line)
    i = i + 1
    while i < lines.length() &&
          (
            lines[i].has_prefix(" ") ||
            lines[i].has_prefix("\t") ||
            lines[i].has_prefix("}")
          ) {
      buf.write_char('\n')
      // attributes inside an item (e.g. on trait methods) are dropped
      let inner = lines[i].trim(chars=" \t").to_owned()
      if !inner.has_prefix("#") {
        buf.write_string(lines[i])
      }
      i = i + 1
    }
    items.push({ line: start + 1, text: buf.to_string(), attrs, })
    attrs = []
  }
  (imports, items)
}

///|
fn last_segment(path : String) -> String {
  match path.rev_find("/") {
    Some(k) => path.unsafe_substring(start=k + 1, end=path.length())
    None => path
  }
}

///|
fn binder_names(bs : Array[Binder]) -> Array[String] {
  bs.map(b => b.name)
}

///|
/// Apply `f` to every name in a type expression.
fn map_names(e : Expr, f : (Pos, String) -> Expr) -> Expr {
  let go = (x : Expr) => map_names(x, f)
  let gob = (b : Binder) => { ..b, ty: b.ty.map(go), }
  match e {
    EVar(p, n) => f(p, n)
    EApp(p, h, i, x) =>
      EApp(p, go(h), i.map(xs => xs.map(go)), x.map(xs => xs.map(go)))
    EPi(p, impls, expl, cod, raises) =>
      EPi(
        p,
        impls.map(gob),
        expl.map(bs => bs.map(gob)),
        go(cod),
        raises.map(go),
      )
    ETuple(p, es) => ETuple(p, es.map(go))
    EBin(p, op, a, b) => EBin(p, op, go(a), go(b))
    EAnn(p, a, b) => EAnn(p, go(a), go(b))
    EUn(p, op, a) => EUn(p, op, go(a))
    _ => e
  }
}

///|
/// Type names used in an expression (with the largest number of implicit
/// arguments they are applied to), not counting the names in `bound`.
fn collect_names(
  e : Expr,
  bound : Array[String],
  out : Map[String, Int32],
) -> Unit {
  let go = (x : Expr) => collect_names(x, bound, out)
  match e {
    // the effects of async functions (`%Async[E]`)
    EVar(_, n) if n.has_prefix("%") => ()
    EApp(_, EVar(_, n), Some(args), _) if n.has_prefix("%") => args.each(go)
    EVar(_, n) => if !bound.contains(n) && !out.contains(n) { out.set(n, 0) }
    EApp(_, EVar(_, n), Some(args), x) => {
      if !bound.contains(n) {
        let k = out.get(n).unwrap_or(0)
        out.set(n, if args.length() > k { args.length() } else { k })
      }
      args.each(go)
      x.map(xs => xs.each(go)) |> ignore
    }
    EApp(_, h, i, x) => {
      go(h)
      i.map(xs => xs.each(go)) |> ignore
      x.map(xs => xs.each(go)) |> ignore
    }
    EPi(_, impls, expl, cod, raises) => {
      let b2 = bound.copy()
      for b in impls {
        b.ty.map(go) |> ignore
        b2.push(b.name)
      }
      for b in expl.unwrap_or([]) {
        b.ty.map(t => collect_names(t, b2, out)) |> ignore
      }
      collect_names(cod, b2, out)
      raises.map(go) |> ignore
    }
    ETuple(_, es) => es.each(go)
    EBin(_, _, a, b) => {
      go(a)
      go(b)
    }
    EAnn(_, a, b) => {
      go(a)
      go(b)
    }
    // `&Tr`: a trait, not a type
    EUn(_, "&", _) => ()
    _ => ()
  }
}

///|
/// Names used as trait bounds (`[T : Hash + Eq]`) in a declaration.
pub fn decl_bound_names(d : Decl) -> Array[String] {
  let out : Array[String] = []
  fn add(e : Expr, out : Array[String]) -> Unit {
    match e {
      EVar(_, n) => if !out.contains(n) { out.push(n) }
      EBin(_, "+", a, b) => {
        add(a, out)
        add(b, out)
      }
      _ => ()
    }
  }

  let bs : Array[Binder] = match d.inner() {
    DFn(fd) => fd.impl_params
    DEnum(ed) => [..ed.impl_params, ..ed.cons.map(c => c.impl_params).flatten()]
    DStruct(sd) => sd.impl_params
    DTrait(td) => td.methods.map(m => m.impl_params).flatten()
    DImpl(id) => id.impl_params
    DDef(_, _, bs, _, _) => bs
    DEffect(ed) => ed.params
    DOpaque(_, _, _)
    | DMbt(_, _, _, _)
    | DPub(_)
    | DDerive(_, _)
    | DLimit(_, _, _)
    | DUnfoldAttr(_, _, _) => []
  }
  for b in bs {
    match b.ty {
      Some(t) => add(t, out)
      None => ()
    }
  }
  out
}

///|
/// Names referred to by a declaration that may be types, with their arity.
pub fn decl_type_names(d : Decl) -> Map[String, Int32] {
  let out : Map[String, Int32] = Map([])
  let tys = (bs : Array[Binder], bound : Array[String]) => {
    for b in bs {
      b.ty.map(t => collect_names(t, bound, out)) |> ignore
    }
  }
  match d.inner() {
    DFn(fd) => {
      let bound = ["Self", ..binder_names(fd.impl_params)]
      tys(fd.params.unwrap_or([]), bound)
      fd.ret.map(t => collect_names(t, bound, out)) |> ignore
      fd.raises.map(t => collect_names(t, bound, out)) |> ignore
    }
    DDef(_, _, bs, _, body) => collect_names(body, binder_names(bs), out)
    DEnum(ed) => {
      let bound = binder_names(ed.impl_params)
      for c in ed.cons {
        let b2 = bound + binder_names(c.impl_params)
        tys(c.params, b2)
        c.ret.map(t => collect_names(t, b2, out)) |> ignore
      }
    }
    DStruct(sd) => {
      let bound = binder_names(sd.impl_params)
      for f in sd.fields {
        collect_names(f.2, bound, out)
      }
    }
    DTrait(td) =>
      for m in td.methods {
        let bound = ["Self", ..binder_names(m.impl_params)]
        tys(m.params, bound)
        collect_names(m.ret, bound, out)
      }
    _ => ()
  }
  out
}

///|
/// Translate a MoonBit interface. `alias` is the name the package is
/// imported under, `aliases` maps package paths to the aliases of the other
/// imported packages.
pub fn parse_mbti(
  src : String,
  pkg_alias : String,
  pkg_path : String,
  aliases : Map[String, String],
) -> MbtiResult {
  let (imports, items) = mbti_items(src)
  let prefix = "@" + pkg_alias + "."
  // the interface refers to its own imports by their last path segment
  let import_alias : Map[String, String] = Map([])
  for path in imports {
    match aliases.get(path) {
      Some(a) => import_alias.set(last_segment(path), a)
      None => ()
    }
  }
  let raw : Array[(Decl, Array[String])] = []
  let skipped : Array[String] = []
  let usings : Array[(Int32, String)] = []
  for item in items {
    // `#deprecated` items are imported (MoonBit only warns about their uses)
    let first = match item.text.find("\n") {
      Some(k) => item.text.unsafe_substring(start=0, end=k)
      None => item.text
    }
    if first.has_prefix("pub using ") || first.has_prefix("using ") {
      usings.push((item.line, item.text))
      continue
    }
    try {
      let p = { toks: tokenize(item.text, line0=item.line), i: 0, }
      for d in mbti_item(p, pkg_path) {
        raw.push((d, item.attrs))
      }
    } catch {
      _ => skipped.push(first)
    }
  }
  // names of the types of this package
  let locals : Array[String] = []
  for r in raw {
    match r.0.inner() {
      DEnum(ed) => locals.push(ed.name)
      DStruct(sd) => locals.push(sd.name)
      DTrait(td) => locals.push(td.name)
      DOpaque(_, n, _) if builtin_alias(pkg_path, n) is None => locals.push(n)
      DDef(_, n, _, _, _) if is_type_name(n) => locals.push(n)
      _ => ()
    }
  }
  let qualify = (self_ty : String?) => {
    (p : Pos, n : String) => {
      let e : Expr = if n == "Self" && self_ty is Some(t) {
        EVar(p, t)
      } else if n == "Int32" {
        // MoonBit's `Int` is an alias of `Int32`
        EVar(p, "Int")
      } else if builtin_alias(pkg_path, n) is Some(b) {
        EVar(p, b)
      } else if locals.contains(n) {
        EVar(p, prefix + n)
      } else if n.has_prefix("@builtin.") {
        // the types and traits of `@builtin` are the global ones
        let m = n.unsafe_substring(start=9, end=n.length())
        EVar(p, if m == "Int32" { "Int" } else { m })
      } else if n.has_prefix("@") {
        // `@pkg.T` refers to an import of this interface
        match n.find(".") {
          Some(k) => {
            let a = n.unsafe_substring(start=1, end=k)
            let t = n.unsafe_substring(start=k + 1, end=n.length())
            let builtin = imports
              .iter()
              .find_first(path => last_segment(path) == a)
              .bind(path => builtin_alias(path, t))
            match import_alias.get(a) {
              _ if builtin is Some(b) => EVar(p, b)
              Some(u) =>
                EVar(p, "@" + u + n.unsafe_substring(start=k, end=n.length()))
              None => EVar(p, n)
            }
          }
          None => EVar(p, n)
        }
      } else {
        EVar(p, n)
      }
      e
    }
  }
  let decls : Array[Decl] = []
  let impls : Array[MbtiImpl] = []
  let reexports : Array[MbtiUsing] = []
  for u in usings {
    using_items(u.0, u.1, prefix, import_alias, reexports, skipped)
  }
  let qualify_trait = (tr : String) => {
    if locals.contains(tr) {
      prefix + tr
    } else {
      match map_names(EVar({ line: 0, col: 0, }, tr), qualify(None)) {
        EVar(_, n) => n
        _ => tr
      }
    }
  }
  for r in raw {
    let (d0, attrs) = r
    let first = decls.length()
    let d = d0.inner()
    match d {
      // effects are not shared between packages yet
      DMbt(_, _, _, _)
      | DPub(_)
      | DDerive(_, _)
      | DLimit(_, _, _)
      | DUnfoldAttr(_, _, _)
      | DEffect(_) => ()
      DFn(fd) => {
        let (name, self_ty) = match fd.name.find("::") {
          Some(k) => {
            let t = fd.name.unsafe_substring(start=0, end=k)
            let qt = if locals.contains(t) { prefix + t } else { t }
            (
              qt + fd.name.unsafe_substring(start=k, end=fd.name.length()),
              Some(qt),
            )
          }
          None => (prefix + fd.name, None)
        }
        let f = qualify(self_ty)
        let qb = (b : Binder) => { ..b, ty: b.ty.map(t => map_names(t, f)), }
        let fd2 = {
          ..fd,
          name,
          impl_params: fd.impl_params.map(qb),
          params: fd.params.map(ps => ps.map(qb)),
          ret: fd.ret.map(t => map_names(t, f)),
          raises: fd.raises.map(t => map_names(t, f)),
        }
        decls.push(DFn(fd2))
        // `#as_free_fn`: the method can also be called as `@pkg.name`
        if self_ty is Some(_) {
          for a in attrs {
            if a.has_prefix("#as_free_fn") && !a.contains("deprecated") {
              let m = fd.name.unsafe_substring(
                start=fd.name.find("::").unwrap() + 2,
                end=fd.name.length(),
              )
              let free = if a.has_prefix("#as_free_fn(") {
                let inner = a.unsafe_substring(start=12, end=a.length() - 1)
                inner.split(",").to_array()[0]
                .to_owned()
                .trim(chars=" ")
                .to_owned()
              } else {
                m
              }
              decls.push(DFn({ ..fd2, name: prefix + free, }))
            }
          }
        }
      }
      DDef(p, n, bs, ty, body) =>
        decls.push(DDef(p, prefix + n, bs, ty, map_names(body, qualify(None))))
      // a type that is MoonBit++'s: `@bigint.BigInt` names it
      DOpaque(p, n, _) if builtin_alias(pkg_path, n) is Some(b) =>
        decls.push(DDef(p, prefix + n, [], Some(EType(p)), EVar(p, b)))
      DOpaque(p, n, k) => decls.push(DOpaque(p, prefix + n, k))
      DEnum(ed) => {
        let f = qualify(None)
        let qb = (b : Binder) => { ..b, ty: b.ty.map(t => map_names(t, f)), }
        decls.push(
          DEnum({
            ..ed,
            name: prefix + ed.name,
            cons: ed.cons.map(c => {
              ..c,
              impl_params: c.impl_params.map(qb),
              params: c.params.map(qb),
              ret: c.ret.map(t => map_names(t, f)),
            }),
          }),
        )
      }
      DStruct(sd) => {
        let f = qualify(None)
        decls.push(
          DStruct({
            ..sd,
            name: prefix + sd.name,
            fields: sd.fields.map(x => (x.0, x.1, map_names(x.2, f))),
          }),
        )
      }
      DTrait(td) => {
        let f = qualify(None)
        let qb = (b : Binder) => { ..b, ty: b.ty.map(t => map_names(t, f)), }
        decls.push(
          DTrait({
            ..td,
            name: prefix + td.name,
            supers: td.supers.map(s => {
              if locals.contains(s) {
                prefix + s
              } else {
                s
              }
            }),
            methods: td.methods.map(m => {
              ..m,
              impl_params: m.impl_params.map(qb),
              params: m.params.map(qb),
              ret: map_names(m.ret, f),
              raises: m.raises.map(t => map_names(t, f)),
            }),
          }),
        )
      }
      DImpl(id) => {
        let f = qualify(None)
        impls.push({
          pos: id.pos,
          params: id.impl_params.map(b => {
            ..b,
            ty: b.ty.map(t => map_names(t, f)),
          }),
          trait_name: qualify_trait(id.trait_name),
          for_ty: map_names(id.for_ty, f),
          text: "impl " + id.trait_name + " for ...",
        })
      }
    }
    // a type of the package is the MoonBit type `@alias.T`
    match d0 {
      DMbt(p, _, ro, _) if decls.length() == first + 1 =>
        match decls[first] {
          DEnum({ name, .. }) | DStruct({ name, .. }) | DTrait({ name, .. }) =>
            decls[first] = DMbt(p, Some(name), ro, decls[first])
          _ => ()
        }
      _ => ()
    }
  }
  { decls, skipped, impls, usings: reexports, }
}

///|
/// The built-in type of MoonBit++ that type `name` of package `path` is.
fn builtin_alias(path : String, name : String) -> String? {
  match (path, name) {
    ("moonbitlang/core/bigint", "BigInt") => Some("BigInt")
    _ => None
  }
}

///|
fn is_type_name(n : String) -> Bool {
  match n.get_char(0) {
    Some(c) => c >= 'A' && c <= 'Z'
    None => false
  }
}

///|
/// Parse one interface item.
fn mbti_item(p : Parser, pkg_path : String) -> Array[Decl] raise ParseError {
  let pos = p.pos()
  p.skip_visibility()
  let ext = (name : String) => {
    FnBody::BodyExtern("@mbt:" + pkg_path + "." + name)
  }
  let out : Array[Decl] = match p.peek().tok {
    TSym("fn" | "async") => {
      let is_async = p.accept("async")
      p.expect("fn")
      let impl_bs = p.impl_binders()
      let mut name = p.ident()
      while p.accept("::") {
        name = name + "::" + p.ident()
      }
      // `loc~ : SourceLoc` is filled in by the MoonBit compiler: it is not
      // a parameter in MoonBit++
      let params = p
        .params(false)
        .filter(b => {
          !(b.ty
          is Some(
            EVar(
              _,
              "SourceLoc"
              | "ArgsLoc"
              | "@builtin.SourceLoc"
              | "@builtin.ArgsLoc"
            )
          ))
        })
      let ret = if p.accept("->") { p.expr() } else { EVar(pos, "Unit") }
      let raises = p.effect_opt(is_async)
      [
        DFn({
          pos,
          name,
          impl_params: impl_bs,
          params: Some(params),
          ret: Some(ret),
          raises,
          body: ext(name),
          is_lemma: false,
        }),
      ]
    }
    TSym("let") | TIdent("const") => {
      ignore(p.advance())
      let name = p.ident()
      p.expect(":")
      let ty = p.expr()
      // ignore the value of a constant
      p.i = p.toks.length() - 1
      [
        DFn({
          pos,
          name,
          impl_params: [],
          params: None,
          ret: Some(ty),
          raises: None,
          body: ext(name),
          is_lemma: false,
        }),
      ]
    }
    TIdent("type") => {
      ignore(p.advance())
      let name = p.ident()
      let bs = p.impl_binders()
      if p.accept("=") {
        [DDef(pos, name, bs, Some(EType(pos)), p.expr())]
      } else {
        // `derive(Eq, @debug.Debug)` does not matter here
        p.i = p.toks.length() - 1
        [DOpaque(pos, name, bs.length())]
      }
    }
    TSym("struct" | "enum" | "suberror" | "trait") => {
      // `pub(all)` types can be constructed and `pub(open)` traits
      // implemented outside their package
      let full = p.toks.length() > 2 &&
        p.toks[0].tok == TSym("pub") &&
        p.toks[1].tok == TSym("(") &&
        p.toks[2].tok is TIdent("all" | "open")
      let kind = p.peek().tok
      p.i = 0
      let d = p.decl()
      if kind == TSym("suberror") {
        [d]
      } else {
        [DMbt(pos, None, !full, d)]
      }
    }
    TSym("impl") => {
      ignore(p.advance())
      let bs = p.impl_binders()
      let mut tr = p.ident()
      while p.accept(".") {
        tr = tr + "." + p.ident()
      }
      p.expect("for")
      let ty = p.expr()
      [
        DImpl({
          pos,
          impl_params: bs,
          trait_name: tr,
          for_ty: ty,
          meth: "",
          params: [],
          body: EVar(pos, "_"),
        }),
      ]
    }
    _ => p.fail("unsupported interface item")
  }
  if p.peek().tok != TEOF {
    p.fail("unexpected tokens")
  }
  out
}

///|
/// `pub using @q {type T as U, f, trait Tr}`: the items of `@q` are also
/// items of this package. Types and functions are re-exported when `@q` is
/// imported (or is `@builtin`); otherwise a type is left to the opaque
/// types the checker makes for names it does not know, under this
/// package's name, which is how compiled code refers to it. Traits are not
/// re-exported (those of `@builtin` are the Prelude's anyway).
fn using_items(
  line : Int32,
  text : String,
  prefix : String,
  import_alias : Map[String, String],
  out : Array[MbtiUsing],
  skipped : Array[String],
) -> Unit {
  let pos : Pos = { line, col: 1, }
  let t = text.trim(chars=" \t\n").to_owned()
  let (q, body) = match (t.find("@"), t.find("{"), t.rev_find("}")) {
    (Some(a), Some(b), Some(c)) if a < b && b < c =>
      (
        t.unsafe_substring(start=a + 1, end=b).trim(chars=" ").to_owned(),
        t.unsafe_substring(start=b + 1, end=c),
      )
    _ => {
      skipped.push(t)
      return
    }
  }
  let source = (n : String) => {
    if q == "builtin" {
      Some(n)
    } else {
      match import_alias.get(q) {
        Some(a) => Some("@" + a + "." + n)
        None => None
      }
    }
  }
  for entry in body.split(",") {
    let e = entry.trim(chars=" \t\n").to_owned()
    if e == "" {
      continue
    }
    let words = e
      .split(" ")
      .filter(w => w != "")
      .map(w => w.to_owned())
      .to_array()
    let (kind, name, rest) = match words {
      ["type", n, .. rest] => ("type", n, rest)
      ["trait", n, .. rest] => ("trait", n, rest)
      [n, .. rest] => ("fn", n, rest)
      [] => continue
    }
    let local_name = match rest {
      ["as", u] => u
      _ => name
    }
    match (kind, source(name)) {
      ("type", Some(target)) =>
        out.push({ pos, name: prefix + local_name, target, is_type: true, })
      ("type", None) => ()
      ("fn", Some(target)) =>
        out.push({ pos, name: prefix + local_name, target, is_type: false, })
      // the traits of `@builtin` are those of the Prelude
      ("trait", _) if q == "builtin" => ()
      _ => skipped.push("pub using @" + q + " {" + e + "}")
    }
  }
}

///|
/// The instances of the impls of the imported interfaces. `traits` are the
/// known trait declarations (the Prelude's and the imported ones, with
/// qualified names); `mbt_method` gives the MoonBit trait and method that
/// implement a MoonBit++ trait method (`None`: the trait is not a MoonBit
/// trait, and its impls are not imported).
///
/// `impl[K : Show] Show for @m.Map[K]` becomes, for each method, an external
/// function calling the MoonBit trait method (`Show::to_string(x)`; MoonBit
/// finds the impl) and an instance whose methods are these functions.
pub fn external_impls(
  impls : Array[MbtiImpl],
  traits : Map[String, TraitDecl],
  mbt_method : (String, String) -> (String, String)?,
) -> (Array[Decl], Array[String]) {
  let out : Array[Decl] = []
  let skipped : Array[String] = []
  for im in impls {
    let head = match im.for_ty {
      EVar(_, n) | EApp(_, EVar(_, n), _, _) => n
      _ => {
        skipped.push(im.text)
        continue
      }
    }
    let td = match traits.get(im.trait_name) {
      Some(td) => td
      None => {
        skipped.push("impl " + im.trait_name + " for " + head)
        continue
      }
    }
    if td.methods.iter().any(m => mbt_method(td.name, m.name) is None) {
      skipped.push("impl " + im.trait_name + " for " + head)
      continue
    }
    let self_sub = (p : Pos, n : String) => {
      if n == "Self" {
        im.for_ty
      } else {
        EVar(p, n)
      }
    }
    // the type parameters of the impl, without their bounds
    let tparams = im.params.map(b => { ..b, ty: None, })
    for m in td.methods {
      let (mtr, mm) = mbt_method(td.name, m.name).unwrap()
      let ext = "ext$" + td.name + "$" + head + "$" + m.name
      let ps = m.params.mapi((k, b) => {
        ..b,
        name: "a" + k.to_string(),
        ty: b.ty.map(t => map_names(t, self_sub)),
      })
      out.push(
        DFn({
          pos: im.pos,
          name: ext,
          impl_params: [..tparams, ..m.impl_params],
          params: Some(ps),
          ret: Some(map_names(m.ret, self_sub)),
          raises: m.raises.map(t => map_names(t, self_sub)),
          body: BodyExtern("@mbt:trait:" + mtr + "::" + mm),
          is_lemma: false,
        }),
      )
      let args = ps.map(b => EVar(im.pos, b.name))
      out.push(
        DImpl({
          pos: im.pos,
          impl_params: im.params,
          trait_name: td.name,
          for_ty: im.for_ty,
          meth: m.name,
          params: ps.map(b => { ..b, ty: None, }),
          body: EApp(im.pos, EVar(im.pos, ext), None, Some(args)),
        }),
      )
    }
  }
  (out, skipped)
}
