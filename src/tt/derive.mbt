///|
/// `derive(Show, Eq, Compare)` on enums and structs: the instances are
/// generated as MoonBit++ source and checked like hand-written ones. They
/// are written on the line of the `derive`, so that errors (e.g. a field
/// whose type has no `Show`) are reported there.
///
/// - `Show`: `C(x, y)` for constructors, `{x: 1, y: 2}` for structs;
/// - `Eq`: the same constructor with equal fields;
/// - `Compare`: by constructor (in declaration order), then by fields from
///   left to right. `Compare` needs `Eq` (derive both).
/// - `Hash`: the constructor's position and the hashes of the fields.
///
/// Type parameters get the derived trait as a bound: `enum Tree[T] derive(Eq)`
/// gives `impl[T : Eq] Eq for Tree[T]`. Indexed types, GADT constructors and
/// explicit parameters are not supported.
let derivable : Array[String] = [
  "Show", "Eq", "Compare", "Hash", "DecEq", "ToJson", "FromJson", "Debug",
]

///|
/// Traits derived by MoonBit itself: for a `#mbt` type, the generated
/// MoonBit declaration carries `derive(...)` and the MoonBit++ instance
/// calls MoonBit's method (so it runs in compiled programs only).
let mbt_derivable : Array[String] = ["ToJson", "FromJson", "Debug"]

///|
/// The MoonBit `derive`s of the `#mbt` types (by MoonBit++ name).
pub let mbt_derives : Map[String, Array[String]] = @percheck.map()

///|
/// Lines with generated code: no editor information is recorded there.
pub let derived_lines : Array[Int32] = @percheck.array()

///|
/// The declarations with their `derive`s replaced by the generated impls.
fn expand_derives(
  decls : Array[@parser.Decl],
) -> Array[@parser.Decl] raise ElabError {
  let out : Array[@parser.Decl] = []
  for d in decls {
    let ds : Array[(Pos, String)] = []
    out.push(strip_derives(d, ds))
    // `DecEq` needs `Eq`
    match ds.iter().find_first(x => x.1 == "DecEq") {
      Some((p, _)) if !ds.iter().any(x => x.1 == "Eq") => ds.push((p, "Eq"))
      _ => ()
    }
    for x in ds {
      let (p, tr) = x
      for g in derived_impls(d.inner(), p, tr, generated_mbt(d)) {
        out.push(g)
      }
    }
  }
  out
}

///|
fn strip_derives(d : @parser.Decl, ds : Array[(Pos, String)]) -> @parser.Decl {
  match d {
    DMbt(p, n, ro, x) => DMbt(p, n, ro, strip_derives(x, ds))
    DPub(x) => DPub(strip_derives(x, ds))
    DLimit(p, l, x) => DLimit(p, l, strip_derives(x, ds))
    DDerive(xs, x) => {
      for y in xs {
        ds.push(y)
      }
      strip_derives(x, ds)
    }
    _ => d
  }
}

///|
/// Is the type declared `#mbt` (without a MoonBit name, so that the compiler
/// generates its MoonBit declaration)?
fn generated_mbt(d : @parser.Decl) -> Bool {
  match d {
    DMbt(_, None, _, _) => true
    DPub(x) | DDerive(_, x) | DLimit(_, _, x) => generated_mbt(x)
    _ => false
  }
}

///|
/// The imported trait `@pkg.<short>` (e.g. `@json.FromJson`), if any.
fn imported_trait(short : String) -> String? {
  for name, info in mbt_types {
    if name.has_prefix("@") &&
      name.has_suffix("." + short) &&
      data_info(name) is Some({ is_trait: true, .. }) {
      ignore(info)
      return Some(name)
    }
  }
  None
}

///|
/// The impl of `tr` for the type declared by `d`, parsed.
fn derived_impls(
  d : @parser.Decl,
  p : Pos,
  tr : String,
  is_mbt : Bool,
) -> Array[@parser.Decl] raise ElabError {
  let cx = empty_cxt(p)
  if !derivable.contains(tr) {
    cx.fail(
      "derive(" + tr + ") is not supported (only " + derivable.join(", ") + ")",
    )
  }
  let (name, tparams) = match d {
    DEnum({ name, impl_params, params, sig, cons, is_error, .. }) => {
      if is_error {
        cx.fail("derive is not supported for error types")
      }
      if params is Some(_) || sig is Some(_) {
        cx.fail("derive is not supported for indexed types (" + name + ")")
      }
      for c in cons {
        if c.ret is Some(_) {
          cx.fail(
            "derive is not supported for constructors with a return type (" +
            name +
            "::" +
            c.name +
            ")",
          )
        }
      }
      (name, impl_params)
    }
    DStruct({ name, impl_params, params, .. }) => {
      if params is Some(_) {
        cx.fail(
          "derive is not supported for structs with parameters (" + name + ")",
        )
      }
      (name, impl_params)
    }
    _ => cx.fail("derive applies to enums and structs")
  }
  for b in tparams {
    match b.ty {
      None | Some(EType(_)) => ()
      _ =>
        cx.fail(
          "derive needs type parameters only, but " +
          name +
          " has the parameter " +
          b.name,
        )
    }
  }
  let ts = tparams.map(b => b.name)
  let head = if ts.length() == 0 {
    name
  } else {
    name + "[" + ts.join(", ") + "]"
  }
  let bounds = if ts.length() == 0 {
    ""
  } else {
    "[" + ts.map(t => t + " : " + tr).join(", ") + "]"
  }
  if mbt_derivable.contains(tr) {
    return mbt_derived(cx, p, tr, name, ts, head, is_mbt)
  }
  let impl_head = "impl" + bounds + " " + tr + " for " + head + " with "
  let body = match d {
    DEnum(ed) => {
      let cons = ed.cons.map(c => {
        (name + "::" + c.name, c.name, c.params.length())
      })
      enum_body(tr, cons)
    }
    DStruct(sd) => struct_body(tr, sd.fields.map(f => f.1))
    _ => ""
  }
  let src = impl_head + body
  derived_lines.push(p.line)
  let ds = @parser.parse_program(src, line0=p.line) catch {
    @parser.ParseError(_, msg) =>
      cx.fail("internal error in derive(" + tr + "): " + msg + "\n" + src)
  }
  // the impls belong to the file of the type
  match global_files.get(name) {
    Some(f) => record_file(ds, f)
    None => ()
  }
  ds
}

///|
fn vars(x : String, n : Int32) -> Array[String] {
  Array::makei(n, k => x + k.to_string())
}

///|
fn con_pat(c : String, xs : Array[String]) -> String {
  if xs.length() == 0 {
    c
  } else {
    c + "(" + xs.join(", ") + ")"
  }
}

///|
/// `x0.compare(y0)`, then the next fields while they are equal.
fn lex_compare(xs : Array[String], ys : Array[String]) -> String {
  if xs.length() == 0 {
    return "0"
  }
  let mut code = xs[xs.length() - 1] + ".compare(" + ys[ys.length() - 1] + ")"
  for k = xs.length() - 2; k >= 0; k = k - 1 {
    code = "{ let c = " +
      xs[k] +
      ".compare(" +
      ys[k] +
      "); if c == 0 { " +
      code +
      " } else { c } }"
  }
  code
}

///|
/// The method of `tr` for an enum with constructors (qualified name, name,
/// number of explicit fields).
fn enum_body(tr : String, cons : Array[(String, String, Int32)]) -> String {
  match tr {
    "Hash" => {
      let arms = cons.mapi((k, c) => {
        let (q, _, n) = c
        let xs = vars("x", n)
        con_pat(q, xs) + " => " + hash_fold(k.to_string(), xs)
      })
      "hash(self) { match self { " + arms.join("; ") + " } }"
    }
    "Show" => {
      let arms = cons.map(c => {
        let (q, short, n) = c
        let xs = vars("x", n)
        let shown = if n == 0 {
          short.escape()
        } else {
          (short + "(").escape() +
          " + " +
          xs.map(x => x + ".to_string()").join(" + \", \" + ") +
          " + \")\""
        }
        con_pat(q, xs) + " => " + shown
      })
      "to_string(self) { match self { " + arms.join("; ") + " } }"
    }
    "DecEq" => {
      let arms = cons.map(c => {
        let (q, _, n) = c
        let xs = vars("x", n)
        let ys = vars("y", n)
        "(" +
        con_pat(q, xs) +
        ", " +
        con_pat(q, ys) +
        ") => " +
        deq_chain(xs, ys)
      })
      // different constructors: their equality is impossible
      for c1 in cons {
        for c2 in cons {
          if c1.0 != c2.0 {
            arms.push(
              "(" +
              con_pat(c1.0, Array::make(c1.2, "_")) +
              ", " +
              con_pat(c2.0, Array::make(c2.2, "_")) +
              ") => No(h => match h {})",
            )
          }
        }
      }
      "deq(a, b) { match (a, b) { " + arms.join("; ") + " } }"
    }
    "Eq" => {
      let arms = cons.map(c => {
        let (q, _, n) = c
        let xs = vars("x", n)
        let ys = vars("y", n)
        let eq = if n == 0 {
          "true"
        } else {
          xs.mapi((k, x) => x + " == " + ys[k]).join(" && ")
        }
        "(" + con_pat(q, xs) + ", " + con_pat(q, ys) + ") => " + eq
      })
      "op_equal(a, b) { match (a, b) { " +
      [..arms, "_ => false"].join("; ") +
      " } }"
    }
    _ => {
      let arms = cons.map(c => {
        let (q, _, n) = c
        let xs = vars("x", n)
        let ys = vars("y", n)
        "(" +
        con_pat(q, xs) +
        ", " +
        con_pat(q, ys) +
        ") => " +
        lex_compare(xs, ys)
      })
      // different constructors: by position
      let tag = (v : String) => {
        "match " +
        v +
        " { " +
        cons
        .mapi((k, c) => {
          con_pat(c.0, Array::make(c.2, "_")) + " => " + k.to_string()
        })
        .join("; ") +
        " }"
      }
      "compare(a, b) { match (a, b) { " +
      [
        ..arms,
        "_ => { let ta = " +
        tag("a") +
        "; let tb = " +
        tag("b") +
        "; ta.compare(tb) }",
      ].join("; ") +
      " } }"
    }
  }
}

///|
/// The method of `tr` for a struct with the given fields.
fn struct_body(tr : String, fields : Array[String]) -> String {
  match tr {
    "DecEq" => {
      let xs = vars("x", fields.length())
      let ys = vars("y", fields.length())
      let pat = (vs : Array[String]) => {
        "{ " + fields.mapi((k, f) => f + ": " + vs[k]).join(", ") + " }"
      }
      "deq(a, b) { match (a, b) { (" +
      pat(xs) +
      ", " +
      pat(ys) +
      ") => " +
      deq_chain(xs, ys) +
      " } }"
    }
    "Hash" =>
      "hash(self) { " + hash_fold("0", fields.map(f => "self." + f)) + " }"
    "Show" => {
      let parts = fields.mapi((k, f) => {
        let sep = if k == 0 { "" } else { ", " }
        (sep + f + ": ").escape() + " + self." + f + ".to_string()"
      })
      "to_string(self) { " + ["\"{\"", ..parts, "\"}\""].join(" + ") + " }"
    }
    "Eq" => {
      let eq = if fields.length() == 0 {
        "true"
      } else {
        fields.map(f => "a." + f + " == b." + f).join(" && ")
      }
      "op_equal(a, b) { " + eq + " }"
    }
    _ =>
      "compare(a, b) { " +
      lex_compare(fields.map(f => "a." + f), fields.map(f => "b." + f)) +
      " }"
  }
}

///|
/// `Yes(Refl)` when `DecEq::deq(x_k, y_k)` proves each pair equal: the
/// proofs are matched with `Refl`, which unifies the fields; otherwise `No`
/// with the refutation of the pair (by matching an equality of the values).
fn deq_chain(xs : Array[String], ys : Array[String]) -> String {
  let mut code = "Yes(Refl)"
  for k = xs.length() - 1; k >= 0; k = k - 1 {
    code = "match DecEq::deq(" +
      xs[k] +
      ", " +
      ys[k] +
      ") { Yes(p\{k}) => match p\{k} { Refl => " +
      code +
      " }; No(n\{k}) => No(h => match h { Refl => n\{k}(Refl) }) }"
  }
  code
}

///|
/// `h * 31 + x.hash()` for each `x`, starting from `start`.
fn hash_fold(start : String, xs : Array[String]) -> String {
  let mut code = start
  for x in xs {
    code = "(" + code + ") * 31 + " + x + ".hash()"
  }
  code
}

///|
/// `derive(ToJson)`, `derive(FromJson)`, `derive(Debug)` of a `#mbt` type:
/// MoonBit derives the impl; the MoonBit++ instance calls it.
fn mbt_derived(
  cx : Cxt,
  p : Pos,
  tr : String,
  name : String,
  ts : Array[String],
  head : String,
  is_mbt : Bool,
) -> Array[@parser.Decl] raise ElabError {
  if !is_mbt {
    cx.fail(
      "derive(" + tr + ") uses MoonBit's derive, so " + name + " must be #mbt",
    )
  }
  // the MoonBit++ trait, its MoonBit name, and the instance's method
  let (trait_name, mbt_name, sig) = match tr {
    "ToJson" =>
      (
        "ToJson",
        "ToJson",
        Some(("to_json", "(a0 : " + head + ") -> Json", "a0")),
      )
    "FromJson" =>
      match imported_trait("FromJson") {
        Some(t) => {
          let pre = t.unsafe_substring(start=0, end=t.length() - 8)
          (
            t,
            mbt_info(t).unwrap().name,
            Some(
              (
                "from_json",
                "(a0 : Json, a1 : " +
                pre +
                "JsonPath) -> " +
                head +
                " raise " +
                pre +
                "JsonDecodeError",
                "a0, a1",
              ),
            ),
          )
        }
        None =>
          cx.fail(
            "derive(FromJson) needs the package moonbitlang/core/json in the imports of the package",
          )
      }
    _ =>
      match imported_trait("Debug") {
        Some(t) => {
          let pre = t.unsafe_substring(start=0, end=t.length() - 5)
          (
            t,
            "Debug",
            Some(("to_repr", "(a0 : " + head + ") -> " + pre + "Repr", "a0")),
          )
        }
        // without `@debug` there is no trait to give an instance of
        None => ("Debug", "Debug", None)
      }
  }
  match mbt_derives.get(name) {
    Some(xs) => xs.push(mbt_name)
    None => mbt_derives.set(name, [mbt_name])
  }
  let (m, params, args) = match sig {
    Some(x) => x
    None => return []
  }
  let ext = "mbtpp_derived_" + tr + "_" + name.replace_all(old=".", new="_")
  let tparams = if ts.length() == 0 { "" } else { "[" + ts.join(", ") + "]" }
  let bounds = if ts.length() == 0 {
    ""
  } else {
    "[" + ts.map(t => t + " : " + trait_name).join(", ") + "]"
  }
  let src = "fn" +
    tparams +
    " " +
    ext +
    params +
    " = \"@mbt:trait:" +
    mbt_name +
    "::" +
    m +
    "\"; impl" +
    bounds +
    " " +
    trait_name +
    " for " +
    head +
    " with " +
    m +
    "(" +
    args +
    ") { " +
    ext +
    "(" +
    args +
    ") }"
  derived_lines.push(p.line)
  let ds = @parser.parse_program(src, line0=p.line) catch {
    @parser.ParseError(_, msg) =>
      cx.fail("internal error in derive(" + tr + "): " + msg + "\n" + src)
  }
  match global_files.get(name) {
    Some(f) => record_file(ds, f)
    None => ()
  }
  // MoonBit has the impl: the compiler does not generate it
  let key = "impl$" + trait_name + "$" + name
  if !external_instances.contains(key) {
    external_instances.push(key)
  }
  ds
}
