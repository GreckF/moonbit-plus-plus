///|
/// `#mbt` functions: compiled to public MoonBit functions with their own
/// names (`pub fn f[T0 : Tr](x : Int, y~ : Tree[T0]) -> Int`), which call
/// the native translation. Their bodies must be in the native fragment; a
/// function that is not is a compile error explaining the first term that
/// is not native. A function that does not `raise` in MoonBit++ does not
/// raise in MoonBit either: a run-time failure inside it aborts.

///|
/// Names of the functions of the runtime (an exported function may not
/// take one).
fn runtime_fns() -> Array[String] {
  let out : Array[String] = []
  for line in runtime_src.split("\n") {
    let l = line.to_owned()
    let rest = if l.has_prefix("fn[") {
      match l.find("] ") {
        Some(i) => l.unsafe_substring(start=i + 2, end=l.length())
        None => continue
      }
    } else if l.has_prefix("fn ") {
      l.unsafe_substring(start=3, end=l.length())
    } else {
      continue
    }
    match rest.find("(") {
      Some(i) => out.push(rest.unsafe_substring(start=0, end=i))
      None => ()
    }
  }
  out
}

///|
/// Every `#mbt` function must have a native translation.
fn Gen::check_mbt_fns(self : Gen) -> Unit raise CodegenError {
  // and the functions generated with `Value` (data.mbt)
  let reserved = [..runtime_fns(), "con_name", "con_fields"]
  for f, mname in @tt.mbt_fns {
    if reserved.contains(mname) || mname == "main" {
      raise CodegenError(
        "#mbt fn " +
        f +
        ": the name " +
        mname +
        " is taken by the runtime of compiled programs (use #mbt(\"name\"))",
      )
    }
    // an implicit value used at run time is a parameter of the MoonBit
    // function: of a MoonBit type
    match self.native_sig(f) {
      Some(sig) => {
        let mut t = @tt.globals.get(f).unwrap().ty
        for i = 0; i < sig.params.length(); i = i + 1 {
          guard t is Pi(x, icit, _, _, rest) else { break }
          match sig.params[i] {
            Some(nt) if icit == Impl && !mbt_only(nt) =>
              raise CodegenError(
                "#mbt fn " +
                f +
                ": the implicit parameter " +
                x +
                " is used at run time, so it is a parameter of the MoonBit function, but its type has no MoonBit type",
              )
            _ => ()
          }
          t = rest
        }
      }
      None => ()
    }
    if self.typed_set.contains(f) {
      continue
    }
    let why = match self.native_sig(f) {
      None =>
        "its signature has no native translation (a type parameter with a bound must occur in a parameter or in the result type)"
      Some(_) => {
        self.diagnose = true
        self.culprit = None
        ignore(self.typed_fn(f))
        self.diagnose = false
        match self.culprit {
          Some(c) => "its body is not in the native fragment: " + c
          None => "its body is not in the native fragment"
        }
      }
    }
    raise CodegenError(
      "#mbt fn " + f + " cannot be compiled to MoonBit: " + why,
    )
  }
}

///|
/// Strip the counter of a generated local name: `x_12` -> `x`.
fn source_name(n : String) -> String {
  match n.rev_find("_") {
    Some(i) if i > 0 => n.unsafe_substring(start=0, end=i)
    _ => n
  }
}

///|
/// The functions and global `let`s of the program (not of the Prelude)
/// without a native version, with the reason (`moonpp build --verbose`).
pub fn native_report(
  imports : Array[(String, String)],
) -> Array[(String, String)] {
  let g = Gen::new(imports)
  g.dry = true
  g.compute_typed()
  let out : Array[(String, String)] = []
  // `main`: when it is uniform, so is all it calls whose arguments cannot be
  // converted (arrays)
  if !@tt.is_async_global("main") && !g.typed_const_any("main") {
    g.diagnose = true
    g.culprit = None
    ignore(g.typed_const_any("main"))
    g.diagnose = false
    out.push(
      (
        "main",
        "its body is not in the native fragment" +
        g.culprit.map(c => ": " + c).unwrap_or(""),
      ),
    )
  }
  let names : Array[String] = @tt.global_files.keys().collect()
  names.sort()
  for n in names {
    let e = match @tt.globals.get(n) {
      Some({ kind: GFunc(Some(_), _, _), .. } as e) => e
      _ => continue
    }
    // the program's own definitions, not trait methods
    let own = match @tt.global_files.get(n) {
      Some(f) => @tt.source_files.contains(f)
      None => false
    }
    let is_method = match n.rev_find("::") {
      Some(i) =>
        @tt.data_info(n.unsafe_substring(start=0, end=i))
        is Some({ is_trait: true, .. })
      None => false
    }
    if !own ||
      is_method ||
      n == "main" ||
      @tt.is_proof_global(n) ||
      n.contains("$") {
      continue
    }
    if func_arity(n) is Some(_) {
      if g.typed_set.contains(n) {
        continue
      }
      // a type-level function is not code
      if @tt.show_tm([], e.ty).has_suffix("-> Type") {
        continue
      }
      let why = match g.native_sig(n) {
        None => "its signature has no native translation: " + g.sig_reason(n)
        Some(_) => {
          g.diagnose = true
          g.culprit = None
          ignore(g.typed_fn(n))
          g.diagnose = false
          match g.culprit {
            Some(c) => "its body is not in the native fragment: " + c
            None => "its body is not in the native fragment"
          }
        }
      }
      out.push((n, why))
    } else if is_native_const_candidate(n, e) &&
      g.native_ty_in([], e.ty) is Some(_) &&
      !g.native_consts.contains(n) {
      let why = match g.typed_const(n) {
        Some(_) =>
          "it holds arrays, and code in the uniform representation uses it"
        None => {
          g.diagnose = true
          g.culprit = None
          ignore(g.typed_const_any(n))
          g.diagnose = false
          match g.culprit {
            Some(c) => "its definition is not in the native fragment: " + c
            None => "its definition is not in the native fragment"
          }
        }
      }
      out.push((n, why))
    }
  }
  out
}

///|
/// Why the term `t` is not in the native fragment.
fn Gen::explain(self : Gen, env : Array[TLocal], t : @tt.Tm) -> String {
  let names = env.map(l => {
    match l {
      TVar(n, _) | TMut(n, _) => source_name(n)
      TType(_) => "T"
      TNone => "_"
    }
  })
  let shown = @tt.show_tm(names, t)
  let shown = if shown.length() > 60 {
    shown.unsafe_substring(start=0, end=57) + "..."
  } else {
    shown
  }
  let (h, _) = flatten_app(t)
  let why = match h {
    Global(g) =>
      match @tt.globals.get(g) {
        Some({ kind: GFunc(_, _, _), .. }) =>
          match g.rev_find("::") {
            Some(i) if @tt.data_info(g.unsafe_substring(start=0, end=i))
              is Some({ is_trait: true, .. }) =>
              Some(
                g +
                " is a method of the trait " +
                g.unsafe_substring(start=0, end=i) +
                ", which is not #mbt",
              )
            _ if func_arity(g) is None =>
              if self.native_consts.contains(g) {
                None
              } else {
                Some("the global let " + g + " is not native")
              }
            _ =>
              if self.native_sig(g) is None {
                Some(
                  g +
                  " has no native signature (a type without a MoonBit type, or a bound that is not #mbt)",
                )
              } else if !self.typed_set.contains(g) {
                Some(g + " is not in the native fragment")
              } else {
                None
              }
          }
        Some({ kind: GPrim(p, _), .. }) if !p.has_prefix("@mbt:") =>
          Some("the primitive " + g + " has no native translation")
        Some({ kind: GCon(ci), .. }) if !self.enum_ok(ci.data) =>
          Some("the type " + ci.data + " is not native")
        _ => None
      }
    _ => None
  }
  match why {
    Some(w) => "in `" + shown + "`, " + w
    None => "`" + shown + "`"
  }
}

///|
let mbt_keywords : Array[String] = [
  "as", "break", "catch", "const", "continue", "else", "enum", "extern", "false",
  "fn", "for", "guard", "if", "impl", "in", "is", "let", "loop", "match", "mut",
  "pub", "priv", "raise", "return", "struct", "test", "trait", "true", "try", "type",
  "typealias", "while", "with", "async", "defer", "readonly", "local",
]

///|
/// Does the codomain of a function type of `n` parameters raise?
fn result_raises(ty : @tt.Tm, n : Int32) -> Bool {
  let mut t = ty
  for _ in 0..<n {
    match t {
      Pi(_, _, _, _, b) => t = b
      _ => return false
    }
  }
  t is Raises(_, e) && @tt.tm_effect(e).1 is Some(_)
}

///|
/// Emit the public MoonBit function of a `#mbt` function (a no-op for
/// other functions).
fn Gen::export_fn(self : Gen, name : String, sig : TSig) -> Unit {
  let mname = match @tt.mbt_fns.get(name) {
    Some(m) => m
    None => return
  }
  let g = @tt.globals.get(name).unwrap()
  let body = match g.kind {
    GFunc(Some(b), _, _) => b
    _ => return
  }
  let labels = @tt.param_labels(name).unwrap_or([])
  let n = sig.params.length()
  // source names of the parameters
  let srcs : Array[String] = []
  let mut b = body
  for _ in 0..<n {
    match b {
      Lam(x, _, _, rest) => {
        srcs.push(x)
        b = rest
      }
      _ => srcs.push("_")
    }
  }
  // which parameters are explicit (labels are those of explicit ones)
  let icits : Array[@tt.Icit] = []
  let mut t = g.ty
  for _ in 0..<n {
    match t {
      Pi(_, i, _, _, rest) => {
        icits.push(i)
        t = rest
      }
      _ => icits.push(Expl)
    }
  }
  let decls : Array[String] = []
  let args : Array[String] = []
  let used : Array[String] = []
  let mut expl = 0
  let expl_total = sig.params
    .mapi((i, p) => p is Some(_) && icits[i] == Expl)
    .filter(b => b)
    .length()
  let implicit_values : Array[String] = []
  for i = 0; i < n; i = i + 1 {
    guard sig.params[i] is Some(nt) else { continue }
    let is_expl = icits[i] == Expl
    let label = if is_expl && expl < labels.length() {
      labels[expl]
    } else {
      None
    }
    if is_expl {
      expl = expl + 1
    } else {
      implicit_values.push(srcs[i])
    }
    // `fn f()` takes a `Unit` in MoonBit++
    if nt == NUnit && is_expl && expl_total == 1 && label is None {
      args.push("()")
      continue
    }
    let x = match label {
      Some((l, _)) => l
      None => {
        let s = srcs[i]
        if is_ident(s) &&
          !mbt_keywords.contains(s) &&
          !used.contains(s) &&
          s != "_" {
          s
        } else {
          "a" + i.to_string()
        }
      }
    }
    used.push(x)
    args.push(x)
    decls.push(
      match label {
        Some((_, false)) => x + "~ : " + self.mbt_ty(nt)
        Some((_, true)) =>
          match nt {
            // `x? : T`: MoonBit++ sees an `Option[T]`, as MoonBit does
            NEnum(_, [inner]) => x + "? : " + self.mbt_ty(inner)
            _ => x + " : " + self.mbt_ty(nt)
          }
        None => x + " : " + self.mbt_ty(nt)
      },
    )
  }
  // the MoonBit function has parameters that MoonBit++ callers do not write
  if implicit_values.length() > 0 {
    warnings.push(
      "#mbt fn " +
      name +
      ": the implicit parameter(s) " +
      implicit_values.join(", ") +
      " are used at run time, so the MoonBit function " +
      mname +
      " takes them as ordinary parameters: " +
      mname +
      "(" +
      decls.join(", ") +
      ")",
    )
  }
  let raises = result_raises(g.ty, n)
  let gen = if sig.ntvars == 0 {
    ""
  } else {
    "[" + self.tvars_with_bounds(sig.ntvars, sig.bounds) + "]"
  }
  let call = self.gid(name) + "_t(" + args.join(", ") + ")"
  let body_code = if raises || !self.fn_raises(name) {
    call
  } else {
    // control flow and failures are errors of the native code
    "try {\n" +
    call +
    "\n} catch {\nCAbort(m) => abort(m)\ne => abort(e.to_string())\n}"
  }
  self.write_to(
    self.file_of(name),
    "\n///|\n/// MoonBit++ " +
    name +
    "\npub " +
    (if @tt.is_async_global(name) { "async fn" } else { "fn" }) +
    gen +
    " " +
    mname +
    "(" +
    decls.join(", ") +
    ") -> " +
    self.mbt_result(sig.result) +
    (if raises { " raise" } else { "" }) +
    " {\n" +
    body_code +
    "\n}\n",
  )
}

///|
/// Async functions must be native, like `#mbt` functions: the uniform
/// representation is synchronous.
fn Gen::check_async_fns(self : Gen) -> Unit raise CodegenError {
  for f, g in @tt.globals {
    if f == "main" ||
      !(g.kind is GFunc(Some(_), _, _)) ||
      !@tt.is_async_global(f) ||
      self.typed_set.contains(f) {
      continue
    }
    raise CodegenError(
      "async fn " +
      f +
      " cannot be compiled to MoonBit: " +
      self.why_not_native(f),
    )
  }
}

///|
/// Why function `f` has no native translation.
fn Gen::why_not_native(self : Gen, f : String) -> String {
  match self.native_sig(f) {
    None =>
      "its type has no native MoonBit translation (like a type computed from a parameter, or a type parameter with a bound that occurs in no parameter and not in the result type)"
    Some(_) => {
      self.diagnose = true
      self.culprit = None
      ignore(self.typed_fn(f))
      self.diagnose = false
      match self.culprit {
        Some(c) => "its body is not in the native fragment: " + c
        None => "its body is not in the native fragment"
      }
    }
  }
}

///|
/// A use of the async function `f` in uniform code: an error, reported
/// after the generation.
fn Gen::async_use(self : Gen, f : String) -> String {
  self.async_misuse.push((f, self.cur_global))
  "abort(\"async function used outside of native code\")"
}

///|
/// `async fn main`: its body must be native.
fn Gen::async_main(self : Gen) -> String raise CodegenError {
  let body = match @tt.globals.get("main") {
    Some({ kind: GFunc(Some(b), _, _), .. }) => b
    _ => raise CodegenError("main has no definition")
  }
  self.cur_global = "main"
  self.cur_result = Some(NUnit)
  let res = Ok(self.typed([], body)) catch { err => Err(err) }
  self.cur_result = None
  match res {
    Ok((code, _)) =>
      "\n///|\nasync fn main {\n  (try {\n    ignore(" +
      code +
      ")\n  } catch {\n    e => report_error(e)\n  })\n  rt_flush()\n}\n"
    Err(_) => {
      self.diagnose = true
      self.culprit = None
      ignore(Ok(self.typed([], body)) catch { err => Err(err) })
      self.diagnose = false
      raise CodegenError(
        "async fn main cannot be compiled to MoonBit: its body is not in the native fragment" +
        (match self.culprit {
          Some(c) => ": " + c
          None => ""
        }),
      )
    }
  }
}

///|
/// Warnings of the last generation (e.g. a `#mbt` function whose MoonBit
/// signature has parameters that are implicit in MoonBit++).
pub let warnings : Array[String] = []
