///|
/// Calls of imported MoonBit functions. From the MoonBit++ type of an
/// imported function (which mirrors its MoonBit signature) we generate a
/// wrapper converting the arguments from `Value` and the result back.
///
/// Supported types: `Int`, `Double`, `Bool`, `Char`, `String`, `Unit`,
/// type variables (instantiated with `Value`), `Array[T]`, `Option[T]`,
/// `#mbt` datatypes (e.g. imported `pub(all)` enums and structs, converted
/// constructor by constructor), function types (as arguments), and opaque
/// MoonBit types whose type arguments are type variables (boxed in the
/// generated `Foreign` enum). Calling a function with another signature is
/// a compile error.
priv enum Binder {
  TyVar
  Explicit
}

///|
fn lookup(stack : Array[Binder], ix : Int32) -> Binder? {
  let i = stack.length() - 1 - ix
  if i >= 0 && i < stack.length() {
    Some(stack[i])
  } else {
    None
  }
}

///|
fn flatten(t : @tt.Tm) -> (@tt.Tm, Array[@tt.Tm]) {
  let args : Array[@tt.Tm] = []
  let mut h = t
  while h is App(f, a, _) {
    args.push(a)
    h = f
  }
  args.rev_in_place()
  (h, args)
}

///|
let scalar_types : Array[(String, String, String)] = [
  ("Int", "as_int", "VInt"),
  ("Double", "as_double", "VDouble"),
  ("Int64", "as_int64", "VInt64"),
  ("UInt", "as_uint", "VUInt"),
  ("UInt64", "as_uint64", "VUInt64"),
  ("Byte", "as_byte", "VByte"),
  ("Float", "as_float", "VFloat"),
  ("Bool", "as_bool", "VBool"),
  ("Char", "as_char", "VChar"),
  ("String", "as_str", "VStr"),
  ("BigInt", "as_nat", "VNat"),
]

///|
/// Is `t` a type variable of the signature?
fn is_tyvar(stack : Array[Binder], t : @tt.Tm) -> Bool {
  match t {
    Var(ix) => lookup(stack, ix) is Some(TyVar)
    _ => false
  }
}

///|
/// A `#mbt` datatype of a signature, as a native type (its type variables
/// are `Value`s, so they need no conversion).
fn Gen::ffi_mbt_type(self : Gen, stack : Array[Binder], t : @tt.Tm) -> NTy? {
  let ctx = stack.map(b => {
    match b {
      TyVar => TyIs(NVar(0))
      Explicit => TyOther
    }
  })
  match self.native_ty_in(ctx, t) {
    Some(NEnum(d, _) as nt) if is_mbt_type(d) && mbt_only(nt) => Some(nt)
    _ => None
  }
}

///|
/// A foreign (opaque) MoonBit type, as the MoonBit type of its boxed values.
fn Gen::foreign_type(self : Gen, stack : Array[Binder], t : @tt.Tm) -> String? {
  let (h, args) = flatten(t)
  match h {
    Global(n) =>
      match @tt.data_info(n) {
        Some(di) if di.builtin &&
          ![
            "Int", "Double", "Bool", "Char", "String", "Unit", "Array", "Error",
            "Int64", "UInt", "UInt64", "Byte", "Float", "BigInt",
          ].contains(n) &&
          args.iter().all(a => is_tyvar(stack, a)) => {
          let ty = if args.length() == 0 {
            n
          } else {
            n + "[" + args.map(_ => "Value").join(", ") + "]"
          }
          if !self.foreign.contains(ty) {
            self.foreign.set(ty, "F" + self.foreign.length().to_string())
            self.foreign_order.push(ty)
          }
          Some(self.foreign.get(ty).unwrap())
        }
        _ => None
      }
    _ => None
  }
}

///|
/// Code converting `e : Value` to the MoonBit type of `t`.
fn Gen::to_mbt(
  self : Gen,
  stack : Array[Binder],
  t : @tt.Tm,
  e : String,
) -> String? {
  if is_tyvar(stack, t) {
    return Some(e)
  }
  match t {
    Global("Unit") => return Some("as_unit(" + e + ")")
    // views: MoonBit++ uses the containers themselves
    Global("StringView") => return Some("as_str(" + e + ")[:]")
    // a trait object: a MoonBit wrapper calling the packed instance
    Global(d) if d.has_prefix("&") =>
      return match
        self.dyn_wrapper(d.unsafe_substring(start=1, end=d.length())) {
        Some((w, mt)) => Some("(" + w + "::{ v: " + e + " } : &" + mt + ")")
        None => None
      }
    Global(n) =>
      for s in scalar_types {
        if s.0 == n {
          return Some(s.1 + "(" + e + ")")
        }
      }
    _ => ()
  }
  match flatten(t) {
    (Global("ArrayView"), [a]) =>
      match self.to_mbt(stack, App(Global("Array"), a, Impl), e) {
        Some(c) => return Some(c + "[:]")
        None => return None
      }
    (Global("Array"), [a]) =>
      if is_tyvar(stack, a) {
        return Some("as_arr(" + e + ")")
      } else {
        let x = self.name("y")
        match self.to_mbt(stack, a, x) {
          Some(c) =>
            return Some("as_arr(" + e + ").map(" + x + " => " + c + ")")
          None => return None
        }
      }
    (Global("Option"), [a]) => {
      let x = self.name("y")
      match self.to_mbt(stack, a, x) {
        Some(c) =>
          return Some(
            "(match " +
            e +
            " { " +
            self.con_code("Option::Some", [x]) +
            " => Some(" +
            c +
            "); _ => None })",
          )
        None => return None
      }
    }
    _ => ()
  }
  match self.ffi_mbt_type(stack, t) {
    Some(nt) if self.convertible(nt, true) =>
      return Some(self.of_value(nt, e, None))
    Some(_) => return None
    None => ()
  }
  match self.foreign_type(stack, t) {
    Some(f) =>
      return Some(
        "(match " +
        e +
        " { VForeign(" +
        f +
        "(x)) => x; _ => rt_fail(\"unexpected foreign value\") })",
      )
    None => ()
  }
  // a function argument: a MoonBit closure calling the MoonBit++ function
  match t {
    Pi(_, Expl, _, _, _) => {
      let params : Array[String] = []
      let mut call = e
      let mut cur = t
      let mut st = stack
      let mut first = true
      while cur is Pi(_, Expl, g, dom, cod) && (first || !g) {
        first = false
        let x = self.name("p")
        let arg = if dom is Global("Unit") &&
          !(cod is Pi(_, Expl, false, _, _)) &&
          params.length() == 0 {
          "VUnit"
        } else {
          params.push(x)
          match self.from_mbt(st, dom, x) {
            Some(c) => c
            None => return None
          }
        }
        call = "apply(" + call + ", " + arg + ")"
        st = [..st, Explicit]
        cur = cod
      }
      let res = match self.to_mbt(st, cur, call) {
        Some(c) => c
        None => return None
      }
      Some(
        "(fn(" +
        params.join(", ") +
        ") { try { " +
        res +
        " } catch { err => abort(\"error in a callback: \" + err.to_string()) } })",
      )
    }
    _ => None
  }
}

///|
/// Code converting `e` of the MoonBit type of `t` to a `Value`.
fn Gen::from_mbt(
  self : Gen,
  stack : Array[Binder],
  t : @tt.Tm,
  e : String,
) -> String? {
  if is_tyvar(stack, t) {
    return Some(e)
  }
  match t {
    Global("Unit") => return Some("{ ignore(" + e + "); VUnit }")
    Global("StringView") => return Some("VStr(" + e + ".to_string())")
    Global(n) =>
      for s in scalar_types {
        if s.0 == n {
          return Some(s.2 + "(" + e + ")")
        }
      }
    _ => ()
  }
  match flatten(t) {
    (Global("ArrayView"), [a]) =>
      return self.from_mbt(
        stack,
        App(Global("Array"), a, Impl),
        e + ".to_array()",
      )
    (Global("Array"), [a]) =>
      if is_tyvar(stack, a) {
        return Some("VArr(" + e + ")")
      } else {
        let x = self.name("y")
        match self.from_mbt(stack, a, x) {
          Some(c) => return Some("VArr(" + e + ".map(" + x + " => " + c + "))")
          None => return None
        }
      }
    (Global("Option"), [a]) => {
      let x = self.name("y")
      match self.from_mbt(stack, a, x) {
        Some(c) =>
          return Some(
            "(match " +
            e +
            " { Some(" +
            x +
            ") => " +
            self.con_code("Option::Some", [c]) +
            "; None => " +
            self.con_code("Option::None", []) +
            " })",
          )
        None => return None
      }
    }
    _ => ()
  }
  match self.ffi_mbt_type(stack, t) {
    Some(nt) if self.convertible(nt, false) =>
      return Some(self.to_value(nt, e, None))
    Some(_) => return None
    None => ()
  }
  match self.foreign_type(stack, t) {
    Some(f) => Some("VForeign(" + f + "(" + e + "))")
    None => None
  }
}

///|
/// Why a parameter (or the result) of an imported function cannot be
/// converted.
fn Gen::ffi_problem(
  self : Gen,
  stack : Array[Binder],
  t : @tt.Tm,
  what : String,
) -> String {
  match self.ffi_mbt_type(stack, t) {
    Some(nt) if what == "parameter" && !self.convertible(nt, true) =>
      "its " +
      what +
      " has a read-only MoonBit type (not pub(all)), whose values cannot be rebuilt from compiled MoonBit++ values; call it from a function in the native fragment"
    _ =>
      "its " +
      what +
      " type is not supported (mark the datatypes it uses #mbt, if they translate to MoonBit)"
  }
}

///|
/// Traits that `Value` implements, so generic MoonBit functions with these
/// bounds can be called.
let value_traits : Array[String] = ["Show", "Eq", "Compare", "Hash"]

///|
/// The MoonBit code calling an imported function, or an explanation of why
/// it is not supported.
fn Gen::ffi_body(
  self : Gen,
  name : String,
  prim : String,
  ty : @tt.Tm,
  arity : Int32,
) -> Result[String, String] {
  let target = prim.unsafe_substring(start=5, end=prim.length())
  let stack : Array[Binder] = []
  let conv : Array[String] = []
  let lets = StringBuilder()
  let mut t = ty
  let mut k = 0
  let labels = @tt.param_labels(name).unwrap_or([])
  let mut expl = 0
  while k < arity {
    match t {
      Pi(_, Impl, _, _, b) => {
        stack.push(TyVar)
        t = b
      }
      Pi(_, Inst, _, dom, b) => {
        match flatten(dom) {
          (Global(tr), _) if value_traits.contains(tr) => ()
          (Global(tr), _) =>
            return Err(
              "the bound " + tr + " cannot be satisfied by compiled values",
            )
          _ => return Err("unsupported bound")
        }
        stack.push(Explicit)
        t = b
      }
      Pi(_, Expl, _, dom, b) => {
        let x = "x" + k.to_string()
        let unit_only = dom is Global("Unit") &&
          arity - k == 1 &&
          labels.length() <= 1
        if !unit_only {
          match self.to_mbt(stack, dom, "args[" + k.to_string() + "]") {
            Some(c) => lets.write_string("  let " + x + " = " + c + "\n")
            None => return Err(self.ffi_problem(stack, dom, "parameter"))
          }
          let label = if expl < labels.length() { labels[expl] } else { None }
          conv.push(
            match label {
              Some((l, false)) => l + "=" + x
              Some((l, true)) => l + "?=" + x
              None => x
            },
          )
        }
        expl = expl + 1
        stack.push(Explicit)
        t = b
      }
      _ => return Err("bad type")
    }
    k = k + 1
  }
  let (res_ty, raises) = match t {
    Raises(r, _) => (r, true)
    _ => (t, false)
  }
  let call = match self.ffi_call(target, conv) {
    Ok(c) => c
    Err(e) => return Err(e)
  }
  let call = if raises {
    "try { " + call + " } catch { err => raise CRaise(foreign_error(err)) }"
  } else {
    call
  }
  match self.from_mbt(stack, res_ty, "r") {
    Some(back) => Ok(lets.to_string() + "  let r = " + call + "\n  " + back)
    None => Err(self.ffi_problem(stack, res_ty, "result"))
  }
}

///|
/// The MoonBit call of an imported function (`target` is the part of its
/// primitive name after `@mbt:`) with the given (converted, labelled)
/// arguments.
fn Gen::ffi_call(
  self : Gen,
  target : String,
  conv : Array[String],
) -> Result[String, String] {
  let call = if target.has_prefix("trait:") {
    // a method of an imported impl: MoonBit finds the impl
    target.unsafe_substring(start=6, end=target.length()) +
    "(" +
    conv.join(", ") +
    ")"
  } else if target.has_prefix("@") || !target.contains(".") {
    // `impl Show for T`: a method of the type
    match target.find("::") {
      Some(i) if conv.length() > 0 => {
        let m = target.unsafe_substring(start=i + 2, end=target.length())
        conv[0] + "." + m + "(" + conv[1:].to_array().join(", ") + ")"
      }
      _ => return Err("unsupported method")
    }
  } else {
    let dot = target.rev_find(".").unwrap()
    let path = target.unsafe_substring(start=0, end=dot)
    let fname = target.unsafe_substring(start=dot + 1, end=target.length())
    let pkg_alias = match self.aliases.get(path) {
      Some(a) => a
      None => return Err("package " + path + " is not imported")
    }
    match fname.find("::") {
      Some(i) => {
        let tname = fname.unsafe_substring(start=0, end=i)
        let m = fname.unsafe_substring(start=i + 2, end=fname.length())
        if @tt.globals.contains("@" + pkg_alias + "." + tname) {
          "@" + pkg_alias + "." + fname + "(" + conv.join(", ") + ")"
        } else if conv.length() > 0 {
          // a method of a type of another package (e.g. `Array`)
          conv[0] + "." + m + "(" + conv[1:].to_array().join(", ") + ")"
        } else {
          return Err("unsupported method")
        }
      }
      None => "@" + pkg_alias + "." + fname + "(" + conv.join(", ") + ")"
    }
  }
  Ok(call)
}

///|
/// Emit the wrapper of an imported function; returns its name.
fn Gen::ffi_fn(
  self : Gen,
  name : String,
  prim : String,
  ty : @tt.Tm,
  arity : Int32,
) -> String raise CodegenError {
  let f = self.name("ffi")
  let body = match self.ffi_body(name, prim, ty, arity) {
    Ok(b) => b
    Err(why) =>
      raise CodegenError(
        "cannot call the MoonBit function " +
        name +
        " from compiled code: " +
        why,
      )
  }
  self.write_to(
    imports_file,
    "\n/// " +
    name +
    "\nfn " +
    f +
    "(args : Array[Value]) -> Value raise {\n" +
    body +
    "\n}\n",
  )
  f
}

///|
/// The MoonBit trait of the MoonBit++ trait `tr`, if it is one.
fn mbt_trait_of(tr : String) -> String? {
  match @tt.mbt_info(tr) {
    Some(info) if @tt.data_info(tr) is Some({ is_trait: true, .. }) =>
      Some(info.name)
    _ => None
  }
}

///|
/// The MoonBit struct wrapping a MoonBit++ `&tr` value, with impls of the
/// MoonBit trait (and its supertraits) that call the packed instance; its
/// name and the MoonBit trait. `None` if `tr` is not a MoonBit trait or a
/// method's types do not convert.
fn Gen::dyn_wrapper(self : Gen, tr : String) -> (String, String)? {
  let mt = match mbt_trait_of(tr) {
    Some(m) => m
    None => return None
  }
  match self.dyn_wrappers.get(tr) {
    Some(w) => return Some((w, mt))
    None => ()
  }
  let w = "DynW" + self.dyn_wrappers.length().to_string()
  self.dyn_wrappers.set(tr, w)
  let code = StringBuilder()
  code.write_string(
    "\n/// &" + tr + " passed to MoonBit\nstruct " + w + " {\n  v : Value\n}\n",
  )
  let d = "&" + tr
  // the trait and its supertraits
  let todo = [tr]
  let seen : Array[String] = []
  while todo.pop() is Some(t) {
    if seen.contains(t) {
      continue
    }
    seen.push(t)
    for s in @tt.trait_supers(t) {
      todo.push(s)
    }
    let tm = match mbt_trait_of(t) {
      Some(m) => m
      None => return None
    }
    let key = "impl$" + t + "$" + d
    for m in @tt.trait_method_names(t) {
      // the method's type in the context [Self, inst], after `self`
      let mut ty = match @tt.trait_method_type(t, m) {
        Some(Pi(_, _, _, _, rest)) => rest
        _ => return None
      }
      let stack : Array[Binder] = [Explicit, Explicit, Explicit]
      let names : Array[String] = []
      let vals : Array[String] = []
      while ty is Pi(_, Expl, _, a, b) {
        let x = "a" + names.length().to_string()
        match self.from_mbt(stack, a, x) {
          Some(c) => vals.push(c)
          None => return None
        }
        names.push(x)
        stack.push(Explicit)
        ty = b
      }
      let ret = match ty {
        Raises(r, _) => r
        _ => ty
      }
      // the MoonBit++ method, applied to the packed value and the arguments
      let mut call = @tt.App(
        @tt.App(
          @tt.App(@tt.Global(t + "::" + m), @tt.Global(d), @tt.Impl),
          @tt.Global(key),
          @tt.Inst,
        ),
        @tt.Var(names.length()),
        @tt.Expl,
      )
      for i = 0; i < names.length(); i = i + 1 {
        call = @tt.App(call, @tt.Var(names.length() - 1 - i), @tt.Expl)
      }
      let env : Array[Local] = [LVar("self.v")]
      let env = vals.fold(init=env, (e, v) => push_local(e, LVar(v)))
      let back = match self.to_mbt(stack, ret, self.tm(env, call)) {
        Some(c) => c
        None => return None
      }
      let mname = @tt.mbt_method_name(t, m)
      let body = "try {\n" +
        back +
        "\n} catch {\n_ => abort(" +
        ("error in " + t + "::" + m).escape() +
        ")\n}"
      if t == "Hash" {
        code.write_string(
          "\nimpl " +
          tm +
          " for " +
          w +
          " with hash_combine(self, hasher) {\nhasher.combine_int(" +
          body +
          ")\n}\n",
        )
      } else {
        code.write_string(
          "\nimpl " +
          tm +
          " for " +
          w +
          " with " +
          mname +
          "(" +
          ["self", ..names].join(", ") +
          ") {\n" +
          body +
          "\n}\n",
        )
      }
    }
  }
  self.write_to(imports_file, code.to_string())
  Some((w, mt))
}
