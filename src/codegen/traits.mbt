///|
/// `#mbt` types and traits in the native translation.
///
/// A `#mbt` datatype is the MoonBit type of its name: generated (with the
/// same name, constructors and fields) when the program defines it, used as
/// it is when it is an existing MoonBit type (`#mbt("Option")`, imported
/// `@pkg.T`). In the uniform representation its values are constructor variants of `Value` as for
/// any datatype, converted at the boundary.
///
/// A `#mbt` trait is a MoonBit trait: a bound `[T : Tr]` of a native
/// function is a MoonBit bound (the instance argument disappears), a method
/// call is `Tr::m(...)`, and an `impl` whose methods are in the typed
/// fragment becomes a MoonBit `impl` (emitted when a native call needs it).
/// A native call needing an instance that is not a MoonBit `impl` falls
/// back to the uniform translation, where instances are values.
fn is_mbt_type(d : String) -> Bool {
  @tt.mbt_info(d) is Some(_) && !is_mbt_trait(d)
}

///|
fn is_mbt_trait(tr : String) -> Bool {
  @tt.mbt_info(tr) is Some(_) &&
  @tt.data_info(tr) is Some({ is_trait: true, .. })
}

///|
fn is_mbt_struct(d : String) -> Bool {
  is_mbt_type(d) && @tt.data_info(d) is Some({ fields: Some(_), .. })
}

///|
fn struct_fields(d : String) -> Array[String] {
  @tt.data_info(d).unwrap().fields.unwrap()
}

///|
/// The MoonBit name of a native datatype.
fn data_name(d : String) -> String {
  match @tt.mbt_info(d) {
    Some(info) => info.name
    None => enum_name(d)
  }
}

///|
/// The field type of a datatype that is a newtype after erasure: one
/// constructor keeping one field (not of the datatype itself). It is a
/// MoonBit tuple struct `struct E_D(T)` rather than an enum (no box).
fn Gen::newtype_field(self : Gen, d : String) -> NTy? {
  if is_mbt_type(d) || !self.enum_ok(d) {
    return None
  }
  match @tt.data_info(d).unwrap().cons {
    [c] =>
      match self.con_fields(c) {
        Some(fs) =>
          match fs.filter(f => f is Some(_)) {
            [Some(t)] if !nty_mentions(t, d) => Some(t)
            _ => None
          }
        None => None
      }
    _ => None
  }
}

///|
fn nty_mentions(t : NTy, d : String) -> Bool {
  match t {
    NEnum(e, args) => e == d || args.iter().any(a => nty_mentions(a, d))
    NForeign(_, args) => args.iter().any(a => nty_mentions(a, d))
    NFun(ps, r) | NAsyncFun(ps, r) =>
      ps.iter().any(a => nty_mentions(a, d)) || nty_mentions(r, d)
    _ => false
  }
}

///|
/// A value of datatype `d` built with constructor `c` from its (kept)
/// fields.
fn Gen::con_expr(
  self : Gen,
  d : String,
  c : String,
  args : Array[String],
) -> String {
  if self.newtype_field(d) is Some(_) {
    return data_name(d) + "(" + args[0] + ")"
  }
  if is_mbt_struct(d) {
    let fs = struct_fields(d)
    data_name(d) +
    "::{ " +
    args.mapi((k, a) => fs[k] + ": " + a).join(", ") +
    " }"
  } else {
    let cn = if is_mbt_type(d) { short_con(c) } else { native_con(c) }
    data_name(d) +
    "::" +
    cn +
    (if args.length() == 0 { "" } else { "(" + args.join(", ") + ")" })
  }
}

///|
/// A pattern for constructor `c` of datatype `d` with sub-patterns for its
/// (kept) fields.
fn Gen::con_pat(
  self : Gen,
  d : String,
  c : String,
  subs : Array[String],
) -> String {
  if is_mbt_struct(d) {
    let fs = struct_fields(d)
    "{ " + [..subs.mapi((k, p) => fs[k] + ": " + p), ".."].join(", ") + " }"
  } else {
    self.con_expr(d, c, subs)
  }
}

///|
/// Are all datatypes of `t` MoonBit types?
fn mbt_only(t : NTy) -> Bool {
  match t {
    NEnum(d, args) => is_mbt_type(d) && args.iter().all(mbt_only)
    NForeign(_, args) => args.iter().all(mbt_only)
    NFun(ps, r) | NAsyncFun(ps, r) => ps.iter().all(mbt_only) && mbt_only(r)
    NNat("BigInt") => true
    // a `BigInt` from MoonBit could be negative
    NNat(_) => false
    _ => true
  }
}

///|
/// A `#mbt` bound `Tr(T)` of a type parameter: (its index, the trait).
fn bound_of(ctx : Array[TyCtx], a : @tt.Tm) -> (Int32, String)? {
  match a {
    App(Global(tr), Var(ix), _) if is_mbt_trait(tr) => {
      let i = ctx.length() - 1 - ix
      if i >= 0 && ctx[i] is TyIs(NVar(k)) {
        Some((k, tr))
      } else {
        None
      }
    }
    _ => None
  }
}

///|
/// `Tr::m` for a method `m` of a `#mbt` trait `Tr`.
fn method_of(n : String) -> (String, String)? {
  match n.rev_find("::") {
    Some(i) => {
      let tr = n.unsafe_substring(start=0, end=i)
      let m = n.unsafe_substring(start=i + 2, end=n.length())
      if is_mbt_trait(tr) && @tt.trait_method_names(tr).contains(m) {
        Some((tr, m))
      } else {
        None
      }
    }
    None => None
  }
}

///|
/// Does `a` have `b` among its (transitive) supertraits, or is it `b`?
fn trait_implies(a : String, b : String) -> Bool {
  a == b || @tt.trait_supers(a).iter().any(s => trait_implies(s, b))
}

///|
/// The native type of method `m` of trait `tr` at type `self_t`.
fn Gen::method_nty(self : Gen, tr : String, m : String, self_t : NTy) -> NTy? {
  match @tt.trait_method_type(tr, m) {
    Some(fty) => self.native_ty_in([TyIs(self_t), TyOther], fty)
    None => None
  }
}

///|
/// Does the method's MoonBit++ type say that it raises?
fn method_raises(tr : String, m : String) -> Bool {
  let mut t = match @tt.trait_method_type(tr, m) {
    Some(t) => t
    None => return false
  }
  while t is Pi(_, _, _, _, b) {
    t = b
  }
  t is Raises(_, _)
}

///|
/// Whether the MoonBit methods of `tr` raise: those of generated traits
/// always do (compiled code raises its control flow), those of existing
/// traits when MoonBit++ says so.
fn mbt_method_raises(tr : String, m : String) -> Bool {
  match @tt.mbt_info(tr) {
    Some(info) => info.defined || method_raises(tr, m)
    None => false
  }
}

///|
/// The MoonBit name of a `#mbt` trait (declaring it if it is generated).
fn Gen::trait_name(self : Gen, tr : String) -> String {
  let info = @tt.mbt_info(tr).unwrap()
  if info.defined {
    self.need_trait(tr)
  }
  info.name
}

///|
/// Declare a generated MoonBit trait (once).
fn Gen::need_trait(self : Gen, tr : String) -> Unit {
  if self.dry || self.traits_done.contains(tr) {
    return
  }
  self.traits_done.push(tr)
  let supers = @tt.trait_supers(tr).map(s => self.trait_name(s))
  let buf = StringBuilder()
  buf.write_string(
    "\n/// MoonBit++ trait " +
    tr +
    "\npub(open) trait " +
    @tt.mbt_info(tr).unwrap().name +
    (if supers.length() == 0 { "" } else { " : " + supers.join(" + ") }) +
    " {\n",
  )
  for m in @tt.trait_method_names(tr) {
    match self.method_nty(tr, m, NSelf) {
      Some(NFun(ps, r)) => {
        let params = if ps == [NUnit] {
          ""
        } else {
          ps.map(p => self.mbt_ty(p)).join(", ")
        }
        buf.write_string(
          "  " + m + "(" + params + ") -> " + self.mbt_result(r) + " raise\n",
        )
      }
      _ => ()
    }
  }
  buf.write_string("}\n")
  self.write_to(self.file_of(tr), buf.to_string())
}

///|
/// `[T0 : A + B, T1]`: type parameters with their bounds.
fn Gen::tvars_with_bounds(
  self : Gen,
  n : Int32,
  bounds : Array[(Int32, String)],
) -> String {
  let tvs : Array[String] = []
  for k = 0; k < n; k = k + 1 {
    let trs = bounds.filter(b => b.0 == k).map(b => self.trait_name(b.1))
    tvs.push(
      if trs.length() == 0 {
        tvar(k)
      } else {
        tvar(k) + " : " + trs.join(" + ")
      },
    )
  }
  tvs.join(", ")
}

///|
/// Match the type `pat` (with the type parameters of an impl) against `t`.
fn match_nty(pat : NTy, t : NTy, sub : Array[NTy?]) -> Bool {
  match (pat, t) {
    (NVar(k), _) =>
      match sub[k] {
        Some(u) => u == t
        None => {
          sub[k] = Some(t)
          true
        }
      }
    (NEnum(d, xs), NEnum(e, ys)) | (NForeign(d, xs), NForeign(e, ys)) =>
      d == e &&
      xs.length() == ys.length() &&
      xs.mapi((k, x) => match_nty(x, ys[k], sub)).iter().all(b => b)
    _ => pat == t
  }
}

///|
/// Can MoonBit find an instance of `tr` for `t`? Then the instance's impl
/// is emitted.
fn Gen::satisfies(self : Gen, t : NTy, tr : String) -> Bool {
  if builtin_instance(t, tr) {
    return true
  }
  match t {
    NVar(k) =>
      self.cur_bounds.iter().any(bd => bd.0 == k && trait_implies(bd.1, tr))
    NSelf | NAny => false
    // MoonBit's own impls for its `Option` and `Result`, which print and
    // compare as the Prelude's instances do (not `Hash`: its values differ)
    NEnum("Option", [a]) if tr is ("Show" | "Eq" | "Compare") =>
      self.satisfies(a, tr)
    NEnum("Result", [a, b]) if tr is ("Show" | "Eq") =>
      self.satisfies(a, tr) && self.satisfies(b, tr)
    NForeign("Array", [a]) if tr == "Show" => self.satisfies(a, tr)
    _ => {
      for i in @tt.instances_of(tr) {
        // imported impls exist in MoonBit already
        let external = @tt.external_instances.contains(i)
        if !external && !self.mbt_impls.contains(i) {
          continue
        }
        guard self.impl_info(i) is Some((ntv, bounds, pat, _)) else { continue }
        let sub : Array[NTy?] = Array::make(ntv, None)
        if !match_nty(pat, t, sub) {
          continue
        }
        let ok = bounds
          .iter()
          .all(bd => {
            match sub[bd.0] {
              Some(u) => self.satisfies(u, bd.1)
              None => false
            }
          })
        if ok {
          if !external {
            self.need_impl(i)
          }
          return true
        }
      }
      false
    }
  }
}

///|
/// Does MoonBit have an instance of the Prelude trait `tr` for its own type
/// `t`?
fn builtin_instance(t : NTy, tr : String) -> Bool {
  match (tr, t) {
    ("Show" | "Eq" | "Compare", NInt | NDouble | NString | NBool | NChar | NUnit
    ) => true
    (
      "Show"
      | "Eq"
      | "Compare"
      | "Hash"
      | "Default"
      | "Add"
      | "Sub"
      | "Mul"
      | "Div",
      NInt64
      | NUInt
      | NUInt64
      | NByte
      | NFloat,
    ) => true
    (
      "Mod"
      | "BitAnd"
      | "BitOr"
      | "BitXOr"
      | "Shl"
      | "Shr",
      NInt64
      | NUInt
      | NUInt64
      | NByte,
    ) => true
    ("Neg", NInt64 | NFloat) => true
    ("Add", NInt | NDouble | NString) => true
    // MoonBit's `BigInt` prints, compares and computes as `Nat` does (not as
    // other Nat-like types, like `Fin`, print)
    ("Show" | "Eq" | "Compare" | "Add" | "Mul", NNat("Nat")) => true
    (
      "Show"
      | "Eq"
      | "Compare"
      | "Hash"
      | "Default"
      | "Add"
      | "Sub"
      | "Mul"
      | "Div"
      | "Mod"
      | "Neg"
      | "BitAnd"
      | "BitOr"
      | "BitXOr"
      | "Shl"
      | "Shr",
      NNat("BigInt"),
    ) => true
    ("Sub" | "Mul" | "Div" | "Neg", NInt | NDouble) => true
    ("Mod", NInt) => true
    ("Default", NInt | NDouble | NString | NBool | NUnit) => true
    ("BitAnd" | "BitOr" | "BitXOr" | "Shl" | "Shr", NInt) => true
    ("Hash", NInt | NDouble | NString | NBool | NChar | NUnit) => true
    ("ToJson", NInt | NDouble | NString | NBool | NChar | NUnit) => true
    ("Show" | "Eq" | "ToJson", NForeign("Json", [])) => true
    (d, NInt | NDouble | NString | NBool | NChar | NUnit) if d.has_suffix(
        ".Debug",
      ) => true
    _ => false
  }
}

///|
/// MoonBit's orphan rule: an impl of an existing MoonBit trait (`#mbt("T")`
/// or a Prelude trait) is only possible for a type generated by the
/// program: a native enum of a MoonBit++ datatype (`E_List`), or a `#mbt`
/// type the program defines. Existing MoonBit types (`#mbt("Option")`,
/// imported `@pkg.T`) have their own impls.
fn impl_allowed(tr : String, self_t : NTy) -> Bool {
  match @tt.mbt_info(tr) {
    Some({ defined: true, .. }) => true
    _ =>
      match self_t {
        NEnum(d, _) =>
          match @tt.mbt_info(d) {
            Some({ defined: true, .. }) => true
            Some(_) => false
            None => !d.has_prefix("@")
          }
        _ => false
      }
  }
}

///|
/// An instance of a `#mbt` trait as a MoonBit impl: its number of type
/// parameters, bounds, `Self` type and trait.
fn Gen::impl_info(
  self : Gen,
  i : String,
) -> (Int32, Array[(Int32, String)], NTy, String)? {
  let mut t = match @tt.globals.get(i) {
    Some(g) => g.ty
    None => return None
  }
  let ctx : Array[TyCtx] = []
  let bounds : Array[(Int32, String)] = []
  let mut ntv = 0
  while t is Pi(_, icit, _, a, b) {
    match (icit, a) {
      (Impl, U) => {
        ctx.push(TyIs(NVar(ntv)))
        ntv = ntv + 1
      }
      (Inst, _) => {
        match bound_of(ctx, a) {
          Some(bd) => bounds.push(bd)
          None => return None
        }
        ctx.push(TyOther)
      }
      _ => return None
    }
    t = b
  }
  match t {
    App(Global(tr), s, _) =>
      match self.native_ty_in(ctx, s) {
        // not for a Nat-like type: its MoonBit type is `BigInt`, which has
        // its own impls (see `builtin_instance`)
        Some(NVar(_) | NNat(_)) | None => None
        Some(nt) => Some((ntv, bounds, nt, tr))
      }
    _ => None
  }
}

///|
/// The MoonBit impl of an instance of a `#mbt` trait, if its methods are in
/// the typed fragment.
fn Gen::impl_code(self : Gen, i : String) -> String? {
  let (ntv, bounds, self_t, tr) = match self.impl_info(i) {
    Some(x) => x
    None => return None
  }
  let (body, n) = match @tt.globals.get(i) {
    Some({ kind: GFunc(Some(b), _, n), .. }) => (b, n)
    _ => return None
  }
  // the binders: type parameters and instances
  let mut env : Array[TLocal] = []
  let mut b = body
  let mut k = 0
  for _ in 0..<n {
    match b {
      Lam(_, Impl, _, rest) => {
        env = tpush(env, TType(NVar(k)))
        k = k + 1
        b = rest
      }
      Lam(_, _, _, rest) => {
        env = tpush(env, TNone)
        b = rest
      }
      _ => return None
    }
  }
  let (h, args) = flatten_app(b)
  let fields = @tt.data_info(tr).unwrap().fields.unwrap()
  if !(h is Global(c) && c == tr + "::mk") ||
    args.length() != fields.length() + 1 {
    return None
  }
  let saved_bounds = self.cur_bounds
  let saved_result = self.cur_result
  self.cur_bounds = bounds
  let out = StringBuilder()
  let ok : Result[Unit, NotTyped] = try {
    // MoonBit needs the impls of the supertraits too
    for s in @tt.trait_supers(tr) {
      if !self.satisfies(self_t, s) {
        raise NotTyped
      }
    }
    let header = "impl" +
      (if ntv == 0 {
        ""
      } else {
        "[" + self.tvars_with_bounds(ntv, bounds) + "]"
      }) +
      " " +
      self.trait_name(tr) +
      " for " +
      self.mbt_ty(self_t) +
      " with "
    for j = 0; j < fields.length(); j = j + 1 {
      let m = fields[j]
      if m.has_prefix("super$") {
        continue
      }
      let fty = match self.method_nty(tr, m, self_t) {
        Some(NFun(_, _) as f) => f
        _ => raise NotTyped
      }
      let ps = match fty {
        NFun(ps, _) => ps
        _ => []
      }
      let code = self.typed_check(env, args[1 + j], fty)
      let unit = ps == [NUnit]
      let names = if unit { [] } else { ps.mapi((k, _) => "a" + k.to_string()) }
      let call = "(" +
        code +
        ")(" +
        (if unit { "" } else { names.join(", ") }) +
        ")"
      let call = if mbt_method_raises(tr, m) {
        call
      } else {
        "try {\n" +
        call +
        "\n} catch {\n_ => abort(" +
        ("error in " + tr + "::" + m).escape() +
        ")\n}"
      }
      if tr == "Hash" {
        // MoonBit's `Hash` is defined by `hash_combine`
        out.write_string(
          header +
          "hash_combine(a0, hasher) {\nhasher.combine_int(" +
          call +
          ")\n}\n",
        )
        continue
      }
      out.write_string(
        header +
        @tt.mbt_method_name(tr, m) +
        "(" +
        names.join(", ") +
        ") {\n" +
        call +
        "\n}\n",
      )
    }
    Ok(())
  } catch {
    err => Err(err)
  }
  self.cur_bounds = saved_bounds
  self.cur_result = saved_result
  match ok {
    Ok(_) => Some(out.to_string())
    Err(_) => None
  }
}

///|
/// Emit the MoonBit impl of an instance (once).
fn Gen::need_impl(self : Gen, i : String) -> Unit {
  if self.dry || self.impls_done.contains(i) {
    return
  }
  self.impls_done.push(i)
  // the native enum of the impl's type
  match self.impl_info(i) {
    Some((_, _, NEnum(d, _), _)) if @tt.mbt_info(d) is None => self.need_enum(d)
    _ => ()
  }
  match self.impl_code(i) {
    Some(code) => self.write_to(self.file_of(i), "\n/// " + i + "\n" + code)
    None => ()
  }
}

///|
/// A call of method `m` of the `#mbt` trait `tr`; `args` are the `Self`
/// type, the instance (MoonBit finds it) and the method's arguments.
fn Gen::typed_method(
  self : Gen,
  env : Array[TLocal],
  tr : String,
  m : String,
  args : Array[@tt.Tm],
) -> (String, NTy) raise NotTyped {
  self.may_raise = true
  if args.length() < 2 {
    raise NotTyped
  }
  let self_t = self.type_arg(env, args[0])
  if !self.satisfies(self_t, tr) {
    raise NotTyped
  }
  let (ps, r) = match self.method_nty(tr, m, self_t) {
    Some(NFun(ps, r)) => (ps, r)
    _ => raise NotTyped
  }
  let margs = args[2:].to_owned()
  let cs = if ps == [NUnit] {
    if margs.length() != 1 {
      raise NotTyped
    }
    []
  } else {
    self.typed_args(env, margs, ps)
  }
  let call = "(" +
    self.trait_name(tr) +
    "::" +
    @tt.mbt_method_name(tr, m) +
    "(" +
    cs.join(", ") +
    ") : " +
    self.mbt_ty(r) +
    ")"
  if !@tt.mbt_info(tr).unwrap().defined && method_raises(tr, m) {
    (
      "(try { " + call + " } catch { err => raise CRaise(foreign_error(err)) })",
      r,
    )
  } else {
    (call, r)
  }
}

///|
/// Can values of `t` be converted from `Value` (`into`) or to `Value`
/// (`!into`)? A read-only MoonBit type cannot be built outside its package,
/// so it cannot be converted from `Value`: native code passes its values
/// around, and the uniform representation only inspects them.
fn Gen::convertible(self : Gen, t : NTy, into : Bool) -> Bool {
  match t {
    NEnum(d, args) =>
      args.iter().all(a => self.convertible(a, into)) &&
      self.data_convertible(d, into, [])
    NFun(ps, r) =>
      ps.iter().all(p => self.convertible(p, !into)) &&
      self.convertible(r, into)
    // boxed as is: the arguments would have to be `Value`s
    NForeign(_, args) => args.length() == 0
    // `Value` functions are synchronous
    NAsyncFun(_, _) => false
    _ => true
  }
}

///|
fn Gen::data_convertible(
  self : Gen,
  d : String,
  into : Bool,
  seen : Array[String],
) -> Bool {
  if seen.contains(d) {
    return true
  }
  if into && @tt.mbt_info(d) is Some({ read_only: true, .. }) {
    return false
  }
  let seen = [..seen, d]
  for c in @tt.data_info(d).unwrap().cons {
    match self.con_fields(c) {
      Some(fs) =>
        for f in fs {
          match f {
            Some(NEnum(e, args)) =>
              if !args.iter().all(a => self.convertible(a, into)) ||
                !self.data_convertible(e, into, seen) {
                return false
              }
            Some(ft) => if !self.convertible(ft, into) { return false }
            None => ()
          }
        }
      None => return false
    }
  }
  true
}

///|
/// Can the uniform version of a native function be a wrapper of it?
fn Gen::wrappable(self : Gen, sig : TSig) -> Bool {
  sig.bounds.length() == 0 &&
  sig.params
  .iter()
  .all(p => {
    match p {
      Some(nt) => self.convertible(nt, true)
      None => true
    }
  }) &&
  self.convertible(sig.result, false)
}
