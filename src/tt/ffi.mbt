///|
/// Imported MoonBit functions in the generators of splices (see
/// doc/mbtpp/staging.md). The checker has only the types of imported
/// functions, so a splice that calls one needs a host that can run MoonBit:
/// `moonpp` builds a MoonBit program with the imported functions (the
/// wrappers of the compiler) and loads it, and the checker calls it with
/// the values of the arguments written as text. Only data cross: numbers,
/// strings, arrays, values of datatypes, and handles of values of MoonBit
/// types that have no definition here (`Map`, ...), which stay with the host.
///
/// The text of a value:
///
/// - `u` unit, `b0` / `b1` booleans, `i<n>;` `Int`, `L<n>;` `Int64`,
///   `U<n>;` `UInt`, `V<n>;` `UInt64`, `y<n>;` `Byte`, `c<n>;` `Char`
///   (its code), `d<n>;` `Double` and `f<n>;` `Float` (their bits),
///   `n<digits>;` a natural number or `BigInt`;
/// - `s<k>:` and `k` characters: a string;
/// - `a<k>;` and `k` values: an array;
/// - `k<m>:` and `m` characters, `<k>;` and `k` values: a constructor
///   (by its name) and its fields;
/// - `h<id>;`: a value kept by the host.
///
/// A call is `call(name, arguments)` where `arguments` is `a<k>;` and the
/// `k` arguments, one for each binder of the function (`u` for the ones
/// that are types or instances), and the answer is `o` and a value, `r` and
/// a string (an error raised), or `e` and a string (the call failed).

///|
/// A host that runs imported MoonBit functions.
pub(all) struct FfiHost {
  /// Make the imported functions `names` (global names) callable. An error
  /// message if it fails.
  prepare : (Array[String]) -> String?
  /// Call an imported function (its global name) with the text of its
  /// arguments; the text of the answer.
  call : (String, String) -> String
}

///|
pub let ffi_host : Ref[FfiHost?] = Ref::new(None)

///|
/// The imported functions that the host can call.
let ffi_ready : Map[String, Bool] = {}

///|
/// Why the last call of an imported function failed (for the error of a
/// splice that is stuck on it).
pub let ffi_error : Ref[String?] = Ref::new(None)

///|
fn reset_ffi() -> Unit {
  ffi_ready.clear()
  ffi_error.val = None
}

// ---------------------------------------------------------------------------
// Writing

///|
fn put_string(out : StringBuilder, s : String) -> Unit {
  let cs : Array[Char] = s.iter().collect()
  out.write_string("s" + cs.length().to_string() + ":")
  for c in cs {
    out.write_char(c)
  }
}

///|
/// Write the value `v` (the checker's); `false` if it is not known yet (a
/// variable, a call that is stuck, a function, ...).
fn put_val(out : StringBuilder, v : Val) -> Bool {
  if prelude_nat.val && nat_val(v) is Some(n) {
    out.write_string("n" + n.to_string() + ";")
    return true
  }
  match force(v) {
    VLit(l) =>
      match l {
        LUnit => out.write_string("u")
        LBool(b) => out.write_string(if b { "b1" } else { "b0" })
        LInt(n) => out.write_string("i" + n.to_string() + ";")
        LInt64(n) => out.write_string("L" + n.to_string() + ";")
        LUInt(n) => out.write_string("U" + n.to_string() + ";")
        LUInt64(n) => out.write_string("V" + n.to_string() + ";")
        LByte(n) => out.write_string("y" + n.to_int().to_string() + ";")
        LChar(c) => out.write_string("c" + c.to_int().to_string() + ";")
        LDouble(d) =>
          out.write_string("d" + d.reinterpret_as_int64().to_string() + ";")
        LFloat(f) =>
          out.write_string(
            "f" + f.to_double().reinterpret_as_int64().to_string() + ";",
          )
        LStr(s) => put_string(out, s)
      }
    VArrLit(xs) => {
      out.write_string("a" + xs.length().to_string() + ";")
      for x in xs {
        if !put_val(out, x) {
          return false
        }
      }
    }
    VCon(c, sp) =>
      match con_info(c) {
        Some(ci) if sp.length() >= ci.nparams => {
          let own = sp[ci.nparams:].to_array().filter(a => a.1 != Impl)
          let cs : Array[Char] = c.iter().collect()
          out.write_string("k" + cs.length().to_string() + ":")
          for ch in cs {
            out.write_char(ch)
          }
          out.write_string(own.length().to_string() + ";")
          for a in own {
            if !put_val(out, a.0) {
              return false
            }
          }
        }
        _ => return false
      }
    VPrim("%foreign", [(h, _)]) =>
      match force(h) {
        VLit(LInt(id)) => out.write_string("h" + id.to_string() + ";")
        _ => return false
      }
    _ => return false
  }
  true
}

// ---------------------------------------------------------------------------
// Reading

///|
/// The text of a value is not what was expected.
priv suberror ReadFail {
  ReadFail
}

///|
priv struct Reader {
  cs : Array[Char]
  mut pos : Int32
}

///|
fn Reader::next(self : Reader) -> Char raise ReadFail {
  if self.pos < self.cs.length() {
    let c = self.cs[self.pos]
    self.pos = self.pos + 1
    c
  } else {
    raise ReadFail
  }
}

///|
/// The characters up to `stop` (which is skipped).
fn Reader::until(self : Reader, stop : Char) -> String raise ReadFail {
  let buf = StringBuilder::new()
  while true {
    let c = self.next()
    if c == stop {
      break
    }
    buf.write_char(c)
  }
  buf.to_string()
}

///|
/// `k` characters.
fn Reader::take(self : Reader, k : Int32) -> String raise ReadFail {
  if k < 0 || self.pos + k > self.cs.length() {
    raise ReadFail
  }
  let buf = StringBuilder::new()
  for _ in 0..<k {
    buf.write_char(self.cs[self.pos])
    self.pos = self.pos + 1
  }
  buf.to_string()
}

///|
/// A number written up to `stop`.
fn Reader::int(self : Reader, stop : Char) -> Int32 raise ReadFail {
  parse_int64(self.until(stop)).to_int()
}

///|
/// A string written by `put_string` without its `s`.
fn Reader::string(self : Reader) -> String raise ReadFail {
  let k = self.int(':')
  self.take(k)
}

///|
fn parse_int64(s : String) -> Int64 raise ReadFail {
  let cs : Array[Char] = s.iter().collect()
  if cs.length() == 0 {
    raise ReadFail
  }
  let neg = cs[0] == '-'
  let mut acc : Int64 = 0
  let mut seen = false
  for i = (if neg { 1 } else { 0 }); i < cs.length(); i = i + 1 {
    let c = cs[i]
    if c < '0' || c > '9' {
      raise ReadFail
    }
    seen = true
    let d = (c.to_int() - '0'.to_int()).to_int64()
    // negative numbers are accumulated downwards (`Int64::MIN` fits)
    acc = if neg { acc * 10L - d } else { acc * 10L + d }
  }
  if !seen {
    raise ReadFail
  }
  acc
}

///|
fn parse_uint64(s : String) -> UInt64 raise ReadFail {
  let cs : Array[Char] = s.iter().collect()
  if cs.length() == 0 {
    raise ReadFail
  }
  let mut acc : UInt64 = 0
  for c in cs {
    if c < '0' || c > '9' {
      raise ReadFail
    }
    acc = acc * 10UL + (c.to_int() - '0'.to_int()).to_uint64()
  }
  acc
}

///|
/// Read a value of the type `ty` (a type of the checker). The scalars do not
/// need it; datatypes take the parameters of their constructors from it.
fn get_val(r : Reader, ty : Val) -> Val raise ReadFail {
  match r.next() {
    'u' => VLit(LUnit)
    'b' => VLit(LBool(r.next() == '1'))
    's' => VLit(LStr(r.string()))
    'i' => VLit(LInt(parse_int64(r.until(';')).to_int()))
    'L' => VLit(LInt64(parse_int64(r.until(';'))))
    'U' => VLit(LUInt(parse_uint64(r.until(';')).to_uint()))
    'V' => VLit(LUInt64(parse_uint64(r.until(';'))))
    'y' => VLit(LByte(parse_int64(r.until(';')).to_byte()))
    'c' => VLit(LChar(r.int(';').unsafe_to_char()))
    'd' => VLit(LDouble(parse_int64(r.until(';')).reinterpret_as_double()))
    'f' =>
      VLit(
        LFloat(
          Float::from_double(parse_int64(r.until(';')).reinterpret_as_double()),
        ),
      )
    'n' => eval([], nat_tm(r.int(';')))
    'h' => VPrim("%foreign", [(VLit(LInt(r.int(';'))), Expl)])
    'a' => {
      let k = r.int(';')
      let elem = match force(ty) {
        VData("Array", [(a, _)]) => a
        _ => VU
      }
      let xs : Array[Val] = []
      for _ in 0..<k {
        xs.push(get_val(r, elem))
      }
      VArrLit(xs)
    }
    'k' => {
      let name = r.take(r.int(':'))
      let k = r.int(';')
      get_con(r, name, k, ty)
    }
    _ => raise ReadFail
  }
}

///|
/// The rest of a constructor `name` with `k` fields, of the type `ty`.
fn get_con(
  r : Reader,
  name : String,
  k : Int32,
  ty : Val,
) -> Val raise ReadFail {
  let (ci, ge) = match (con_info(name), globals.get(name)) {
    (Some(ci), Some(ge)) => (ci, ge)
    _ => raise ReadFail
  }
  let params = match force(ty) {
    VData(_, sp) if sp.length() >= ci.nparams => sp[0:ci.nparams].to_array()
    _ => raise ReadFail
  }
  let args : Spine = []
  let mut t = ge.vty
  for p in params {
    match force(t) {
      VPi(_, _, _, _, cl) => {
        args.push((p.0, Impl))
        t = inst(cl, p.0)
      }
      _ => raise ReadFail
    }
  }
  for _ in 0..<k {
    match force(t) {
      VPi(_, Expl, _, a, cl) => {
        let v = get_val(r, a)
        args.push((v, Expl))
        t = inst(cl, v)
      }
      _ => raise ReadFail
    }
  }
  VCon(name, args)
}

// ---------------------------------------------------------------------------
// Calls

///|
/// The result type of the imported function `n` applied to `sp`, and
/// whether it may raise.
fn ffi_result_type(n : String, sp : Spine) -> (Val, Bool)? {
  let g = match globals.get(n) {
    Some(g) => g
    None => return None
  }
  match instantiate(g.vty, sp) {
    Some(VRaises(r, _)) => Some((r, true))
    Some(t) => Some((t, false))
    None => None
  }
}

///|
/// Call the imported function `n` (applied to all its arguments `sp`) in the
/// host: its result, or `None` when the arguments are not known (the call
/// stays as it is) or the host cannot call it (`ffi_error` says why).
fn run_ffi(n : String, sp : Spine) -> Val? {
  let host = match ffi_host.val {
    Some(h) => h
    None => return None
  }
  if !ffi_ready.contains(n) {
    return None
  }
  let rty = match ffi_result_type(n, sp) {
    Some((t, _)) => t
    None => return None
  }
  let out = StringBuilder::new()
  out.write_string("a" + sp.length().to_string() + ";")
  for a in sp {
    if a.1 == Expl {
      if !put_val(out, a.0) {
        return None
      }
    } else {
      out.write_string("u")
    }
  }
  let ans = (host.call)(n, out.to_string())
  let r : Reader = { cs: ans.iter().collect(), pos: 0, }
  let reason = (what : String) => {
    let msg = r.string() catch { _ => ans }
    ffi_error.val = Some("the MoonBit function " + n + " " + what + ": " + msg)
    None
  }
  let tag = r.next() catch { _ => 'e' }
  match tag {
    'o' =>
      Some(get_val(r, rty)) catch {
        _ => {
          ffi_error.val = Some(
            "cannot read the result of the MoonBit function " + n + ": " + ans,
          )
          None
        }
      }
    // an error raised by the MoonBit function
    'r' => {
      let msg = r.string() catch { _ => ans }
      Some(raise_val(VLit(LStr(msg))))
    }
    _ => reason("could not be called")
  }
}

///|
/// The imported MoonBit functions (their global names) that the definitions
/// reachable from those with a splice call.
fn imported_functions_of_splices() -> Array[String] {
  let splice : Map[String, Bool] = { "%splice": true }
  let seen : Map[String, Bool] = {}
  let todo : Array[String] = []
  for n, g in globals {
    match g.kind {
      GFunc(Some(body), _, _) if tm_mentions_any(body, splice) => todo.push(n)
      _ => ()
    }
  }
  let found : Array[String] = []
  while todo.pop() is Some(n) {
    if seen.contains(n) {
      continue
    }
    seen.set(n, true)
    match globals.get(n) {
      Some({ kind: GPrim(p, _), .. }) if p.has_prefix("@mbt:") => found.push(n)
      Some({ kind: GFunc(Some(body), _, _), ty, .. }) => {
        let all : Map[String, Bool] = {}
        collect_globals(body, all)
        collect_globals(ty, all)
        for m, _ in all {
          if !seen.contains(m) {
            todo.push(m)
          }
        }
      }
      _ => ()
    }
  }
  found.sort()
  found
}

///|
/// The globals that `t` mentions.
fn collect_globals(t : Tm, out : Map[String, Bool]) -> Unit {
  match t {
    Global(n) => out.set(n, true)
    Match(ss, cls) => {
      for s in ss {
        collect_globals(s, out)
      }
      for cl in cls {
        collect_pattern_globals(cl.pats, out)
        match cl.cond {
          Some(c) => collect_globals(c, out)
          None => ()
        }
        collect_globals(cl.body, out)
      }
    }
    Try(b, cls) => {
      collect_globals(b, out)
      for cl in cls {
        collect_pattern_globals(cl.pats, out)
        match cl.cond {
          Some(c) => collect_globals(c, out)
          None => ()
        }
        collect_globals(cl.body, out)
      }
    }
    _ =>
      ignore(
        tm_map(t, x => {
          collect_globals(x, out)
          x
        }),
      )
  }
}

///|
fn collect_pattern_globals(ps : Array[CPat], out : Map[String, Bool]) -> Unit {
  for p in ps {
    match p {
      CPCon(c, qs) => {
        out.set(c, true)
        collect_pattern_globals(qs, out)
      }
      _ => ()
    }
  }
}
