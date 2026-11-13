///|
/// The driver of the splices of a package (see tt/ffi.mbt): a MoonBit
/// program that has the imported functions the splices call, with the
/// wrappers of the compiler, and a `call` function that moonpp loads and the
/// checker calls with the text of the values of the arguments.
let driver_file : String = "mbtpp_driver.mbt"

///|
/// The driver's own code: the text of values, and `call`.
let driver_src : String =
  #|// ---- the driver of the splices of MoonBit++ ----------------------------
  #|
  #|/// The imported functions that can be called, by global name, and why the
  #|/// others cannot.
  #|let ffi_table : Map[String, (Array[Value]) -> Value raise] = {}
  #|
  #|let ffi_why : Map[String, String] = {}
  #|
  #|/// Values of foreign types that the checker holds a handle of.
  #|let foreign_table : Array[Foreign] = []
  #|
  #|suberror DriverFail {
  #|  DriverFail(String)
  #|}
  #|
  #|/// Run a function of the checker (given by its number).
  #|extern "js" fn host_callback(id : Int, args : String) -> String =
  #|  "(id, a) => globalThis.__mbtpp_callback(id, a)"
  #|
  #|struct Rd {
  #|  cs : Array[Char]
  #|  mut pos : Int
  #|}
  #|
  #|fn rd_next(r : Rd) -> Char raise {
  #|  if r.pos < r.cs.length() {
  #|    let c = r.cs[r.pos]
  #|    r.pos = r.pos + 1
  #|    c
  #|  } else {
  #|    raise DriverFail("the text of a value ends too early")
  #|  }
  #|}
  #|
  #|fn rd_until(r : Rd, stop : Char) -> String raise {
  #|  let buf = StringBuilder::new()
  #|  while true {
  #|    let c = rd_next(r)
  #|    if c == stop {
  #|      break
  #|    }
  #|    buf.write_char(c)
  #|  }
  #|  buf.to_string()
  #|}
  #|
  #|fn rd_take(r : Rd, k : Int) -> String raise {
  #|  if k < 0 || r.pos + k > r.cs.length() {
  #|    raise DriverFail("bad length in the text of a value")
  #|  }
  #|  let buf = StringBuilder::new()
  #|  for _ in 0..<k {
  #|    buf.write_char(r.cs[r.pos])
  #|    r.pos = r.pos + 1
  #|  }
  #|  buf.to_string()
  #|}
  #|
  #|fn rd_i64(s : String) -> Int64 raise {
  #|  let cs : Array[Char] = s.iter().collect()
  #|  if cs.length() == 0 {
  #|    raise DriverFail("bad number")
  #|  }
  #|  let neg = cs[0] == '-'
  #|  let mut acc : Int64 = 0
  #|  for i = if neg { 1 } else { 0 }; i < cs.length(); i = i + 1 {
  #|    let c = cs[i]
  #|    if c < '0' || c > '9' {
  #|      raise DriverFail("bad number")
  #|    }
  #|    let d = (c.to_int() - '0'.to_int()).to_int64()
  #|    acc = if neg { acc * 10L - d } else { acc * 10L + d }
  #|  }
  #|  acc
  #|}
  #|
  #|fn rd_u64(s : String) -> UInt64 raise {
  #|  let cs : Array[Char] = s.iter().collect()
  #|  if cs.length() == 0 {
  #|    raise DriverFail("bad number")
  #|  }
  #|  let mut acc : UInt64 = 0
  #|  for c in cs {
  #|    if c < '0' || c > '9' {
  #|      raise DriverFail("bad number")
  #|    }
  #|    acc = acc * 10UL + (c.to_int() - '0'.to_int()).to_uint64()
  #|  }
  #|  acc
  #|}
  #|
  #|fn rd_big(s : String) -> BigInt raise {
  #|  let cs : Array[Char] = s.iter().collect()
  #|  if cs.length() == 0 {
  #|    raise DriverFail("bad number")
  #|  }
  #|  let mut acc : BigInt = 0N
  #|  for c in cs {
  #|    if c < '0' || c > '9' {
  #|      raise DriverFail("bad number")
  #|    }
  #|    acc = acc * 10N + BigInt::from_int(c.to_int() - '0'.to_int())
  #|  }
  #|  acc
  #|}
  #|
  #|fn rd_int(r : Rd, stop : Char) -> Int raise {
  #|  rd_i64(rd_until(r, stop)).to_int()
  #|}
  #|
  #|fn rd_string(r : Rd) -> String raise {
  #|  let k = rd_int(r, ':')
  #|  rd_take(r, k)
  #|}
  #|
  #|/// The value written in the text `r` (see tt/ffi.mbt for the format).
  #|fn text_value(r : Rd) -> Value raise {
  #|  match rd_next(r) {
  #|    'u' => VUnit
  #|    'b' => VBool(rd_next(r) == '1')
  #|    's' => VStr(rd_string(r))
  #|    'i' => VInt(rd_int(r, ';'))
  #|    'L' => VInt64(rd_i64(rd_until(r, ';')))
  #|    'U' => VUInt(rd_u64(rd_until(r, ';')).to_uint())
  #|    'V' => VUInt64(rd_u64(rd_until(r, ';')))
  #|    'y' => VByte(rd_i64(rd_until(r, ';')).to_byte())
  #|    'c' => VChar(rd_int(r, ';').unsafe_to_char())
  #|    'd' => VDouble(rd_i64(rd_until(r, ';')).reinterpret_as_double())
  #|    'f' =>
  #|      VFloat(Float::from_double(rd_i64(rd_until(r, ';')).reinterpret_as_double()))
  #|    'n' => VNat(rd_big(rd_until(r, ';')))
  #|    'h' => {
  #|      let id = rd_int(r, ';')
  #|      if id >= 0 && id < foreign_table.length() {
  #|        VForeign(foreign_table[id])
  #|      } else {
  #|        raise DriverFail("bad handle")
  #|      }
  #|    }
  #|    'a' => {
  #|      let k = rd_int(r, ';')
  #|      let xs : Array[Value] = []
  #|      for _ in 0..<k {
  #|        xs.push(text_value(r))
  #|      }
  #|      VArr(xs)
  #|    }
  #|    // a function of the checker, called back with its arguments
  #|    'F' => {
  #|      let id = rd_int(r, ';')
  #|      let n = rd_int(r, ';')
  #|      checker_fun(id, n, [])
  #|    }
  #|    'k' => {
  #|      let n = rd_int(r, ':')
  #|      let name = rd_take(r, n)
  #|      let k = rd_int(r, ';')
  #|      let xs : Array[Value] = []
  #|      for _ in 0..<k {
  #|        xs.push(text_value(r))
  #|      }
  #|      for m in con_makers {
  #|        match m(name, xs) {
  #|          Some(v) => return v
  #|          None => ()
  #|        }
  #|      }
  #|      raise DriverFail("unknown constructor " + name + " with " + k.to_string() + " fields")
  #|    }
  #|    _ => raise DriverFail("bad text of a value")
  #|  }
  #|}
  #|
  #|/// The function `id` of the checker as a curried value of `n` parameters.
  #|fn checker_fun(id : Int, n : Int, got : Array[Value]) -> Value {
  #|  VFun(a => {
  #|    let all = got.copy()
  #|    all.push(a)
  #|    if all.length() < n {
  #|      checker_fun(id, n, all)
  #|    } else {
  #|      let out = StringBuilder::new()
  #|      out.write_string("a" + all.length().to_string() + ";")
  #|      for x in all {
  #|        value_text(out, x)
  #|      }
  #|      let ans = host_callback(id, out.to_string())
  #|      let r : Rd = { cs: ans.iter().collect(), pos: 0 }
  #|      match rd_next(r) {
  #|        'o' => text_value(r)
  #|        'r' => raise CRaise(VDyn("MoonBitError", [VStr(rd_string(r))]))
  #|        _ => raise DriverFail(rd_string(r))
  #|      }
  #|    }
  #|  })
  #|}
  #|
  #|fn put_str(out : StringBuilder, s : String) -> Unit {
  #|  let cs : Array[Char] = s.iter().collect()
  #|  out.write_string("s" + cs.length().to_string() + ":")
  #|  for c in cs {
  #|    out.write_char(c)
  #|  }
  #|}
  #|
  #|/// Write a value as text.
  #|fn value_text(out : StringBuilder, v : Value) -> Unit raise {
  #|  match v {
  #|    VUnit | VType => out.write_string("u")
  #|    VBool(b) => out.write_string(if b { "b1" } else { "b0" })
  #|    VInt(n) => out.write_string("i" + n.to_string() + ";")
  #|    VInt64(n) => out.write_string("L" + n.to_string() + ";")
  #|    VUInt(n) => out.write_string("U" + n.to_string() + ";")
  #|    VUInt64(n) => out.write_string("V" + n.to_string() + ";")
  #|    VByte(n) => out.write_string("y" + n.to_int().to_string() + ";")
  #|    VChar(c) => out.write_string("c" + c.to_int().to_string() + ";")
  #|    VDouble(d) =>
  #|      out.write_string("d" + d.reinterpret_as_int64().to_string() + ";")
  #|    VFloat(f) =>
  #|      out.write_string("f" + f.to_double().reinterpret_as_int64().to_string() + ";")
  #|    VStr(s) => put_str(out, s)
  #|    VNat(n) => out.write_string("n" + n.to_string() + ";")
  #|    VArr(xs) => {
  #|      out.write_string("a" + xs.length().to_string() + ";")
  #|      for x in xs {
  #|        value_text(out, x)
  #|      }
  #|    }
  #|    VForeign(f) => {
  #|      foreign_table.push(f)
  #|      out.write_string("h" + (foreign_table.length() - 1).to_string() + ";")
  #|    }
  #|    VFun(_) => raise DriverFail("a function cannot be passed to the checker")
  #|    _ =>
  #|      match con_decode(v) {
  #|        Some((c, xs)) => {
  #|          let cs : Array[Char] = c.iter().collect()
  #|          out.write_string("k" + cs.length().to_string() + ":")
  #|          for ch in cs {
  #|            out.write_char(ch)
  #|          }
  #|          out.write_string(xs.length().to_string() + ";")
  #|          for x in xs {
  #|            value_text(out, x)
  #|          }
  #|        }
  #|        None => raise DriverFail("cannot pass " + show_value(v) + " to the checker")
  #|      }
  #|  }
  #|}
  #|
  #|/// Call the imported function `name` with the text of its arguments;
  #|/// the text of the answer (`o` and the value, `r` an error the function
  #|/// raised, `e` a failure of the call).
  #|pub fn call(name : String, args : String) -> String {
  #|  let out = StringBuilder::new()
  #|  try {
  #|    match ffi_table.get(name) {
  #|      None =>
  #|        raise DriverFail(
  #|          match ffi_why.get(name) {
  #|            Some(why) => why
  #|            None => "the driver has no function " + name
  #|          },
  #|        )
  #|      Some(f) => {
  #|        let r : Rd = { cs: args.iter().collect(), pos: 0 }
  #|        if rd_next(r) != 'a' {
  #|          raise DriverFail("bad arguments")
  #|        }
  #|        let k = rd_int(r, ';')
  #|        let vs : Array[Value] = []
  #|        for _ in 0..<k {
  #|          vs.push(text_value(r))
  #|        }
  #|        let res = f(vs)
  #|        out.write_string("o")
  #|        value_text(out, res)
  #|      }
  #|    }
  #|  } catch {
  #|    CRaise(e) => {
  #|      out.reset()
  #|      out.write_string("r")
  #|      put_str(
  #|        out,
  #|        match e {
  #|          VDyn("MoonBitError", [VStr(m)]) => m
  #|          _ => show_value(e)
  #|        },
  #|      )
  #|    }
  #|    DriverFail(m) => {
  #|      out.reset()
  #|      out.write_string("e")
  #|      put_str(out, m)
  #|    }
  #|    e => {
  #|      out.reset()
  #|      out.write_string("e")
  #|      put_str(out, e.to_string())
  #|    }
  #|  }
  #|  out.to_string()
  #|}
  #|
  #|fn main {
  #|  ()
  #|}
  #|

///|
/// The MoonBit program of the driver for the imported functions `names`
/// (global names): its files, and the functions that cannot be called with
/// the reason (their signatures use types that cannot be converted).
pub fn generate_driver(
  imports : Array[(String, String)],
  names : Array[String],
) -> (Array[(String, String)], Array[(String, String)]) raise CodegenError {
  warnings.clear()
  let g = Gen::new(imports)
  let skipped : Array[(String, String)] = []
  let init = StringBuilder()
  init.write_string("\n///|\nfn init {\n")
  for n in names {
    match @tt.globals.get(n) {
      Some({ kind: GPrim(p, arity), ty, .. }) if p.has_prefix("@mbt:") =>
        try {
          let f = g.ffi_fn(n, p, ty, arity)
          init.write_string("  ffi_table.set(" + n.escape() + ", " + f + ")\n")
        } catch {
          CodegenError(msg) => {
            skipped.push((n, msg))
            init.write_string(
              "  ffi_why.set(" + n.escape() + ", " + msg.escape() + ")\n",
            )
          }
        }
      _ => skipped.push((n, n + " is not an imported function"))
    }
  }
  init.write_string("}\n")
  g.write_to(imports_file, init.to_string())
  let files = g.output_files()
  files.push(
    (driver_file, "// Generated by moonpp. Do not edit.\n\n" + driver_src),
  )
  (files, skipped)
}
