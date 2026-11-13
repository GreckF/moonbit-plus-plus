///|
/// Native data. The uniform representation `Value` is an extensible enum of
/// the runtime (`VInt`, `VFun`, ...), extended by each generated file with
/// one variant per constructor used of its datatypes, with one `Value` field
/// per field that is not erased: `Exp::Add` of `Exp : [T] -> Type` becomes
/// `K_Exp_Add(Value, Value)`, its index gone. Constructing and matching are
/// native MoonBit; the runtime inspects constructors generically through
/// `con_name` and `con_fields`, which use decoders registered by each file.

///|
/// The variant of constructor `c` (registered on first use), and its arity.
fn Gen::ctor(self : Gen, c : String) -> (String, Int32) {
  match self.ctors.get(c) {
    Some(x) => return x
    None => ()
  }
  let buf = StringBuilder()
  buf.write_string("K_")
  let mut prev_us = true
  for ch in c {
    if is_ident_char(ch) && ch != '_' {
      buf.write_char(ch)
      prev_us = false
    } else if !prev_us {
      buf.write_char('_')
      prev_us = true
    }
  }
  let mut id = buf.to_string()
  while id.has_suffix("_") {
    id = id.unsafe_substring(start=0, end=id.length() - 1)
  }
  // distinct names for distinct constructors
  let base = id
  let mut k = 1
  while self.ctors.values().any(x => x.0 == id) {
    k = k + 1
    id = base + "_" + k.to_string()
  }
  let arity = match @tt.con_info(c) {
    Some(ci) => {
      let mut n = 0
      for j = 0; j < ci.nargs; j = j + 1 {
        if !self.er.con_erased(c, j) {
          n = n + 1
        }
      }
      n
    }
    None => 0
  }
  self.ctors.set(c, (id, arity))
  self.ctor_order.push(c)
  (id, arity)
}

///|
/// A value (or pattern) of constructor `c` with its kept fields.
fn Gen::con_code(self : Gen, c : String, args : Array[String]) -> String {
  let (id, _) = self.ctor(c)
  if args.length() == 0 {
    id
  } else {
    id + "(" + args.join(", ") + ")"
  }
}
