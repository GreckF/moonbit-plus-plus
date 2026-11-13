///|
/// Datatypes that are `Nat` after erasure: one constructor without kept
/// fields (the zero) and one whose only kept field is of the datatype itself
/// (the successor), like `Nat`, or `Fin` whose index fields are erased. Their
/// values are `BigInt`s, as in Idris 2: the zero is 0, the successor adds
/// one, and a pattern `S(…S(p))` is a test on the number (see
/// `Gen::nat_pat`). The interpreter does this for `Nat` only (it does not
/// erase).
priv struct NatLike {
  data : String
  succ : String
  /// The index of the recursive field among the successor's own arguments.
  field : Int32
}

///|
/// The shape of datatype `d` if it is like `Nat`. Propositions (erased),
/// errors (inspected by constructor name), effect capabilities, `#mbt` and
/// imported types (MoonBit types) keep their representations.
fn Gen::nat_like(self : Gen, d : String) -> NatLike? {
  match self.nat_likes.get(d) {
    Some(r) => return r
    None => ()
  }
  let r = self.compute_nat_like(d)
  self.nat_likes.set(d, r)
  r
}

///|
fn Gen::compute_nat_like(self : Gen, d : String) -> NatLike? {
  let di = match @tt.data_info(d) {
    Some(di) => di
    None => return None
  }
  if di.is_prop ||
    di.is_trait ||
    di.is_error ||
    di.builtin ||
    @tt.is_effect(d) ||
    d.has_prefix("%") ||
    d.has_prefix("@") ||
    is_mbt_type(d) ||
    di.cons.length() != 2 {
    return None
  }
  // the kept fields of a constructor, with their types
  let kept = (c : String) => {
    let ci = @tt.con_info(c).unwrap()
    let out : Array[(Int32, @tt.Tm)] = []
    let mut t = @tt.globals.get(c).unwrap().ty
    for k = 0; k < ci.nparams + ci.nargs; k = k + 1 {
      match t {
        Pi(_, _, _, a, b) => {
          let j = k - ci.nparams
          if j >= 0 && !self.er.con_erased(c, j) {
            out.push((j, a))
          }
          t = b
        }
        _ => return None
      }
    }
    Some(out)
  }
  for z = 0; z < 2; z = z + 1 {
    let zero = di.cons[z]
    let succ = di.cons[1 - z]
    match (kept(zero), kept(succ)) {
      (Some([]), Some([(j, a)])) if flatten_app(a).0 is Global(h) && h == d =>
        return Some({ data: d, succ, field: j, })
      _ => ()
    }
  }
  None
}

///|
/// The Nat-like datatype of constructor `c`, and whether it is the successor.
fn Gen::nat_con(self : Gen, c : String) -> (NatLike, Bool)? {
  match @tt.con_info(c) {
    Some(ci) =>
      match self.nat_like(ci.data) {
        Some(nl) => Some((nl, c == nl.succ))
        None => None
      }
    None => None
  }
}

///|
/// The number a saturated `S(…S(Z))` of a Nat-like datatype denotes, and the
/// datatype.
fn Gen::nat_numeral(self : Gen, t : @tt.Tm) -> (Int32, String)? {
  let mut k = 0
  let mut cur = t
  while true {
    let (h, args) = flatten_app(cur)
    guard h is Global(c) && @tt.con_info(c) is Some(ci) else { return None }
    guard self.nat_con(c) is Some((nl, is_succ)) else { return None }
    if args.length() != ci.nparams + ci.nargs {
      return None
    }
    if !is_succ {
      return Some((k, nl.data))
    }
    k = k + 1
    cur = args[ci.nparams + nl.field]
  }
  None
}

///|
/// A pattern `S(…S(q))` of a Nat-like datatype, with `q` a variable, `_` or
/// the zero, is the test `n >= k`, or `n == k` when `q` is the zero (the
/// result: `(k, exact)`). Its slots, in slot order, are given to `slot`: the
/// nodes of the chain (`Some(j)`: the value `n - j`) and their erased fields
/// (`None`; only variables bind them, see erase.mbt).
fn Gen::nat_pat(
  self : Gen,
  p : @tt.CPat,
  slot : (Int32?) -> Unit,
) -> (Int32, Bool) {
  fn go(q : @tt.CPat, depth : Int32) -> (Int32, Bool) {
    slot(Some(depth))
    match q {
      CPCon(c, ps) =>
        match self.nat_con(c) {
          Some((nl, true)) => {
            let mut r = (depth, false)
            for j = 0; j < ps.length(); j = j + 1 {
              if j == nl.field {
                r = go(ps[j], depth + 1)
              } else {
                slot(None)
              }
            }
            r
          }
          _ => {
            for _ in ps {
              slot(None)
            }
            (depth, true)
          }
        }
      _ => (depth, false)
    }
  }

  go(p, 0)
}
