///|
/// MoonBit struct features. A `mut` field of a struct defined here is
/// stored in a box (a one-element array): `p.x` reads the box, `p.x = v`
/// writes it, and building the struct makes a new box. (The fields of
/// structs imported from MoonBit keep their MoonBit representation.) A
/// tuple struct `struct P(Int, Int)` has the fields `0`, `1`; `P(a, b)`
/// builds one and is its pattern.

///|
/// The mutable fields (`T::x`).
pub let mut_fields : Map[String, Bool] = Map([])

///|
/// The tuple structs.
pub let tuple_structs : Map[String, Bool] = Map([])

///|
/// The default implementations of trait methods (`impl Tr with m(..)`), by
/// `Tr::m`.
let trait_defaults : Map[String, @parser.ImplDecl] = Map([])

///|
fn reset_structs() -> Unit {
  mut_fields.clear()
  tuple_structs.clear()
  trait_defaults.clear()
}

///|
/// The type of a field, without its `mut` mark, and whether it is mutable.
fn unmark_mut(t : @parser.Expr) -> (@parser.Expr, Bool) {
  match t {
    EApp(_, EVar(_, "%Mut"), Some([a]), None) => (a, true)
    _ => (t, false)
  }
}

///|
/// `{ x, y: p, .. }` against the struct type `d`: the constructor pattern.
fn struct_pattern(
  cxt : Cxt,
  d : String,
  fields : Array[(String, @parser.Pat)],
  open : Bool,
) -> @parser.Pat raise ElabError {
  let fs = match data_info(d) {
    Some({ fields: Some(fs), .. }) => fs
    _ => cxt.fail(d + " is not a struct")
  }
  for f in fields {
    if !fs.contains(f.0) {
      cxt.fail("struct " + d + " has no field " + f.0)
    }
  }
  let subs = fs.map(f => {
    match fields.iter().find_first(x => x.0 == f) {
      Some((_, p)) => {
        if mut_fields.contains(d + "::" + f) && !(p is PWild(_)) {
          cxt.fail("a pattern cannot look into the mutable field " + f)
        }
        p
      }
      None => {
        if !open {
          cxt.fail(
            "missing field " + f + " in the pattern (add `..` to omit it)",
          )
        }
        @parser.PWild(cxt.pos)
      }
    }
  })
  PCon(cxt.pos, d + "::mk", None, subs)
}
