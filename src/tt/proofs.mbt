///|
/// Proofs for the compiler. Propositions are proof irrelevant: two proofs of
/// a proposition are equal, and a proof is only eliminated into a
/// proposition or, for a subsingleton (at most one constructor, whose fields
/// are proofs), whatever the goal. So no value depends on a proof, and the
/// compiler erases them: proof parameters and fields, `let`s of proofs and
/// calls of lemmas.

///|
/// Which of the first `n` parameters of global `name` are proofs.
pub fn proof_params(name : String, n : Int32) -> Array[Bool] {
  match globals.get(name) {
    Some(g) => proof_binders(eval([], g.ty), n)
    None => Array::make(n, false)
  }
}

///|
/// Which of the fields of constructor `c` (after its parameters) are
/// proofs.
pub fn proof_fields(c : String) -> Array[Bool] {
  match (globals.get(c), con_info(c)) {
    (Some(g), Some(ci)) => {
      let all = proof_binders(eval([], g.ty), ci.nparams + ci.nargs)
      all[ci.nparams:].to_owned()
    }
    _ => []
  }
}

///|
fn proof_binders(ty : Val, n : Int32) -> Array[Bool] {
  let out : Array[Bool] = []
  let mut t = ty
  let mut ts : LTypes = []
  for i = 0; i < n; i = i + 1 {
    match force(t) {
      VPi(_, _, _, a, cl) => {
        out.push(is_prop_type(ts, a))
        ts = types_push(ts, Some(a))
        t = inst(cl, v_var(i))
      }
      _ => out.push(false)
    }
  }
  out
}

///|
/// Does global `name` (a lemma, a function returning a proof, a constructor
/// of a proposition) produce proofs?
pub fn is_proof_global(name : String) -> Bool {
  match globals.get(name) {
    Some({ kind: GFunc(_, _, _) | GCon(_) | GPrim(_, _), ty, .. }) =>
      is_prop_type([], eval([], ty))
    _ => false
  }
}

///|
/// Is the type `t` (of a `let`, in any context) a proposition? Only
/// propositions given by a datatype (`x === y`, `Le(a, b)`) are recognised.
pub fn is_prop_head(t : Tm) -> Bool {
  let mut h = t
  while h is App(f, _, _) {
    h = f
  }
  match h {
    Global(d) =>
      match data_info(d) {
        Some(di) => di.is_prop
        None => false
      }
    _ => false
  }
}
