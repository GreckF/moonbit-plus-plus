///|
/// A type or trait of the package with the name of one of the Prelude
/// replaces it: the Prelude's type, its constructors, fields and methods, and
/// what mentions them (instances, functions, transitively) are removed before
/// the package is checked. (A package defining its own `HashMap`, say, does
/// not get the Prelude's methods on the wrong fields.)
fn prune_prelude(decls : Array[@parser.Decl]) -> Unit {
  let removed : Map[String, Bool] = Map([])
  for d in decls {
    let n = match d.inner() {
      DEnum(ed) => ed.name
      DStruct(sd) => sd.name
      DTrait(td) => td.name
      DOpaque(_, n, _) => n
      _ => continue
    }
    if globals.get(n) is Some({ kind: GData(di), .. }) && !di.builtin {
      removed.set(n, true)
    }
  }
  if removed.is_empty() {
    return
  }
  let types = removed.keys().collect()
  let names : Array[String] = globals.keys().collect()
  for g in names {
    if types.iter().any(t => g.has_prefix(t + "::")) {
      removed.set(g, true)
    }
  }
  // what mentions a removed global, until nothing changes
  let mut changed = true
  while changed {
    changed = false
    for g in names {
      if removed.contains(g) {
        continue
      }
      let e = globals.get(g).unwrap()
      let body = match e.kind {
        GFunc(Some(b), _, _) => Some(b)
        _ => None
      }
      if tm_mentions_any(e.ty, removed) ||
        body.map(b => tm_mentions_any(b, removed)).unwrap_or(false) {
        removed.set(g, true)
        changed = true
      }
    }
  }
  for g in removed.keys() {
    globals.remove(g)
    mbt_types.remove(g)
    st.traits.remove(g)
    st.instances.remove(g)
    st.instance_heads.remove(g)
    st.labels.remove(g)
  }
  let keep = (xs : Array[String]) => xs.filter(x => !removed.contains(x))
  for k, v in st.cons_by_short {
    st.cons_by_short.set(k, keep(v))
  }
  for k, v in st.trait_methods {
    st.trait_methods.set(k, keep(v))
  }
  for k, v in st.instances {
    st.instances.set(k, keep(v))
  }
  for k, v in st.instance_heads {
    st.instance_heads.set(k, keep(v))
  }
  // the Prelude's `Nat` functions run natively only if they are its own
  if removed.contains("Nat") {
    prelude_nat.val = false
  }
}

///|
/// Whether `Nat` is the Prelude's (not replaced by the package): only then
/// are the functions of `nat_natives` native.
pub let prelude_nat : Ref[Bool] = Ref(true)

///|
/// Does `t` mention one of the globals of `names`?
pub fn tm_mentions_any(t : Tm, names : Map[String, Bool]) -> Bool {
  let go = (x : Tm) => tm_mentions_any(x, names)
  let cl = (c : Clause) => {
    c.pats.iter().any(p => pat_mentions_any(p, names)) ||
    c.cond.map(go).unwrap_or(false) ||
    go(c.body)
  }
  match t {
    Global(n) => names.contains(n)
    Lam(_, _, _, b) | Return(b) | Raise(b) | Assign(_, b) => go(b)
    App(f, a, _) | Pi(_, _, _, f, a) | Raises(f, a) | Seq(f, a) | Defer(f, a) =>
      go(f) || go(a)
    Let(_, a, v, b) | LetMut(_, a, v, b) | While(a, v, b) =>
      go(a) || go(v) || go(b)
    Match(ss, cls) => ss.iter().any(go) || cls.iter().any(cl)
    Try(b, cls) => go(b) || cls.iter().any(cl)
    ArrayLit(es) => es.iter().any(go)
    Var(_)
    | Meta(_)
    | InsertedMeta(_, _)
    | U
    | PropU
    | Lit(_)
    | Break
    | Continue => false
  }
}

///|
fn pat_mentions_any(p : CPat, names : Map[String, Bool]) -> Bool {
  match p {
    CPCon(c, ps) =>
      names.contains(c) || ps.iter().any(q => pat_mentions_any(q, names))
    _ => false
  }
}
