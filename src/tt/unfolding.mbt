///|
/// Controlled unfolding (doc/mbtpp/unfolding.md): `#opaque` functions are
/// not unfolded (nor run) during type checking, except where unfolded by
/// `#unfold(f)`, `unfold(f) { e }` or the `unfold` tactic. Unfolding is
/// transitive: unfolding `g` unfolds what `g` unfolds, and a transparent
/// function that unfolds something is unfolded only where that can be.

///|
/// The opaque functions (`true`: sealed, never unfolded outside its own
/// definition).
let unfold_modes : Map[String, Bool] = {}

///|
/// The functions each function unfolds (`#unfold`, `unfold` blocks and
/// tactics in its definition, or those of the declaration that made it).
let unfold_deps : Map[String, Array[String]] = {}

///|
/// The names of the `#unfold` attributes, with their positions (checked
/// when the definition is).
let unfold_attr_names : Map[String, Array[(Pos, String)]] = {}

///|
/// Where functions may be unfolded: the definition of `owner` (`""` for a
/// signature), with the names unfolded explicitly and their closure.
priv struct UFrame {
  owner : String
  explicit : Array[String]
  set : Map[String, Bool]
  /// functions made while checking the definition (local functions, ...)
  helpers : Array[String]
}

///|
let unfold_frames : Array[UFrame] = []

///|
/// The opaque functions that could not be unfolded while checking the
/// current declaration (for a hint when it fails).
let blocked_opaque : Array[String] = []

///|
fn reset_unfolding() -> Unit {
  unfold_modes.clear()
  unfold_deps.clear()
  unfold_attr_names.clear()
  unfold_frames.clear()
  blocked_opaque.clear()
}

///|
/// Record and remove the `#opaque` and `#unfold` attributes of a
/// declaration.
fn strip_unfold_attrs(d : @parser.Decl) -> @parser.Decl {
  match d {
    DUnfoldAttr(_, a, inner) => {
      let name = match inner.inner() {
        DFn(fd) => Some(fd.name)
        // `lemma l : P = proof { … }`
        DDef(_, n, _, _, _) => Some(n)
        _ => None
      }
      match name {
        Some(n) =>
          match a {
            Opaque => unfold_modes.set(n, false)
            Sealed => unfold_modes.set(n, true)
            Unfolds(names) =>
              for x in names {
                map_push(unfold_deps, n, x.1)
                map_push(unfold_attr_names, n, x)
              }
          }
        None => ()
      }
      strip_unfold_attrs(inner)
    }
    DMbt(p, n, ro, x) => DMbt(p, n, ro, strip_unfold_attrs(x))
    DPub(x) => DPub(strip_unfold_attrs(x))
    DDerive(ds, x) => DDerive(ds, strip_unfold_attrs(x))
    DLimit(p, l, x) => DLimit(p, l, strip_unfold_attrs(x))
    _ => d
  }
}

///|
/// `names` and what they unfold, transitively.
fn unfold_closure(names : Array[String]) -> Map[String, Bool] {
  let set : Map[String, Bool] = {}
  let todo = names.copy()
  while todo.pop() is Some(n) {
    if !set.contains(n) {
      set.set(n, true)
      for d in unfold_deps.get(n).unwrap_or([]) {
        todo.push(d)
      }
    }
  }
  set
}

///|
/// May the global function `n` be unfolded here?
fn can_unfold(n : String) -> Bool {
  if unfold_everything.val ||
    (unfold_modes.is_empty() && unfold_deps.is_empty()) {
    return true
  }
  can_unfold_in(n, [])
}

///|
fn can_unfold_in(n : String, visiting : Array[String]) -> Bool {
  if unfold_frames.last() is Some(f) && f.set.contains(n) {
    return true
  }
  if unfold_modes.contains(n) {
    if !blocked_opaque.contains(n) {
      blocked_opaque.push(n)
    }
    return false
  }
  // a transparent function is unfolded where what it unfolds can be
  if visiting.contains(n) {
    return true
  }
  match unfold_deps.get(n) {
    Some(ds) => {
      visiting.push(n)
      let ok = ds.iter().all(d => can_unfold_in(d, visiting))
      ignore(visiting.pop())
      ok
    }
    None => true
  }
}

///|
fn push_frame(owner : String, explicit : Array[String]) -> Unit {
  unfold_frames.push({
    owner,
    explicit,
    set: unfold_closure(explicit),
    helpers: [],
  })
}

///|
/// Check the definition of `owner` (`th`) where it and what it unfolds may
/// be unfolded.
fn with_unfolding(
  owner : String,
  th : () -> Unit raise ElabError,
) -> Unit raise ElabError {
  for x in unfold_attr_names.get(owner).unwrap_or([]) {
    check_unfoldable(empty_cxt(x.0), owner, x.1)
  }
  push_frame(owner, [owner, ..unfold_deps.get(owner).unwrap_or([])])
  let res : Result[Unit, ElabError] = try {
    th()
    Ok(())
  } catch {
    ElabError(p, m) => Err(ElabError(p, m))
  }
  let f = unfold_frames.pop().unwrap()
  // the functions made from the definition unfold what it unfolds
  let deps = [owner, ..unfold_deps.get(owner).unwrap_or([])]
  for h in f.helpers {
    unfold_deps.set(h, deps.filter(x => x != h))
  }
  match res {
    Ok(_) => ()
    Err(e) => raise e
  }
}

///|
/// Check a signature (or any other declaration) where nothing extra is
/// unfolded.
fn with_no_unfolding(th : () -> Unit raise ElabError) -> Unit raise ElabError {
  if unfold_modes.is_empty() && unfold_deps.is_empty() {
    return th()
  }
  push_frame("", [])
  let res : Result[Unit, ElabError] = try {
    th()
    Ok(())
  } catch {
    ElabError(p, m) => Err(ElabError(p, m))
  }
  ignore(unfold_frames.pop())
  match res {
    Ok(_) => ()
    Err(e) => raise e
  }
}

///|
/// `n` may be named in an unfolding by `owner`.
fn check_unfoldable(
  cxt : Cxt,
  owner : String,
  n : String,
) -> Unit raise ElabError {
  ensure(cxt, n)
  match globals.get(n) {
    Some({ kind: GFunc(_, _, _), .. }) => ()
    Some(_) => cxt.fail(n + " is not a function, so it cannot be unfolded")
    None => cxt.fail("unknown function " + n)
  }
  if unfold_modes.get(n) is Some(true) && n != owner {
    cxt.fail(n + " is #opaque(sealed): it cannot be unfolded")
  }
}

///|
/// `th` where `names` may be unfolded too (`unfold(f) { e }`, the `unfold`
/// tactic); the declaration being checked then unfolds them.
fn with_extra_unfolding(
  cxt : Cxt,
  names : Array[(Pos, String)],
  th : () -> (Tm, Val) raise ElabError,
) -> (Tm, Val) raise ElabError {
  let owner = match unfold_frames.last() {
    Some(f) => f.owner
    None => ""
  }
  for x in names {
    check_unfoldable(cxt.at(x.0), owner, x.1)
  }
  let ns = names.map(x => x.1)
  add_unfold_deps(owner, ns)
  let explicit = match unfold_frames.last() {
    Some(f) => [..f.explicit, ..ns]
    None => ns
  }
  push_frame(owner, explicit)
  let res : Result[(Tm, Val), ElabError] = Ok(th()) catch {
    ElabError(p, m) => Err(ElabError(p, m))
  }
  ignore(unfold_frames.pop())
  match res {
    Ok(r) => r
    Err(e) => raise e
  }
}

///|
/// The definition of `owner` unfolds `names` (for the rest of its check
/// too: the `unfold` tactic).
fn add_unfold_deps(owner : String, names : Array[String]) -> Unit {
  if owner == "" {
    return
  }
  for n in names {
    if n != owner && !unfold_deps.get(owner).unwrap_or([]).contains(n) {
      map_push(unfold_deps, owner, n)
    }
  }
}

///|
/// Let the rest of the current check unfold `names` (the `unfold` tactic).
fn extend_unfolding(names : Array[String]) -> Unit {
  match unfold_frames.last() {
    Some(f) => {
      add_unfold_deps(f.owner, names)
      let explicit = [..f.explicit, ..names]
      unfold_frames[unfold_frames.length() - 1] = {
        ..f,
        explicit,
        set: unfold_closure(explicit),
      }
    }
    None => ()
  }
}

///|
/// `th` in a copy of the current frame, which `extend_unfolding` may extend.
fn with_frame_copy(th : () -> Tm raise ElabError) -> Tm raise ElabError {
  match unfold_frames.last() {
    Some(f) => push_frame(f.owner, f.explicit)
    None => push_frame("", [])
  }
  let res : Result[Tm, ElabError] = Ok(th()) catch {
    ElabError(p, m) => Err(ElabError(p, m))
  }
  ignore(unfold_frames.pop())
  match res {
    Ok(r) => r
    Err(e) => raise e
  }
}

///|
/// A global function was given a body while checking a definition: it was
/// made from it (a local function, ...), and unfolds what it unfolds.
fn note_unfold_helper(name : String) -> Unit {
  let owner = match unfold_frames.last() {
    Some(f) => f.owner
    None => return
  }
  if owner == "" || name == owner {
    return
  }
  // the frame of the definition itself (`unfold` blocks push more)
  match unfold_frames.search_by(f => f.owner == owner) {
    Some(k) if !unfold_frames[k].helpers.contains(name) =>
      unfold_frames[k].helpers.push(name)
    _ => ()
  }
}

///|
/// A hint for an error, when opaque functions were not unfolded.
fn opaque_hint() -> String {
  if blocked_opaque.length() == 0 {
    return ""
  }
  let fs = blocked_opaque.join(", ")
  "\nhint: " +
  fs +
  (if blocked_opaque.length() == 1 { " is" } else { " are" }) +
  " opaque here; if the definition is needed, add #unfold(" +
  fs +
  ") to the declaration, or use unfold(" +
  fs +
  ") { … }"
}
