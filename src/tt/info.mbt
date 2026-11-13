///|
/// Information for editors, recorded while checking the files of a package
/// (positions of the prelude and of imports are not recorded): the types of
/// the names used (hover), where the globals they refer to are defined (go
/// to definition), and the goals of tactic blocks (info view). Types are
/// shown at the end of the check, when the metas are solved.
pub(all) struct NameInfo {
  pos : Pos
  /// The name as written.
  name : String
  /// The global it refers to (`None`: a local variable).
  global : String?
  /// `x : T`, shown on demand.
  show : () -> String
}

///|
pub(all) struct GoalInfo {
  /// `x : A` lines, then the goal.
  hyps : Array[String]
  goal : String
}

///|
/// A tactic block: the goals at its start, and after each tactic (`None`:
/// the tactic failed).
pub(all) struct ProofInfo {
  pos : Pos
  start : Array[GoalInfo]
  tactics : Array[(Pos, Array[GoalInfo]?)]
}

///|
pub let name_infos : Array[NameInfo] = @percheck.array()

///|
pub let proof_infos : Array[ProofInfo] = @percheck.array()

///|
/// Where the globals of the package are declared.
pub let decl_pos : Map[String, Pos] = @percheck.map()

///|
/// What the globals of `decl_pos` are: "fn", "lemma", "let", "enum",
/// "struct", "trait", "type", "constructor", "field" or "method" (of a
/// trait).
pub let decl_kinds : Map[String, String] = @percheck.map()

///|
/// Only the files of the checked package are recorded.
fn in_package(p : Pos) -> Bool {
  p.line >= file_stride
}

///|
fn record_name(
  p : Pos,
  x : String,
  global : String?,
  show : () -> String,
) -> Unit {
  if in_package(p) && !derived_lines.contains(p.line) {
    name_infos.push({ pos: p, name: x, global, show, })
  }
}

///|
fn record_global(p : Pos, x : String, n : String) -> Unit {
  record_name(p, x, Some(n), () => {
    n + " : " + show_global_type(n).unwrap_or("?")
  })
}

///|
/// The type of local `l` of `cxt`, in its own context.
fn local_type(cxt : Cxt, l : Int32) -> String {
  show_tm(cxt.names[0:l].to_owned(), quote(l, cxt.types[l]))
}

///|
fn goal_info(cxt : Cxt, ty : Val) -> GoalInfo {
  let hyps : Array[String] = []
  for l = 0; l < cxt.lvl; l = l + 1 {
    let x = cxt.names[l]
    if x == "_" || x.contains("$") {
      continue
    }
    hyps.push(x + " : " + local_type(cxt, l))
  }
  { hyps, goal: cxt.show(ty), }
}

///|
/// The file (index into `source_files`) and line of a position.
pub fn split_pos(p : Pos) -> (Int32, Int32) {
  (p.line / file_stride - 1, p.line % file_stride)
}
