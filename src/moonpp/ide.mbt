///|
/// A number as JSON (`Int32::to_json` is not in every version of the core).
fn json_int(n : Int32) -> Json {
  Json::number(n.to_double())
}

///|
/// `moonpp ide <file> [--overlay <json>]`: check the package of a file for
/// an editor and print what the editor shows, as JSON:
///
/// - `diagnostics`: the error (if any) and the `#mbt` hints;
/// - `names`: the names used, with their types and definitions (hover, go
///   to definition);
/// - `proofs`: the goals of tactic blocks (info view);
/// - `symbols`: the declarations of the package (outline, symbol search).
///
/// The package is the directory of the file if it has a `moon.pkg`, else
/// the file alone. `--overlay` names a JSON file mapping paths to contents
/// that replace the files on disk (unsaved editor buffers).
fn cmd_ide(
  opts : Options,
  file : String,
  overlay : String?,
) -> Bool raise Failure {
  let file = normalize_path(file)
  let dir = dir_of(file)
  let files = if is_project_package(dir) {
    ordered_files(dir, package_files(dir).map(normalize_path))
  } else {
    [file]
  }
  let contents : Map[String, String] = {}
  match overlay {
    Some(o) => {
      let text = @fs.read_file_to_string(o) catch {
        @fs.IOError(msg) => die("cannot read " + o + ": " + msg)
      }
      let j = @json.parse(text) catch { _ => die("bad overlay " + o) }
      match j {
        Object(m) =>
          for k, v in m {
            if v is String(s) {
              contents.set(absolute_path(k), s)
            }
          }
        _ => die("bad overlay " + o)
      }
    }
    None => ()
  }
  let srcs = files.map(f => {
    let src = match contents.get(absolute_path(f)) {
      Some(s) => s
      None =>
        @fs.read_file_to_string(f) catch {
          @fs.IOError(msg) => die("cannot read " + f + ": " + msg)
        }
    }
    (f, src)
  })
  let diags : Array[Json] = []
  let imports = load_imports(dir) catch {
    Failure(msg) => {
      diags.push(diag(file, 1, 1, "error", msg))
      []
    }
  }
  let mut ok = true
  @tt.check_package(srcs, prelude=opts.prelude, imports~) catch {
    @tt.CheckError(msg) => {
      ok = false
      match @tt.last_error {
        [(p, m), ..] => {
          let (k, line) = @tt.split_pos(p)
          if k >= 0 && k < files.length() {
            diags.push(diag(files[k], line, p.col, "error", m))
          } else {
            diags.push(diag(file, 1, 1, "error", m))
          }
        }
        [] => diags.push(diag(file, 1, 1, "error", msg))
      }
    }
  }
  if ok {
    for h in mbt_hints(imports) {
      diags.push(
        Json::object({
          "file": Json::string(h.file),
          "line": json_int(h.line),
          "col": json_int(1),
          "severity": Json::string("hint"),
          "message": Json::string(
            "pub " + h.kind + " " + h.name + " could be #mbt",
          ),
          "mbt": Json::string(h.name),
        }),
      )
    }
  }
  let loc = (p : @tt.Pos) => {
    let (k, line) = @tt.split_pos(p)
    if k >= 0 && k < files.length() {
      Some((files[k], line, p.col))
    } else {
      None
    }
  }
  let names : Array[Json] = []
  for n in @tt.name_infos {
    guard loc(n.pos) is Some((f, line, col)) else { continue }
    let m : Map[String, Json] = {
      "file": Json::string(f),
      "line": json_int(line),
      "col": json_int(col),
      "len": json_int(n.name.length()),
      "type": Json::string((n.show)()),
    }
    match n.global.bind(g => @tt.decl_pos.get(g)).bind(loc) {
      Some((df, dl, dc)) =>
        m.set(
          "def",
          Json::object({
            "file": Json::string(df),
            "line": json_int(dl),
            "col": json_int(dc),
          }),
        )
      None => ()
    }
    names.push(Json::object(m))
  }
  let goal_json = (gs : Array[@tt.GoalInfo]) => {
    Json::array(
      gs.map(g => {
        Json::object({
          "hyps": Json::array(g.hyps.map(Json::string(_))),
          "goal": Json::string(g.goal),
        })
      }),
    )
  }
  let proofs : Array[Json] = []
  for pr in @tt.proof_infos {
    guard loc(pr.pos) is Some((f, line, col)) else { continue }
    let tactics = pr.tactics.map(t => {
      let (tl, tc) = match loc(t.0) {
        Some((_, l, c)) => (l, c)
        None => (0, 0)
      }
      Json::object({
        "line": json_int(tl),
        "col": json_int(tc),
        "goals": match t.1 {
          Some(gs) => goal_json(gs)
          None => Json::null()
        },
      })
    })
    proofs.push(
      Json::object({
        "file": Json::string(f),
        "line": json_int(line),
        "col": json_int(col),
        "start": goal_json(pr.start),
        "tactics": Json::array(tactics),
      }),
    )
  }
  let symbols : Array[Json] = []
  for name, p in @tt.decl_pos {
    guard loc(p) is Some((f, line, col)) else { continue }
    symbols.push(
      Json::object({
        "name": Json::string(name),
        "kind": Json::string(@tt.decl_kinds.get(name).unwrap_or("fn")),
        "file": Json::string(f),
        "line": json_int(line),
        "col": json_int(col),
      }),
    )
  }
  println(
    Json::object({
      "files": Json::array(files.map(Json::string(_))),
      "symbols": Json::array(symbols),
      "diagnostics": Json::array(diags),
      "names": Json::array(names),
      "proofs": Json::array(proofs),
    }).stringify(),
  )
  true
}

///|
fn diag(
  file : String,
  line : Int32,
  col : Int32,
  severity : String,
  message : String,
) -> Json {
  Json::object({
    "file": Json::string(file),
    "line": json_int(line),
    "col": json_int(col),
    "severity": Json::string(severity),
    "message": Json::string(message),
  })
}
