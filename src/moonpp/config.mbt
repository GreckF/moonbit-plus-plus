///|
/// Reading the configuration of modules, packages and workspaces, in the new
/// syntax (`moon.mod`, `moon.pkg`, `moon.work`, see moonfile.mbt) or the
/// old JSON files (`moon.mod.json`, `moon.pkg.json`).

///|
priv struct ModInfo {
  name : String?
  version : String?
  /// The `source` directory (`""` for the module root).
  source : String
  /// Dependencies from mooncakes.io, as `name@version` (or `name`).
  deps : Array[String]
  /// Local dependencies of an old `moon.mod.json`: (name, directory).
  local_deps : Array[(String, String)]
}

///|
/// Is `dir` a MoonBit module?
fn is_module_dir(dir : String) -> Bool {
  @fs.path_exists(dir + "/moon.mod") || @fs.path_exists(dir + "/moon.mod.json")
}

///|
/// Is `path` absolute (`/x`, `C:/x`, `C:\x`)?
fn is_absolute(path : String) -> Bool {
  path.has_prefix("/") || path.has_prefix("\\") || path.contains(":")
}

///|
fn join_path(dir : String, path : String) -> String {
  normalize_path(if is_absolute(path) { path } else { dir + "/" + path })
}

///|
/// Forward slashes, without `.` and `x/..` segments.
fn normalize_path(path : String) -> String {
  let parts : Array[String] = []
  for seg in path.replace_all(old="\\", new="/").split("/") {
    let s = seg.to_owned()
    if s == "." || (s == "" && parts.length() > 0) {
      continue
    }
    if s == ".." && parts.length() > 0 && parts[parts.length() - 1] != ".." {
      ignore(parts.pop())
    } else {
      parts.push(s)
    }
  }
  parts.join("/")
}

///|
fn module_info(dir : String) -> ModInfo raise Failure {
  match read_moon_file(dir + "/moon.mod") {
    Some(f) =>
      return {
        name: f.string_field("name"),
        version: f.string_field("version"),
        source: f.string_field("source").unwrap_or(""),
        deps: f.imports.filter(i => i.kind is None).map(i => i.path),
        local_deps: [],
      }
    None => ()
  }
  let j = match read_json(dir + "/moon.mod.json") {
    Some(j) => j
    None =>
      return {
        name: None,
        version: None,
        source: "",
        deps: [],
        local_deps: [],
      }
  }
  let str = (k : String) => {
    match (if j is Object(obj) { obj.get(k) } else { None }) {
      Some(String(s)) => Some(s)
      _ => None
    }
  }
  let deps : Array[String] = []
  let local_deps : Array[(String, String)] = []
  match (if j is Object(obj) { obj.get("deps") } else { None }) {
    Some(Object(ds)) =>
      for name, spec in ds {
        match spec {
          String(v) => deps.push(name + "@" + v)
          Object(o) =>
            match (o.get("path"), o.get("version")) {
              (Some(String(p)), _) => local_deps.push((name, join_path(dir, p)))
              (_, Some(String(v))) => deps.push(name + "@" + v)
              _ => deps.push(name)
            }
          _ => ()
        }
      }
    _ => ()
  }
  {
    name: str("name"),
    version: str("version"),
    source: str("source").unwrap_or(""),
    deps,
    local_deps,
  }
}

///|
/// The `source` directory of a MoonBit module (`""` for the module root).
fn module_source(dir : String) -> String {
  (module_info(dir) catch { _ => return "" }).source
}

///|
/// The packages a package imports (path, alias), not counting test imports.
fn package_imports(dir : String) -> Array[(String, String)] raise Failure {
  match read_moon_file(dir + "/moon.pkg") {
    Some(f) =>
      return f.imports
        .filter(i => i.kind is None)
        .map(i => (i.path, i.pkg_alias.unwrap_or(last_segment(i.path))))
    None => ()
  }
  let cfg = dir + "/moon.pkg.json"
  if !@fs.path_exists(cfg) {
    return []
  }
  let json = match read_json(cfg) {
    Some(j) => j
    None => die(cfg + ": invalid JSON")
  }
  let entries = match (if json is Object(obj) { obj.get("import") } else { None }) {
    Some(Array(xs)) => xs
    Some(_) => die(cfg + ": \"import\" must be an array")
    None => []
  }
  entries.map(e => {
    match e {
      String(p) => (p, last_segment(p))
      Object(o) =>
        match (o.get("path"), o.get("alias")) {
          (Some(String(p)), Some(String(a))) => (p, a)
          (Some(String(p)), None) => (p, last_segment(p))
          _ => die(cfg + ": an import needs a \"path\"")
        }
      _ => die(cfg + ": invalid import entry")
    }
  })
}

///|
/// The order in which the files of a package are checked, if the package
/// gives one: `options("mbtpp-order": [ "b.mbtpp", "a.mbtpp" ])` in its
/// `moon.pkg` (or `"mbtpp-order"` in a `moon.pkg.json`).
fn package_order(dir : String) -> Array[String]? raise Failure {
  match read_moon_file(dir + "/moon.pkg") {
    Some(f) =>
      return match f.option("mbtpp-order") {
        Some(MList(xs)) =>
          Some(
            xs.map(x => {
              match x {
                MStr(s) => s
                _ => die(dir + "/moon.pkg: \"mbtpp-order\" lists file names")
              }
            }),
          )
        Some(_) => die(dir + "/moon.pkg: \"mbtpp-order\" must be a list")
        None => None
      }
    None => ()
  }
  match read_json(dir + "/moon.pkg.json") {
    Some(j) =>
      match (if j is Object(obj) { obj.get("mbtpp-order") } else { None }) {
        Some(Array(xs)) =>
          Some(
            xs.map(x => {
              match x {
                String(s) => s
                _ =>
                  die(dir + "/moon.pkg.json: \"mbtpp-order\" lists file names")
              }
            }),
          )
        Some(_) => die(dir + "/moon.pkg.json: \"mbtpp-order\" must be a list")
        None => None
      }
    None => None
  }
}

///|
/// The files of a package in the order they are checked: those listed in
/// `"mbtpp-order"` first, in that order, then the others in dictionary
/// order.
fn ordered_files(
  dir : String,
  files : Array[String],
) -> Array[String] raise Failure {
  let order = match package_order(dir) {
    Some(o) => o
    None => return files
  }
  let out : Array[String] = []
  for name in order {
    match files.search_by(f => last_segment(f) == name) {
      Some(i) => if !out.contains(files[i]) { out.push(files[i]) }
      None =>
        die(
          relative(dir, current_dir()) +
          "/moon.pkg: \"mbtpp-order\" lists " +
          name +
          ", which is not a file of the package",
        )
    }
  }
  for f in files {
    if !out.contains(f) {
      out.push(f)
    }
  }
  out
}

///|
/// Is the package in `dir` a main package (`"is-main": true`)?
fn package_is_main(dir : String) -> Bool {
  match (read_moon_file(dir + "/moon.pkg") catch { _ => None }) {
    Some(f) =>
      // `options("is-main": true)`, or `pkgtype(kind: "executable")` in
      // newer versions
      return f.option("is-main") is Some(MAtom("true")) ||
        f.call_arg("pkgtype", "kind") is Some(MStr("executable"))
    None => ()
  }
  match read_json(dir + "/moon.pkg.json") {
    Some(j) =>
      (if j is Object(obj) { obj.get("is-main") } else { None }) is Some(Json::True)
    None => false
  }
}

///|
/// Is `dir` a package (it has a `moon.pkg` or `moon.pkg.json`)?
fn has_package_file(dir : String) -> Bool {
  @fs.path_exists(dir + "/moon.pkg") || @fs.path_exists(dir + "/moon.pkg.json")
}

///|
/// The modules of the workspace containing `dir` (the members of the nearest
/// `moon.work` above it), as directories.
fn workspace_members(dir : String) -> Array[String] {
  let mut d : String? = Some(dir)
  while d is Some(cur) {
    match (read_moon_file(cur + "/moon.work") catch { _ => None }) {
      Some(f) =>
        return match f.fields.get("members") {
          Some(MList(ms)) =>
            ms.filter_map(m => {
              match m {
                MStr(p) => Some(join_path(cur, p))
                _ => None
              }
            })
          _ => []
        }
      None => ()
    }
    d = parent_dir(cur)
  }
  []
}

///|
/// The directory of package `pkg` in a local module: a member of the
/// workspace, or a local dependency of an old `moon.mod.json`.
fn local_package_dir(pkg : String, dir : String) -> String? {
  let mods : Array[String] = workspace_members(dir)
  match find_project(dir) {
    Some(root) =>
      for ld in (module_info(root) catch { _ => return None }).local_deps {
        mods.push(ld.1)
      }
    None => ()
  }
  for m in mods {
    let info = module_info(m) catch { _ => continue }
    match info.name {
      Some(name) if pkg == name || pkg.has_prefix(name + "/") => {
        let base = if info.source == "" { m } else { m + "/" + info.source }
        return Some(
          if pkg == name {
            base
          } else {
            base + pkg.unsafe_substring(start=name.length(), end=pkg.length())
          },
        )
      }
      _ => ()
    }
  }
  None
}
