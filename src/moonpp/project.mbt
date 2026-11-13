///|
/// Projects: a MoonBit++ project is a MoonBit module (`moon.mod`, so that
/// `moon add` / `moon install` manage its dependencies) whose packages are
/// directories of `.mbtpp` files, each with an optional `moon.pkg` listing
/// the MoonBit packages it imports. The old JSON files are read too.
fn dir_of(path : String) -> String {
  let a = path.rev_find("/")
  let b = path.rev_find("\\")
  let k = match (a, b) {
    (Some(x), Some(y)) => if x > y { x } else { y }
    (Some(x), None) | (None, Some(x)) => x
    (None, None) => return "."
  }
  if k == 0 {
    "/"
  } else {
    path.unsafe_substring(start=0, end=k)
  }
}

///|
/// Fail with a message (unlike `fail`, without the location in moonpp).
fn[T] die(msg : String) -> T raise Failure {
  raise Failure(msg)
}

///|
fn parent_dir(dir : String) -> String? {
  let d = dir_of(dir)
  if d == dir || d == "" || d == "/" {
    None
  } else if d == "." {
    // `src` is in the current directory
    if dir == "." || dir == "./" {
      None
    } else {
      Some(".")
    }
  } else {
    Some(d)
  }
}

///|
fn last_segment(path : String) -> String {
  match path.rev_find("/") {
    Some(k) => path.unsafe_substring(start=k + 1, end=path.length())
    None => path
  }
}

///|
fn list_dir(dir : String) -> Array[String] {
  let names = (@fs.read_dir(dir) catch { _ => return [] }).to_owned()
  // dictionary order (`String::compare` puts shorter strings first)
  names.sort_by(dict_compare)
  names
}

///|
fn dict_compare(a : String, b : String) -> Int32 {
  let n = if a.length() < b.length() { a.length() } else { b.length() }
  for k = 0; k < n; k = k + 1 {
    let c = a.code_unit_at(k).compare(b.code_unit_at(k))
    if c != 0 {
      return c
    }
  }
  a.length().compare(b.length())
}

///|
fn is_dir(path : String) -> Bool {
  @fs.is_dir(path) catch {
    _ => false
  }
}

///|
fn read_json(path : String) -> Json? {
  if !@fs.path_exists(path) {
    return None
  }
  let text = @fs.read_file_to_string(path) catch { _ => return None }
  let j = @json.parse(text) catch { _ => return None }
  Some(j)
}

///|
/// The root of the project containing `dir`: the nearest directory with a
/// `moon.mod` (or `moon.mod.json`).
fn find_project(dir : String) -> String? {
  let mut d : String? = Some(dir)
  while d is Some(cur) {
    if is_module_dir(cur) {
      return Some(cur)
    }
    d = parent_dir(cur)
  }
  None
}

///|
/// The `.mbtpp` files of a package directory.
fn package_files(dir : String) -> Array[String] {
  list_dir(dir).filter(f => f.has_suffix(".mbtpp")).map(f => dir + "/" + f)
}

///|
/// The packages of a project: the directories (below its `source`
/// directory) that contain `.mbtpp` files.
fn project_packages(root : String) -> Array[String] {
  let src = module_source(root)
  let base = if src == "" { root } else { root + "/" + src }
  let out : Array[String] = []
  fn walk(dir : String, out : Array[String]) -> Unit {
    if package_files(dir).length() > 0 {
      out.push(dir)
    }
    for name in list_dir(dir) {
      if name.has_prefix(".") ||
        name.has_prefix("_") ||
        name == "target" ||
        name == "node_modules" {
        continue
      }
      let sub = dir + "/" + name
      if is_dir(sub) {
        walk(sub, out)
      }
    }
  }

  walk(base, out)
  out
}

///|
/// Is the package in `dir` a main package?
fn is_main_package(dir : String) -> Bool {
  package_is_main(dir)
}

///|
/// A path relative to `base`, for messages.
fn relative(path : String, base : String) -> String {
  if path.has_prefix(base + "/") {
    path.unsafe_substring(start=base.length() + 1, end=path.length())
  } else {
    path
  }
}

///|
let template_main : String =
  #|// A MoonBit++ program. `moonpp run` runs it, `moonpp check` type checks it.
  #|
  #|enum Vector[T] : Nat -> Type {
  #|  Nil : Vector[T](0)
  #|  Cons[n : Nat](T, Vector[T](n)) : Vector[T](S(n))
  #|}
  #|
  #|// T : Add is a trait annotation.
  #|fn[T : Add, n : Nat] Vector::sum(self : Vector[T](n), base : T) -> T {
  #|  match self {
  #|    Nil => base
  #|    Cons(x, xs) => x + xs.sum(base)
  #|  }
  #|}
  #|
  #|fn main {
  #|  let v : Vector[String](2) = Cons("Hello, ", Cons("MoonBit++", Nil))
  #|  println(v.sum(""))
  #|}
  #|

///|
/// `moonpp new <name>`: create a project directory.
fn new_project(name : String) -> Unit raise Failure {
  if @fs.path_exists(name) {
    die(name + " already exists")
  }
  let module_name = "username/" + last_segment(name)
  let files : Array[(String, String)] = [
    (
      "moon.mod",
      (
        $|name = "\{module_name}"
        $|
        $|version = "0.1.0"
        $|
        $|source = "src"
        $|
      ),
    ),
    (
      "src/main/moon.pkg",
      (
        #|import {
        #|}
        #|
        #|options(
        #|  "is-main": true,
        #|)
        #|
      ),
    ),
    ("src/main/main.mbtpp", template_main),
    (
      ".gitignore",
      (
        #|.mooncakes/
        #|_build/
        #|target/
        #|_mbtpp_build/
        #|mbtpp_out/
        #|
      ),
    ),
    (
      "README.md",
      (
        $|# \{last_segment(name)}
        $|
        $|A MoonBit++ project.
        $|
        $|```bash
        $|moonpp run                 # run src/main
        $|moonpp check               # type check all packages
        $|moonpp add <user/module>   # add a dependency from mooncakes.io
        $|```
        $|
        $|Imported MoonBit packages are listed in the `import` block of a
        $|package's `moon.pkg` and used as `@pkg.name`. `moonpp build`
        $|compiles the main package to a MoonBit project in `mbtpp_out/`.
        $|
      ),
    ),
  ]
  for f in files {
    let path = name + "/" + f.0
    let parts = f.0.split("/").map(s => s.to_owned()).to_array()
    let mut d = name
    @fs.create_dir(d) catch {
      _ => ()
    }
    for k = 0; k < parts.length() - 1; k = k + 1 {
      d = d + "/" + parts[k]
      @fs.create_dir(d) catch {
        _ => ()
      }
    }
    @fs.write_string_to_file(path, f.1) catch {
      @fs.IOError(msg) => die("cannot write " + path + ": " + msg)
    }
  }
}

///|
/// Is `dir` a package of a project: it has a `moon.pkg`, or it is in the
/// source directory of the project (as `moonpp check` finds packages)?
fn is_project_package(dir : String) -> Bool {
  if has_package_file(dir) {
    return true
  }
  match find_project(dir) {
    Some(root) => {
      let src = module_source(root)
      if src == "" {
        return false
      }
      let base = normalize_path(root + "/" + src)
      let d = normalize_path(dir)
      d == base || d.has_prefix(base + "/")
    }
    None => false
  }
}

///|
/// An absolute form of a path, for comparisons.
fn absolute_path(path : String) -> String {
  let p = path.replace_all(old="\\", new="/")
  let abs = p.has_prefix("/") || (p.length() > 1 && p.code_unit_at(1) == ':')
  let full = normalize_path(if abs { p } else { current_dir() + "/" + p })
  // a drive letter in either case
  if full.length() > 1 && full.code_unit_at(1) == ':' {
    full[:1].to_owned().to_lower() + full[1:].to_owned()
  } else {
    full
  }
}
