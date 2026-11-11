///|
/// `moonpp`: the MoonBit++ build tool, modelled on `moon`.
let help_msg : String =
  #|moonpp: the MoonBit++ build tool
  #|
  #|usage:
  #|  moonpp new <name>          create a new project
  #|  moonpp check [path]        type check the project (or a package directory or file);
  #|                             also lists the `pub` declarations that could be #mbt
  #|  moonpp fix [path]          add #mbt to the `pub` declarations that could have it
  #|  moonpp ide <file> [--overlay <json>]  check for an editor: errors, types and goals as JSON
  #|  moonpp run [path]          run the main package (or a package directory or file)
  #|  moonpp test [path]         run the `test` blocks (with the interpreter)
  #|  moonpp build [path]        compile to a MoonBit project and `moon build` it: by default
  #|                             mbtpp_out/<pkg> in the project (or _mbtpp_build/<file> for a
  #|                             single file), with the dependencies of the project
  #|  moonpp run --compiled [path] [-- args]  compile to MoonBit and run it with
  #|                             `moon run`, passing `args` to the program
  #|  moonpp add <user/module>   add a dependency (`moon add`) and extract its interfaces
  #|  moonpp remove <module>     remove a dependency (`moon remove`)
  #|  moonpp install             install the dependencies (`moon install`) and extract interfaces
  #|  moonpp tree                show the dependency tree (`moon tree`)
  #|  moonpp interfaces          generate missing interfaces of downloaded dependencies
  #|                             (done automatically by `add` and `install`)
  #|  moonpp version
  #|
  #|options:
  #|  --no-prelude   do not load the prelude
  #|  --verbose      list the interface items that could not be imported, and
  #|                 (build, run --compiled) the functions without a native version
  #|  --compiled     (run) run the program compiled to MoonBit instead of interpreting it
  #|  -o, --output <dir>  (build, run --compiled) where to generate the MoonBit project
  #|
  #|A package is a directory of .mbtpp files. The MoonBit packages it uses are
  #|listed in the `import` block of its moon.pkg (or the "import" field of a
  #|moon.pkg.json) and referred to as @pkg.name; imported functions are type
  #|checked by the interpreter, and called by the compiled program.

///|
let version : String = "moonpp 0.7.1"

///|
/// Line-buffered output.
struct Out {
  buf : StringBuilder
}

///|
fn Out::write(self : Out, s : String) -> Unit {
  for c in s {
    if c == '\n' {
      println(self.buf.to_string())
      self.buf.reset()
    } else {
      self.buf.write_char(c)
    }
  }
}

///|
fn Out::flush(self : Out) -> Unit {
  if self.buf.to_string() != "" {
    println(self.buf.to_string())
    self.buf.reset()
  }
}

///|
struct Options {
  prelude : Bool
  verbose : Bool
  compiled : Bool
  /// The directory of the generated MoonBit project.
  output : String?
  /// The arguments after `--`, for the program (`run --compiled`).
  args : Array[String]
}

///|
/// Read the files of a package (or a single file) and type check them.
fn check_files(
  opts : Options,
  dir : String,
  files : Array[String],
) -> Array[@tt.Import] raise Failure {
  let srcs : Array[(String, String)] = []
  let cwd = current_dir()
  for f in ordered_files(dir, files) {
    let src = @fs.read_file_to_string(f) catch {
      @fs.IOError(msg) => die("cannot read " + f + ": " + msg)
    }
    srcs.push((relative(f, cwd), src))
  }
  let imports = load_imports(dir)
  @tt.check_package(srcs, prelude=opts.prelude, imports~) catch {
    @tt.CheckError(msg) => die(msg)
  }
  if opts.verbose && @tt.import_skipped.length() > 0 {
    println("not imported:")
    for s in @tt.import_skipped {
      println("  " + s)
    }
  }
  imports
}

///|
/// The `pub` declarations of the package just checked that could be `#mbt`.
fn mbt_hints(imports : Array[@tt.Import]) -> Array[@tt.MbtHint] {
  let aliases = imports.map(i => (i.path, i.alias))
  @tt.mbt_hints(names => @codegen.native_fns(aliases, names))
}

///|
fn show_hint(h : @tt.MbtHint) -> String {
  h.file +
  ":" +
  h.line.to_string() +
  ": hint: pub " +
  h.kind +
  " " +
  h.name +
  " could be #mbt (" +
  (match h.kind {
    "fn" => "it would be exported as a MoonBit function"
    "trait" => "it would be a MoonBit trait"
    _ => "it would be a MoonBit type"
  }) +
  ")"
}

///|
/// What a path argument designates: a single file, or packages.
fn targets(
  path : String?,
) -> (String, Array[(String, Array[String])]) raise Failure {
  let cwd = current_dir()
  match path {
    Some(p) if p.has_suffix(".mbtpp") => {
      if !@fs.path_exists(p) {
        die("no such file: " + p)
      }
      (cwd, [(dir_of(p), [p])])
    }
    Some(p) if package_files(p).length() > 0 => (cwd, [(p, package_files(p))])
    _ => {
      let start = path.unwrap_or(cwd)
      let root = match find_project(start) {
        Some(r) => r
        None =>
          die(
            "not in a MoonBit++ project (no moon.mod found); try `moonpp new`",
          )
      }
      let pkgs = project_packages(root)
      if pkgs.length() == 0 {
        die("the project has no .mbtpp files")
      }
      (root, pkgs.map(d => (d, package_files(d))))
    }
  }
}

///|
fn cmd_check(opts : Options, path : String?) -> Bool raise Failure {
  let (base, pkgs) = targets(path)
  let mut ok = true
  for pkg in pkgs {
    let (dir, files) = pkg
    let name = relative(dir, base)
    let imports = check_files(opts, dir, files) catch {
      Failure(msg) => {
        println(msg)
        ok = false
        continue
      }
    }
    let hints = mbt_hints(imports)
    for h in hints {
      println(show_hint(h))
    }
    if hints.length() > 0 {
      println("  (`moonpp fix` adds #mbt to them)")
    }
    println(
      "ok: " +
      (if files.length() == 1 && path is Some(_) { files[0] } else { name }),
    )
  }
  ok
}

///|
/// Add `#mbt` to the `pub` declarations that could have it, on a line of its
/// own above the declaration. The package is checked again afterwards; if
/// that fails, the files are restored.
fn cmd_fix(opts : Options, path : String?) -> Bool raise Failure {
  let (_, pkgs) = targets(path)
  let mut count = 0
  for pkg in pkgs {
    let (dir, files) = pkg
    let hints = mbt_hints(check_files(opts, dir, files))
    let originals : Array[(String, String)] = []
    for
      file in hints
      .map(h => h.file)
      .iter()
      .fold(init=[], (acc : Array[String], f) => {
        if !acc.contains(f) {
          acc.push(f)
        }
        acc
      }) {
      let src = @fs.read_file_to_string(file) catch {
        @fs.IOError(msg) => die("cannot read " + file + ": " + msg)
      }
      originals.push((file, src))
      let nl = if src.contains("\r\n") { "\r\n" } else { "\n" }
      let lines = src.split(nl).map(l => l.to_string()).to_array()
      // from the bottom, so that the line numbers stay valid
      let lns = hints.filter(h => h.file == file).map(h => h.line)
      lns.sort()
      lns.rev_in_place()
      for ln in lns {
        let line = lines[ln - 1]
        let mut k = 0
        while k < line.length() && (line[k] == ' ' || line[k] == '\t') {
          k = k + 1
        }
        lines.insert(ln - 1, line.unsafe_substring(start=0, end=k) + "#mbt")
      }
      write_file(file, lines.join(nl))
    }
    let restore = () => {
      for o in originals {
        write_file(o.0, o.1) catch {
          _ => ()
        }
      }
    }
    ignore(check_files(opts, dir, files)) catch {
      Failure(msg) => {
        restore()
        die("adding #mbt broke the package (the files are restored): " + msg)
      }
    }
    for h in hints {
      println(h.file + ":" + h.line.to_string() + ": #mbt " + h.name)
    }
    count = count + hints.length()
  }
  if count == 0 {
    println("nothing to fix")
  }
  true
}

///|
/// The package to run or build.
fn main_package(path : String?) -> (String, Array[String]) raise Failure {
  let (_, pkgs) = targets(path)
  if pkgs.length() == 1 {
    pkgs[0]
  } else {
    match pkgs.iter().find_first(p => is_main_package(p.0)) {
      Some(p) => p
      None =>
        die(
          "no main package; mark one with options(\"is-main\": true) in its moon.pkg",
        )
    }
  }
}

///|
fn write_file(path : String, content : String) -> Unit raise Failure {
  @fs.write_string_to_file(path, content) catch {
    @fs.IOError(msg) => die("cannot write " + path + ": " + msg)
  }
}

///|
fn make_dirs(path : String) -> Unit {
  let parts = path.split("/").map(s => s.to_string()).to_array()
  let mut d = ""
  for p in parts {
    d = if d == "" { p } else { d + "/" + p }
    if d != "" && d != "." && !@fs.path_exists(d) {
      @fs.create_dir(d) catch {
        _ => ()
      }
    }
  }
}

///|
/// The configuration files of the generated project (`moon.mod`,
/// `moon.work`): the name, version and dependencies of the MoonBit++ project
/// (`root`, if any). Local modules (workspace members, or local dependencies
/// of an old `moon.mod.json`) are members of the generated workspace, by
/// absolute path.
fn output_module(
  root : String?,
  default_name : String,
) -> (String, String) raise Failure {
  let info = match root {
    Some(r) => module_info(r)
    None => { name: None, version: None, source: "", deps: [], local_deps: [], }
  }
  let deps = info.deps.copy()
  let members : Array[String] = []
  match root {
    Some(r) => {
      for m in workspace_members(r) {
        if normalize_path(m) != normalize_path(r) && is_module_dir(m) {
          members.push(m)
        }
      }
      for ld in info.local_deps {
        members.push(normalize_path(ld.1))
        let v = (module_info(ld.1) catch { _ => info }).version
        deps.push(
          match v {
            Some(v) if is_module_dir(ld.1) => ld.0 + "@" + v
            _ => ld.0
          },
        )
      }
    }
    None => ()
  }
  let m = StringBuilder::new()
  m.write_string("name = " + mstr(info.name.unwrap_or(default_name)) + "\n\n")
  m.write_string("version = " + mstr(info.version.unwrap_or("0.1.0")) + "\n")
  if deps.length() > 0 {
    m.write_string("\nimport {\n")
    for d in deps {
      m.write_string("  " + mstr(d) + ",\n")
    }
    m.write_string("}\n")
  }
  // the generated project is a workspace of its own (also so that a
  // `moon.work` of the MoonBit++ project does not apply to it)
  let w = StringBuilder::new()
  w.write_string("members = [\n  \".\",\n")
  for mem in members {
    w.write_string("  " + mstr(mem) + ",\n")
  }
  w.write_string("]\n")
  (m.to_string(), w.to_string())
}

///|
/// Compile a package (or file) to a MoonBit project. Returns the project
/// directory and the name of the generated package in it.
fn compile(opts : Options, path : String?) -> (String, String) raise Failure {
  let (dir, files) = main_package(path)
  ignore(check_files(opts, dir, files))
  let imports = load_imports(dir)
  let code = @codegen.generate_files(imports.map(i => (i.path, i.alias))) catch {
    @codegen.CodegenError(msg) => die("cannot compile: " + msg)
  }
  for w in @codegen.warnings {
    println("warning: " + w)
  }
  if opts.verbose {
    let report = @codegen.native_report(imports.map(i => (i.path, i.alias)))
    if report.length() > 0 {
      println(
        "without a native version (they run in the uniform representation):",
      )
      for r in report {
        println("  " + r.0 + ": " + r.1)
      }
    }
  }
  let single = match path {
    Some(p) => p.has_suffix(".mbtpp")
    None => false
  }
  let project = if single { None } else { find_project(dir) }
  let (out, pkg, default_name) = match project {
    Some(root) => {
      let pkg = last_segment(dir)
      // generated by older versions of moonpp, inside the project's module
      let old = (if module_source(root) == "" {
          root
        } else {
          root + "/" + module_source(root)
        }) +
        "/mbtpp_out"
      if @fs.path_exists(old) {
        println(
          "note: " +
          relative(old, current_dir()) +
          " was generated by an older moonpp and can be deleted",
        )
      }
      (root + "/mbtpp_out/" + pkg, pkg, "mbtpp/" + pkg)
    }
    None => {
      let stem = last_segment(files[0]).replace(old=".mbtpp", new="")
      (dir_of(files[0]) + "/_mbtpp_build/" + stem, "main", "mbtpp/" + stem)
    }
  }
  let out = opts.output.unwrap_or(out)
  make_dirs(out + "/" + pkg)
  let (mod_file, work_file) = output_module(project, default_name)
  // files of older versions of moonpp
  for old in ["/moon.mod.json", "/" + pkg + "/moon.pkg.json"] {
    if @fs.path_exists(out + old) {
      @fs.remove_file(out + old) catch {
        _ => ()
      }
    }
  }
  write_file(out + "/moon.mod", mod_file)
  write_file(out + "/moon.work", work_file)
  write_file(
    out + "/.gitignore",
    (
      #|_build/
      #|target/
      #|.mooncakes/
      #|moon.work.lock
      #|
    ),
  )
  // the JS backend produces ES modules: `node main.js` needs this
  write_file(out + "/package.json", "{ \"type\": \"module\" }\n")
  let source = match project {
    Some(root) => relative(dir, root)
    None => files[0]
  }
  write_file(
    out + "/README.md",
    (
      $|# MoonBit code generated from MoonBit++
      $|
      $|Generated by `moonpp build` from `\{source}`; it is overwritten by the
      $|next build. A standalone MoonBit project:
      $|
      $|```bash
      $|moon run \{pkg}
      $|moon build
      $|```
      $|
      $|Each `.mbtpp` file of the package is compiled to the `.mbt` file of the
      $|same name in `\{pkg}/`; `mbtpp_prelude.mbt` has the prelude, `mbtpp_imports.mbt`
      $|the glue for imported MoonBit packages and `mbtpp_runtime.mbt` the runtime.
      $|
    ),
  )
  let pkg_file = StringBuilder::new()
  pkg_file.write_string("warnings = \"-a\"\n")
  // the runtime uses the conversions of `Float` (moonbitlang/core/float)
  pkg_file.write_string("\nimport {\n  \"moonbitlang/core/float\",\n")
  for i in imports {
    pkg_file.write_string("  " + mstr(i.path) + " @" + i.alias + ",\n")
  }
  pkg_file.write_string("}\n")
  pkg_file.write_string("\noptions(\n  \"is-main\": true,\n)\n")
  write_file(out + "/" + pkg + "/moon.pkg", pkg_file.to_string())
  let pkg_dir = out + "/" + pkg
  let written = code.map(f => f.0)
  written.push(@codegen.runtime_file_name())
  // files of an earlier build that are not generated any more
  for f in list_dir(pkg_dir) {
    if f.has_suffix(".mbt") && !written.contains(f) {
      let text = @fs.read_file_to_string(pkg_dir + "/" + f) catch { _ => "" }
      if text.has_prefix("// Generated by moonpp") {
        @fs.remove_file(pkg_dir + "/" + f) catch {
          _ => ()
        }
      }
    }
  }
  for f in code {
    write_file(pkg_dir + "/" + f.0, f.1)
  }
  write_file(
    pkg_dir + "/" + @codegen.runtime_file_name(),
    @codegen.runtime_code(),
  )
  // format the generated code (best effort)
  if can_run_commands {
    ignore(run_quiet("moon fmt", out))
  }
  (out, pkg)
}

///|
/// A command line argument for the shell (`sh` or `cmd`), quoted when
/// needed.
fn shell_arg(a : String) -> String {
  if a != "" &&
    a
    .iter()
    .all(c => {
      (c >= 'a' && c <= 'z') ||
      (c >= 'A' && c <= 'Z') ||
      (c >= '0' && c <= '9') ||
      c is ('-' | '_' | '.' | '/' | ':' | '=' | ',' | '+')
    }) {
    return a
  }
  "\"" +
  a.replace_all(old="\\", new="\\\\").replace_all(old="\"", new="\\\"") +
  "\""
}

///|
fn cmd_build(opts : Options, path : String?) -> Bool raise Failure {
  let (out, pkg) = compile(opts, path)
  moon("build", out)
  println(
    "compiled to the MoonBit project " +
    relative(out, current_dir()) +
    " (run it there with `moon run " +
    pkg +
    "`)",
  )
  true
}

///|
fn cmd_run(opts : Options, path : String?) -> Bool raise Failure {
  if opts.compiled {
    let (mod_dir, pkg) = compile(opts, path)
    let args = if opts.args.is_empty() {
      ""
    } else {
      " -- " + opts.args.map(shell_arg).join(" ")
    }
    moon("run -q " + pkg + args, mod_dir)
    return true
  }
  if !opts.args.is_empty() {
    die(
      "arguments after `--` are passed to compiled programs: use `moonpp run --compiled`",
    )
  }
  let (base, pkgs) = targets(path)
  let (dir, files) = if pkgs.length() == 1 {
    pkgs[0]
  } else {
    match pkgs.iter().find_first(p => is_main_package(p.0)) {
      Some(p) => p
      None =>
        die(
          "no main package; mark one with options(\"is-main\": true) in its moon.pkg",
        )
    }
  }
  ignore(base)
  ignore(check_files(opts, dir, files))
  let out = { buf: StringBuilder::new(), }
  @interp.run_main(s => out.write(s)) catch {
    @interp.RunError(msg) => {
      out.flush()
      println(msg)
      return false
    }
  }
  out.flush()
  true
}

///|
/// Run the `test` blocks of the packages (with the interpreter).
fn cmd_test(opts : Options, path : String?) -> Bool raise Failure {
  let (_, pkgs) = targets(path)
  let mut passed = 0
  let mut failed = 0
  for pkg in pkgs {
    let (dir, files) = pkg
    ignore(check_files(opts, dir, files))
    for name, display in @parser.test_names {
      if !@tt.globals.contains(name) {
        continue
      }
      let out = { buf: StringBuilder::new(), }
      let label = if display == "" { name } else { display }
      let ok = try {
        @interp.run_global(name, s => out.write(s))
        true
      } catch {
        @interp.RunError(msg) => {
          out.flush()
          println("test " + label.escape() + " failed: " + msg)
          false
        }
      }
      if ok {
        out.flush()
        passed = passed + 1
      } else {
        failed = failed + 1
      }
    }
    @parser.test_names.clear()
  }
  println(
    "Total tests: " +
    (passed + failed).to_string() +
    ", passed: " +
    passed.to_string() +
    ", failed: " +
    failed.to_string() +
    ".",
  )
  failed == 0
}

///|
/// Run a `moon` command in the project, failing if it fails.
fn moon(args : String, dir : String) -> Unit raise Failure {
  if !can_run_commands {
    die("this build of moonpp cannot run `moon`; use the JS build (bin/moonpp)")
  }
  let status = run_command("moon " + args, dir)
  if status != 0 {
    let hint = match find_project(dir) {
      Some(root) if !@fs.path_exists(root + "/moon.mod") =>
        "\nhint: the project uses moon.mod.json, which newer versions of moon no longer accept; run `moon fmt` in " +
        root +
        " to migrate it to moon.mod (moonpp reads both)"
      _ => ""
    }
    die(
      "`moon " +
      args +
      "` failed (exit status " +
      status.to_string() +
      ")" +
      hint,
    )
  }
}

///|
/// Make sure every package of the downloaded dependencies has an interface
/// file, generating the missing ones with `moon info`.
fn extract_interfaces(root : String) -> Unit raise Failure {
  let cakes = root + "/.mooncakes"
  for user in list_dir(cakes) {
    for m in list_dir(cakes + "/" + user) {
      let mod_dir = cakes + "/" + user + "/" + m
      if !is_module_dir(mod_dir) {
        continue
      }
      let src = module_source(mod_dir)
      let base = if src == "" { mod_dir } else { mod_dir + "/" + src }
      let missing : Array[String] = []
      fn walk(dir : String, missing : Array[String]) -> Unit {
        let is_pkg = @fs.path_exists(dir + "/moon.pkg.json") ||
          @fs.path_exists(dir + "/moon.pkg")
        if is_pkg && mbti_in(dir) is None {
          missing.push(dir)
        }
        for name in list_dir(dir) {
          if !name.has_prefix(".") && !name.has_prefix("_") && name != "target" {
            let sub = dir + "/" + name
            if is_dir(sub) {
              walk(sub, missing)
            }
          }
        }
      }

      walk(base, missing)
      if missing.length() > 0 {
        println(
          "generating interfaces of " +
          user +
          "/" +
          m +
          " (" +
          missing.length().to_string() +
          " package(s))",
        )
        moon("info", mod_dir) catch {
          Failure(msg) => println("warning: " + msg)
        }
      }
    }
  }
}

///|
fn project_root() -> String raise Failure {
  match find_project(current_dir()) {
    Some(r) => r
    None => die("not in a MoonBit++ project (no moon.mod found)")
  }
}

///|
fn run_cli(args : Array[String]) -> Bool raise Failure {
  let rest : Array[String] = []
  let mut prelude = true
  let mut verbose = false
  let mut compiled = false
  let mut output : String? = None
  let prog_args : Array[String] = []
  let mut i = 0
  while i < args.length() {
    match args[i] {
      "--" => {
        for a in args[i + 1:] {
          prog_args.push(a)
        }
        break
      }
      "--no-prelude" => prelude = false
      "--verbose" => verbose = true
      "--compiled" => compiled = true
      "-o" | "--output" =>
        if i + 1 < args.length() {
          i = i + 1
          output = Some(args[i])
        } else {
          die("missing directory after " + args[i])
        }
      a => rest.push(a)
    }
    i = i + 1
  }
  let opts = { prelude, verbose, compiled, output, args: prog_args, }
  match rest {
    [] | ["help"] | ["--help"] | ["-h"] => {
      println(help_msg)
      true
    }
    ["version"] | ["--version"] => {
      println(version)
      true
    }
    ["new", name] => {
      new_project(name)
      println("created " + name + "; try: cd " + name + " && moonpp run")
      true
    }
    ["check"] => cmd_check(opts, None)
    ["check", p] => cmd_check(opts, Some(p))
    ["ide", f] => cmd_ide(opts, f, None)
    ["ide", f, "--overlay", o] => cmd_ide(opts, f, Some(o))
    ["fix"] => cmd_fix(opts, None)
    ["fix", p] => cmd_fix(opts, Some(p))
    ["build"] => cmd_build(opts, None)
    ["build", p] => cmd_build(opts, Some(p))
    ["run"] => cmd_run(opts, None)
    ["run", p] => cmd_run(opts, Some(p))
    ["test"] => cmd_test(opts, None)
    ["test", p] => cmd_test(opts, Some(p))
    [p] if p.has_suffix(".mbtpp") => cmd_run(opts, Some(p))
    ["add", m] => {
      let root = project_root()
      moon("add " + m, root)
      extract_interfaces(root)
      // `user/module@version`
      let name = match m.find("@") {
        Some(k) => m.unsafe_substring(start=0, end=k)
        None => m
      }
      println(
        "added " +
        m +
        "; list its packages (e.g. \"" +
        name +
        "/<pkg>\") in the import block of a moon.pkg",
      )
      true
    }
    ["remove", m] => {
      moon("remove " + m, project_root())
      true
    }
    ["install"] => {
      let root = project_root()
      moon("install", root)
      extract_interfaces(root)
      true
    }
    ["interfaces"] => {
      extract_interfaces(project_root())
      true
    }
    ["tree"] => {
      moon("tree", project_root())
      true
    }
    _ => {
      println(help_msg)
      false
    }
  }
}

///|
fn main {
  install_crash_report()
  // the first argument is the program itself
  let args = @sys.get_cli_args()
  let ok = run_cli(args[1:].to_array()) catch {
    Failure(msg) => {
      println("error: " + msg)
      false
    }
  }
  if !ok {
    set_exit_code(1)
  }
}
