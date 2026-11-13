///|
/// The driver of the splices: when the splices of a package call imported
/// MoonBit functions, the checker needs a program that has them (see
/// tt/ffi.mbt). It is built with the compiler's wrappers of imported
/// functions as a MoonBit project in `mbtpp_out/driver` (next to the output
/// of `moonpp build`), compiled to JavaScript with `moon`, and loaded into
/// moonpp. Only the JS build of moonpp can do this.

///|
/// Write a file unless it has this content already (so that `moon` does not
/// build again what did not change).
fn write_if_changed(path : String, content : String) -> Unit raise Failure {
  if @fs.path_exists(path) {
    let old = @fs.read_file_to_string(path) catch { _ => "" }
    if old == content {
      return
    }
  }
  write_file(path, content)
}

///|
/// Build and load the driver for the imported functions `names`; an error
/// message if that fails.
fn build_driver(
  out : String,
  project : String?,
  imports : Array[@tt.Import],
  names : Array[String],
) -> String? {
  let (files, _) = @codegen.generate_driver(
    imports.map(i => (i.path, i.pkg_alias)),
    names,
  ) catch {
    @codegen.CodegenError(msg) => return Some(msg)
  }
  try {
    let pkg = "driver"
    make_dirs(out + "/" + pkg)
    let (mod_file, work_file) = output_module(project, "mbtpp/driver")
    write_if_changed(out + "/moon.mod", mod_file)
    write_if_changed(out + "/moon.work", work_file)
    write_if_changed(
      out + "/.gitignore",
      (
        #|_build/
        #|target/
        #|.mooncakes/
        #|moon.work.lock
        #|
      ),
    )
    // the driver is loaded with `require`
    write_if_changed(out + "/package.json", "{ \"type\": \"commonjs\" }\n")
    let pkg_file = StringBuilder::new()
    pkg_file.write_string("warnings = \"-a\"\n")
    pkg_file.write_string("\nimport {\n  \"moonbitlang/core/float\",\n")
    for i in imports {
      pkg_file.write_string("  " + mstr(i.path) + " @" + i.pkg_alias + ",\n")
    }
    pkg_file.write_string("}\n")
    pkg_file.write_string(
      "\noptions(\n  \"is-main\": true,\n  link: { \"js\": { \"exports\": [ \"call\" ], \"format\": \"cjs\" } },\n)\n",
    )
    write_if_changed(out + "/" + pkg + "/moon.pkg", pkg_file.to_string())
    for f in files {
      write_if_changed(out + "/" + pkg + "/" + f.0, f.1)
    }
    write_if_changed(
      out + "/" + pkg + "/" + @codegen.runtime_file_name(),
      @codegen.runtime_code(),
    )
    // quietly, and with its messages only if it fails
    if run_quiet("moon build --target js", out) != 0 &&
      run_command("moon build --target js", out) != 0 {
      return Some(
        "building the MoonBit program for the splices failed (" +
        out +
        "); see the errors above",
      )
    }
    load_driver(out + "/_build/js/debug/build/" + pkg + "/" + pkg + ".js")
    None
  } catch {
    Failure(msg) => Some(msg)
  }
}

///|
/// Let the checker call imported MoonBit functions in the splices of the
/// package in `dir` (where moonpp can run `moon`).
fn install_ffi_host(dir : String, imports : Array[@tt.Import]) -> Unit {
  if !can_run_commands {
    return
  }
  let project = find_project(dir)
  let out = match project {
    Some(root) => root + "/mbtpp_out/driver"
    None => dir + "/_mbtpp_build/driver"
  }
  @tt.ffi_host.val = Some({
    prepare: names => build_driver(out, project, imports, names),
    call: (name, args) => driver_call(name, args),
    set_callback: f => set_driver_callback(f),
  })
}
