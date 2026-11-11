///|
/// Other backends cannot start processes: only the JS build of moonpp can
/// call `moon`.
fn run_command(cmd : String, cwd : String) -> Int32 {
  ignore(cmd)
  ignore(cwd)
  -1
}

///|
fn run_quiet(cmd : String, cwd : String) -> Int32 {
  run_command(cmd, cwd)
}

///|
fn current_dir() -> String {
  "."
}

///|
let can_run_commands : Bool = false

///|
fn install_crash_report() -> Unit {
  ()
}

///|
fn set_exit_code(code : Int32) -> Unit {
  @sys.exit(code)
}

///|
fn set_driver_callback(f : (Int32, String) -> String) -> Unit {
  ignore(f)
}

///|
fn load_driver(path : String) -> Unit {
  ignore(path)
}

///|
fn driver_call(name : String, args : String) -> String {
  ignore(name)
  ignore(args)
  "e0:"
}
