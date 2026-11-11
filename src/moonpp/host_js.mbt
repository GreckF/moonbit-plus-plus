///|
/// A computation too deep for the checker or the interpreter (a recursion
/// on a large unary `Nat`, say) overflows the stack of Node.js: report it as
/// an error, with the definition being checked, rather than crash.
extern "js" fn js_catch_stack_overflow() -> Unit =
  #|() => {
  #|  process.on("uncaughtException", (e) => {
  #|    if (e instanceof RangeError && /call stack/.test(e.message)) {
  #|      const d = globalThis.__mbtpp_checking;
  #|      console.log("error: " + (d ? "checking " + d + ": " : "") +
  #|        "the computation is too deep for the stack (a recursion on a large Nat, say); " +
  #|        "make the function #opaque, or compute with smaller values");
  #|    } else {
  #|      console.error((e && e.stack) || e);
  #|    }
  #|    process.exit(1);
  #|  });
  #|}

///|
extern "js" fn js_set_checking(name : String) -> Unit =
  #|(name) => { globalThis.__mbtpp_checking = name; }

///|
fn install_crash_report() -> Unit {
  js_catch_stack_overflow()
  @tt.checking_hook.val = js_set_checking
}

///|
/// Running external commands (`moon add`, `moon info`, ...) on Node.js.
extern "js" fn js_run(cmd : String, cwd : String) -> Int32 =
  #|(cmd, cwd) => {
  #|  const r = require("child_process").spawnSync(cmd, { cwd, stdio: "inherit", shell: true });
  #|  return r.status === null ? 1 : r.status;
  #|}

///|
extern "js" fn js_run_quiet(cmd : String, cwd : String) -> Int32 =
  #|(cmd, cwd) => {
  #|  const r = require("child_process").spawnSync(cmd, { cwd, stdio: "ignore", shell: true });
  #|  return r.status === null ? 1 : r.status;
  #|}

///|
/// Run a shell command without showing its output.
fn run_quiet(cmd : String, cwd : String) -> Int32 {
  js_run_quiet(cmd, cwd)
}

///|
extern "js" fn js_cwd() -> String = "() => process.cwd()"

///|
/// Run a shell command in `cwd`; returns its exit status.
fn run_command(cmd : String, cwd : String) -> Int32 {
  js_run(cmd, cwd)
}

///|
fn current_dir() -> String {
  js_cwd()
}

///|
let can_run_commands : Bool = true

///|
/// Report the exit status to the launcher: moonpp runs in a worker thread,
/// where `process.exit` could drop output that is not flushed yet.
extern "js" fn set_exit_code(code : Int32) -> Unit =
  #|(code) => {
  #|  const { parentPort } = require("worker_threads");
  #|  if (parentPort) { parentPort.postMessage({ exitCode: code }); }
  #|  else { process.exitCode = code; }
  #|}

///|
/// Load the driver of the splices (a CommonJS module built by `moon build
/// --target js`, see driver.mbt), replacing the one loaded before.
extern "js" fn js_load_driver(path : String) -> Unit =
  #|(p) => {
  #|  const full = require("path").resolve(p);
  #|  delete require.cache[require.resolve(full)];
  #|  globalThis.__mbtpp_driver = require(full);
  #|}

///|
extern "js" fn js_driver_call(name : String, args : String) -> String =
  #|(n, a) => {
  #|  try {
  #|    return globalThis.__mbtpp_driver.call(n, a);
  #|  } catch (e) {
  #|    const m = String((e && e.message) || e);
  #|    return "e" + Array.from(m).length + ":" + m;
  #|  }
  #|}

///|
/// The function that the driver calls to run a function of the checker.
extern "js" fn js_set_callback(f : (Int32, String) -> String) -> Unit =
  #|(f) => { globalThis.__mbtpp_callback = f; }

///|
fn set_driver_callback(f : (Int32, String) -> String) -> Unit {
  js_set_callback(f)
}

///|
fn load_driver(path : String) -> Unit {
  js_load_driver(path)
}

///|
fn driver_call(name : String, args : String) -> String {
  js_driver_call(name, args)
}
