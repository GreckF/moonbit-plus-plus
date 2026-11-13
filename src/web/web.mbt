///|
/// Entry points of the online playground (built with `--target js`).
/// Each takes the source of a single file `main.mbtpp`.
let file : String = "main.mbtpp"

///|
/// Type check; returns "ok" or the first error.
pub fn check(src : String) -> String {
  @tt.check_program(file, src) catch {
    @tt.CheckError(msg) => return msg
  }
  "ok"
}

///|
/// Type check and run with the interpreter; returns the output (and the
/// error, if any).
pub fn run(src : String) -> String {
  @tt.check_program(file, src) catch {
    @tt.CheckError(msg) => return msg
  }
  let buf = StringBuilder()
  @interp.run_main(s => buf.write_string(s)) catch {
    @interp.RunError(msg) => buf.write_string(msg)
  }
  buf.to_string()
}

///|
/// Type check and compile to MoonBit; returns the generated files (one
/// `// ==== name ====` section each), or
/// an error starting with "error".
pub fn compile(src : String) -> String {
  @tt.check_program(file, src) catch {
    @tt.CheckError(msg) => return "error: " + msg
  }
  @codegen.generate([]) catch {
    @codegen.CodegenError(msg) => "error: cannot compile: " + msg
  }
}

///|
/// The runtime support file of compiled programs (`mbtpp_runtime.mbt`).
pub fn runtime() -> String {
  @codegen.runtime_code()
}
