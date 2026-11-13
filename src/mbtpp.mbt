///|
/// Type check and run a MoonBit++ program, returning its output (or the
/// first error).
pub fn run_source(file : String, src : String) -> String {
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
/// Only type check; returns "ok" or the first error.
pub fn check_source(file : String, src : String) -> String {
  @tt.check_program(file, src) catch {
    @tt.CheckError(msg) => return msg
  }
  "ok"
}
