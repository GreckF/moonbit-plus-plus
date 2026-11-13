///|
/// Guard for the primitive tables. A primitive `"%name"` lives in six places:
/// the Prelude declaration (`tt/prelude.mbt`), `tt/prims.mbt` (`prim_pure`),
/// `interp/interp.mbt` (`Machine::prim`), `inline_prims` (`codegen.mbt`),
/// `native_prims` (`typed.mbt`) and the runtime's `prim` (`runtime.mbt`).
/// The rule enforced here: every `inline_prims` / `native_prims` key and every
/// Prelude primitive must be handled by the runtime's `prim` (the target of a
/// dynamic `prim("%name", ..)` call), unless listed in `special_prims` below.

///|
/// Index of the first occurrence of `sub` in `s` at or after `from`.
fn find_sub(s : String, sub : String, from : Int32) -> Int32? {
  match s.unsafe_substring(start=from, end=s.length()).find(sub) {
    Some(i) => Some(from + i)
    None => None
  }
}

///|
/// The text of the runtime's `fn prim(name : String, args : Array[Value])`.
fn runtime_prim_text() -> String {
  let src = runtime_src
  let start = find_sub(src, "fn prim(name : String, args : Array[Value])", 0).unwrap()
  // the function ends at the first closing brace in column 0
  let stop = find_sub(src, "\n}\n", start).unwrap()
  src.unsafe_substring(start~, end=stop)
}

///|
/// All `"%name"` strings declared as `= "%name"` in the Prelude.
fn prelude_prim_names() -> Array[String] {
  let src = @tt.prelude_src
  let names : Array[String] = []
  let mut from = 0
  while find_sub(src, "= \"%", from) is Some(i) {
    let s = i + 3
    let e = find_sub(src, "\"", s).unwrap()
    let name = src.unsafe_substring(start=s, end=e)
    if !names.contains(name) {
      names.push(name)
    }
    from = e
  }
  names
}

///|
/// Prelude primitives the compiler handles outside the tables (none needed:
/// staging, effect and external `@mbt:` primitives are not declared as
/// `= "%name"` in the Prelude).
let special_prims : Array[String] = []

///|
/// KNOWN GAPS: `native_prims` entries (typed.mbt) with no arm in the runtime's
/// `prim`. In uniform code `Gen::prim_call` uses the native template between
/// conversions, but falls back to the dynamic `prim("%name", ..)` call (which
/// ends in `rt_fail("primitive .. failed")`) when an argument's code contains
/// `$`; for these names that call has no arm. Remove an entry when its arm is
/// added to the runtime (the test then insists on that).
let known_gaps : Array[String] = [
  "%nat_lt", "%nat_le", "%nat_gt", "%nat_ge", "%nat_sub", "%nat_div", "%nat_mod",
  "%nat_gcd", "%nat_pow", "%nat_shl", "%nat_shr", "%nat_log2", "%nat_land", "%nat_lor",
  "%nat_lxor", "%nat_of_bigint", "%nat_to_bigint", "%bigint_eq", "%bigint_ge", "%bigint_gt",
  "%bigint_le", "%bigint_lt", "%bigint_add", "%bigint_sub", "%bigint_mul", "%bigint_div",
  "%bigint_mod", "%bigint_neg", "%bigint_pow", "%bigint_shl", "%bigint_shr", "%bigint_land",
  "%bigint_lor", "%bigint_lxor", "%bigint_hash", "%bigint_of_int", "%bigint_to_int",
  "%bigint_of_int64", "%bigint_to_int64", "%bigint_to_string", "%bigint_compare",
]

///|
test "compiler primitive tables agree" {
  let rt = runtime_prim_text()
  let in_runtime = fn(n : String) {
    find_sub(rt, "(\"" + n + "\",", 0) is Some(_)
  }
  let prelude = prelude_prim_names()
  let problems : Array[String] = []
  if prelude.length() < 150 {
    problems.push(
      "scanning the Prelude found only \{prelude.length()} primitives",
    )
  }
  let missing_a : Array[String] = []
  for name, _ in inline_prims {
    if !in_runtime(name) {
      missing_a.push(name)
    }
  }
  let missing_b : Array[String] = []
  for name, _ in native_prims {
    if !in_runtime(name) && !known_gaps.contains(name) {
      missing_b.push(name)
    }
  }
  let missing_c : Array[String] = []
  for name in prelude {
    let ok = in_runtime(name) ||
      inline_prims.contains(name) ||
      native_prims.contains(name) ||
      special_prims.contains(name)
    if !ok {
      missing_c.push(name)
    }
  }
  let stale_gaps : Array[String] = []
  for name in known_gaps {
    if in_runtime(name) || !native_prims.contains(name) {
      stale_gaps.push(name)
    }
  }
  if missing_a.length() > 0 {
    missing_a.sort()
    problems.push(
      "in inline_prims (codegen.mbt) but not in the runtime's prim (runtime.mbt): " +
      missing_a.join(", "),
    )
  }
  if missing_b.length() > 0 {
    missing_b.sort()
    problems.push(
      "in native_prims (typed.mbt) but not in the runtime's prim (runtime.mbt) nor known_gaps: " +
      missing_b.join(", "),
    )
  }
  if missing_c.length() > 0 {
    missing_c.sort()
    problems.push(
      "declared in the Prelude but in none of the runtime's prim, inline_prims, native_prims, special_prims: " +
      missing_c.join(", "),
    )
  }
  if stale_gaps.length() > 0 {
    stale_gaps.sort()
    problems.push(
      "known_gaps entries that are no longer gaps (now in the runtime, or not in native_prims): " +
      stale_gaps.join(", "),
    )
  }
  if problems.length() > 0 {
    fail(problems.join("\n"))
  }
}
