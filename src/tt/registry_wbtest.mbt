///|
test "the per-check state registers its own reset" {
  // The compiler drops globals that no code reachable from the test uses, so
  // make the whole checker reachable first.
  check_program("registry.mbtpp", "fn main() -> Unit { }") catch {
    _ => ()
  }
  // 50 globals are declared with the `@percheck` constructors
  assert_eq(@percheck.count(), 50)
}

///|
test "reset_all empties the per-check state" {
  metas.push({ sol: None, lax: false, })
  raises_cache.set("f", true)
  effect_decls.set("E", [])
  st.fresh = 7
  lifted_count.val = 3
  @percheck.reset_all()
  assert_eq(metas.length(), 0)
  assert_eq(raises_cache.length(), 0)
  assert_eq(effect_decls.contains("E"), false)
  assert_eq(effect_decls.contains("%Exn"), true)
  assert_eq(st.fresh, 0)
  assert_eq(lifted_count.val, 0)
}
