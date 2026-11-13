///|
test "moon.pkg" {
  let f = parse_moon_file(
    (
      #|warnings = "-a"
      #|
      #|import {
      #|  "u/mig/lib",
      #|  "moonbitlang/core/strconv" @conv,
      #|}
      #|
      #|import {
      #|  "moonbitlang/x/fs",
      #|} for "test"
      #|
      #|options(
      #|  "is-main": true,
      #|  targets: { "a.mbt": [ "js" ], "b.mbt": [ "not", "js" ] },
      #|  link: { "js": { "exports": [ "f" ], "format": "esm" } },
      #|)
    ),
  )
  inspect(
    f.imports.map(i => (i.path, i.pkg_alias, i.kind)),
    content=(
      #|[(u/mig/lib, None, None), (moonbitlang/core/strconv, Some(conv), None), (moonbitlang/x/fs, None, Some(test))]
    ),
  )
  inspect(
    f.option("is-main"),
    content=(
      #|Some(MAtom(true))
    ),
  )
  inspect(
    f.string_field("warnings"),
    content=(
      #|Some(-a)
    ),
  )
}

///|
test "moon.mod and moon.work" {
  let m = parse_moon_file(
    (
      #|name = "u/app"
      #|
      #|version = "0.1.0"
      #|
      #|import {
      #|  "moonbitlang/x@0.5.6",
      #|}
      #|
      #|keywords = [ ]
      #|
      #|source = "src"
    ),
  )
  inspect(
    (
      m.string_field("name"),
      m.string_field("source"),
      m.imports.map(i => i.path),
    ),
    content=(
      #|(Some(u/app), Some(src), [moonbitlang/x@0.5.6])
    ),
  )
  let w = parse_moon_file("members = [\n  \".\",\n  \"../geo\",\n]\n")
  inspect(
    w.fields.get("members"),
    content=(
      #|Some(MList([MStr(.), MStr(../geo)]))
    ),
  )
}

///|
test "pkgtype" {
  let f = parse_moon_file(
    (
      #|warnings = "-a"
      #|
      #|pkgtype(kind: "executable")
    ),
  )
  inspect(
    f.call_arg("pkgtype", "kind"),
    content=(
      #|Some(MStr(executable))
    ),
  )
}

///|
test "paths" {
  inspect(join_path("C:\\a\\app", "../geo"), content="C:/a/geo")
  inspect(join_path("/x/app", "."), content="/x/app")
  inspect(join_path("/x/app", "./lib/../m"), content="/x/app/m")
}
