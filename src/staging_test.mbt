///|
/// Staged metaprogramming: `code { e }`, `${ c }`, `Code[T]`
/// (doc/mbtpp/staging.md).

///|
/// The definition of `name` after the expansion of its splices.
fn expanded(src : String, name : String) -> String {
  @tt.check_program("t.mbtpp", src) catch {
    @tt.CheckError(msg) => return msg
  }
  drop_counters(
    @tt.show_global_body(name).unwrap_or("no definition of " + name),
  )
}

///|
/// Without the counters of generated names: `f$go$12` is `f$go$N`.
fn drop_counters(s : String) -> String {
  let buf = StringBuilder::new()
  let cs : Array[Char] = s.iter().collect()
  let mut i = 0
  while i < cs.length() {
    buf.write_char(cs[i])
    if cs[i] == '$' &&
      i + 1 < cs.length() &&
      cs[i + 1] >= '0' &&
      cs[i + 1] <= '9' {
      buf.write_char('N')
      i = i + 1
      while i < cs.length() && cs[i] >= '0' && cs[i] <= '9' {
        i = i + 1
      }
    } else {
      i = i + 1
    }
  }
  buf.to_string()
}

///|
let power_src : String =
  #|fn power(n : Nat, x : Code[Int]) -> Code[Int] {
  #|  match n {
  #|    Z => code { 1 }
  #|    S(k) => code { ${x} * ${power(k, x)} }
  #|  }
  #|}
  #|
  #|fn cube(x : Int) -> Int {
  #|  ${ power(3, code { x }) }
  #|}
  #|
  #|lemma cube_2 : cube(2) === 8 = Refl
  #|
  #|fn main {
  #|  println(cube(3))
  #|}

///|
test "a splice is replaced by the code it makes" {
  inspect(expanded(power_src, "cube"), content="(x) => x * (x * (x * 1))")
  inspect(
    @mbtpp.run_source("t.mbtpp", power_src),
    content=(
      #|27
      #|
    ),
  )
  inspect(
    fn_code(power_src, "cube"),
    content=(
      #|fn f_cube_t(x : Int) -> Int {
      #|(x * (x * (x * (1))))
      #|}
      #|fn f_cube(a0 : Value) -> Value raise {
      #|  VInt(f_cube_t(as_int(a0)))
      #|}
    ),
  )
}

///|
let exp_src : String =
  #|enum Exp : [T] -> Type {
  #|  IntLit(Int) : Exp[Int]
  #|  BoolLit(Bool) : Exp[Bool]
  #|  Var : Exp[Int]
  #|  Add(Exp[Int], Exp[Int]) : Exp[Int]
  #|  Less(Exp[Int], Exp[Int]) : Exp[Bool]
  #|  If[T](Exp[Bool], Exp[T], Exp[T]) : Exp[T]
  #|}
  #|
  #|fn[T] Exp::compile(self : Exp[T], x : Code[Int]) -> Code[T] {
  #|  match self {
  #|    IntLit(n) => code { n }
  #|    BoolLit(b) => code { b }
  #|    Var => x
  #|    Add(l, r) => code { ${l.compile(x)} + ${r.compile(x)} }
  #|    Less(l, r) => code { ${l.compile(x)} < ${r.compile(x)} }
  #|    If[_](c, t, f) => code { if ${c.compile(x)} { ${t.compile(x)} } else { ${f.compile(x)} } }
  #|  }
  #|}
  #|
  #|fn f(x : Int) -> Int {
  #|  ${ If(Less(Var, IntLit(10)), Add(Var, IntLit(1)), IntLit(0)).compile(code { x }) }
  #|}
  #|
  #|fn main {
  #|  println(f(3))
  #|  println(f(30))
  #|}

///|
test "a staged interpreter of a typed language is a compiler" {
  inspect(
    expanded(exp_src, "f"),
    content=(
      #|(x) => match (x < 10) { true => x + 1; _ => 0 }
    ),
  )
  inspect(
    @mbtpp.run_source("t.mbtpp", exp_src),
    content=(
      #|4
      #|0
      #|
    ),
  )
  inspect(
    fn_code(exp_src, "f"),
    content=(
      #|fn f_f_t(x : Int) -> Int {
      #|if (x < (10)) {
      #|(x + (1))
      #|} else {
      #|0
      #|}
      #|fn f_f(a0 : Value) -> Value raise {
      #|  VInt(f_f_t(as_int(a0)))
      #|}
    ),
  )
}

///|
test "code is run at run time by run" {
  let src =
    #|fn twice(c : Code[Int]) -> Code[Int] { code { ${c} + ${c} } }
    #|fn main {
    #|  let n = 20
    #|  let c = twice(code { n + 1 })
    #|  println(c.run())
    #|}
  inspect(
    @mbtpp.run_source("t.mbtpp", src),
    content=(
      #|42
      #|
    ),
  )
  inspect(
    expanded(src, "main"),
    content=(
      #|{ let n = 20; let c = twice(code { n + 1 }); println(Code::run(c)) }
    ),
  )
}

///|
test "a variable of the generated code is not known to a splice" {
  inspect(
    @mbtpp.check_source(
      "t.mbtpp",
      (
        #|fn power(n : Nat, x : Code[Int]) -> Code[Int] {
        #|  match n {
        #|    Z => code { 1 }
        #|    S(k) => code { ${x} * ${power(k, x)} }
        #|  }
        #|}
        #|fn bad(n : Nat, x : Int) -> Int {
        #|  ${ power(n, code { x }) }
        #|}
      ),
    ),
    content=(
      #|t.mbtpp:8:12: error: n is not known when this splice runs: it is a variable of the generated code (it is bound at stage 0 and used at stage -1). Use it inside `code { }`
    ),
  )
  inspect(
    @mbtpp.check_source(
      "t.mbtpp",
      (
        #|fn bad(x : Int) -> Code[Int] {
        #|  let mut i = x
        #|  i = i + 1
        #|  code { i }
        #|}
      ),
    ),
    content=(
      #|t.mbtpp:4:10: error: the mutable variable i cannot be used across `code { }` or `${ }` (it is bound at stage 0 and used at stage 1); copy it first: let i0 = i
    ),
  )
  inspect(
    @mbtpp.check_source(
      "t.mbtpp",
      (
        #|fn bad(x : Int) -> Int {
        #|  ${ x }
        #|}
      ),
    ),
    content=(
      #|t.mbtpp:2:6: error: x is not known when this splice runs: it is a variable of the generated code (it is bound at stage 0 and used at stage -1). Use it inside `code { }`
    ),
  )
}

///|
test "generated code with loops and mutable variables" {
  let src =
    #|// the code of `body(i)` for each i from 0 to n - 1
    #|fn repeat(n : Int, body : (Int) -> Code[Unit]) -> Code[Unit] {
    #|  if n == 0 { code { () } } else {
    #|    code { ${repeat(n - 1, body)}; ${body(n - 1)} }
    #|  }
    #|}
    #|
    #|fn sum_to(m : Int) -> Int {
    #|  let mut s = 0
    #|  ${ repeat(3, i => code { s = s + i * m }) }
    #|  s
    #|}
    #|
    #|fn count(c : Code[Bool]) -> Code[Int] {
    #|  code {
    #|    let mut n = 0
    #|    while ${c} { n = n + 1; if n > 4 { break } }
    #|    n
    #|  }
    #|}
    #|
    #|fn five() -> Int { ${ count(code { true }) } }
    #|
    #|fn main {
    #|  println(sum_to(10))
    #|  println(five())
    #|}
  inspect(
    expanded(src, "sum_to"),
    content=(
      #|(m) => { let mut s = 0; s = s + (0 * m); s = s + (1 * m); s = s + (2 * m); s }
    ),
  )
  inspect(
    expanded(src, "five"),
    content=(
      #|(_) => { let mut n = 0; while true { n = n + 1; match (n > 4) { true => break; _ => () } }; n }
    ),
  )
  inspect(
    @mbtpp.run_source("t.mbtpp", src),
    content=(
      #|30
      #|5
      #|
    ),
  )
}

///|
test "a splice that cannot be run" {
  inspect(
    @mbtpp.check_source(
      "t.mbtpp",
      (
        #|fn twice(x : Int) -> Int = "@mbt:demo.twice"
        #|fn gen(x : Int) -> Code[Int] {
        #|  if twice(x) == 0 { code { 0 } } else { code { 1 } }
        #|}
        #|fn f() -> Int {
        #|  ${ gen(2) }
        #|}
      ),
    ),
    content=(
      #|t.mbtpp:6:3: error: this splice cannot be run when the program is checked: the code it makes is stuck on
      #|  gen(2)
      #|(a generator can use arrays and `print`, but not variables of the generated code or, without moonpp, imported MoonBit functions; to run the code at run time instead, use .run())
    ),
  )
}

///|
test "values known to the generator persist in the code" {
  let src =
    #|enum Color { Red; Green } derive(Show)
    #|fn pick(c : Color, s : String, f : (Int) -> Int) -> Code[String] {
    #|  code { s + c.to_string() + f(1).to_string() }
    #|}
    #|fn g(k : Int) -> String {
    #|  ${ pick(Green, "a" + "b", x => x + 40 + 1) }
    #|}
    #|fn main { println(g(0)) }
  inspect(
    expanded(src, "g"),
    content=(
      #|(k) => ("ab" + Show::to_string(Green)) + Int::to_string(((x) => (x + 40) + 1)(1))
    ),
  )
  inspect(
    @mbtpp.run_source("t.mbtpp", src),
    content=(
      #|abGreen42
      #|
    ),
  )
}

///|
test "code that raises" {
  let src =
    #|suberror DivError { DivError(String) }
    #|fn div(a : Int, b : Int) -> Int raise DivError {
    #|  if b == 0 { raise DivError("div by zero") }
    #|  a / b
    #|}
    #|fn half(c : Code[Int]) -> Code[Int raise DivError] { code { div(${c}, 0) } }
    #|fn f(x : Int) -> Int raise DivError { ${ half(code { x }) } }
    #|fn main {
    #|  try { println(f(4)) } catch { DivError(m) => println(m) }
    #|}
  inspect(
    expanded(src, "f"),
    content=(
      #|(x) => div(x, 0)
    ),
  )
  inspect(
    @mbtpp.run_source("t.mbtpp", src),
    content=(
      #|div by zero
      #|
    ),
  )
}

///|
test "return in code leaves the code" {
  let src =
    #|fn clamp(c : Code[Int]) -> Code[Int] {
    #|  code { let v = ${c}; if v > 9 { return 9 }; v }
    #|}
    #|fn f(x : Int) -> Int { ${ clamp(code { x }) } + 1 }
    #|fn main { println(f(3)); println(f(30)) }
  inspect(
    expanded(src, "f"),
    content=(
      #|(x) => ((_) => { let v = x; match (v > 9) { true => return 9; _ => () }; v })(()) + 1
    ),
  )
  inspect(
    @mbtpp.run_source("t.mbtpp", src),
    content=(
      #|4
      #|10
      #|
    ),
  )
}

///|
test "local recursive functions in generators and in code" {
  let src =
    #|fn f(x : Int) -> Int {
    #|  ${
    #|    fn go(n : Int, acc : Code[Int]) -> Code[Int] {
    #|      if n == 0 { acc } else { go(n - 1, code { ${acc} + x }) }
    #|    }
    #|    go(3, code { 0 })
    #|  }
    #|}
    #|fn loop_code(step : Code[Int]) -> Code[Int] {
    #|  code {
    #|    fn go(i : Int, acc : Int) -> Int {
    #|      if i == 0 { acc } else { go(i - 1, acc + ${step}) }
    #|    }
    #|    go(4, 0)
    #|  }
    #|}
    #|fn g(x : Int) -> Int { ${ loop_code(code { x }) } }
    #|fn main { println(f(5)); println(g(5)) }
  inspect(
    expanded(src, "f"),
    content=(
      #|(x) => ((0 + x) + x) + x
    ),
  )
  inspect(
    expanded(src, "g"),
    content=(
      #|(x) => { let go = loop_code$go$N$s1(x); go(4, 0) }
    ),
  )
  inspect(
    @mbtpp.run_source("t.mbtpp", src),
    content=(
      #|15
      #|20
      #|
    ),
  )
}

///|
test "code is compared by what it does" {
  inspect(
    @mbtpp.check_source(
      "t.mbtpp",
      (
        #|fn inc(c : Code[Int]) -> Code[Int] { code { ${c} + 1 } }
        #|lemma inc_run(c : Code[Int]) -> inc(c).run() === c.run() + 1 { Refl }
        #|lemma eta(c : Code[Int]) -> code { ${c} } === c { Refl }
        #|lemma beta : code { 1 + 1 }.run() === 2 = Refl
      ),
    ),
    content=(
      #|ok
    ),
  )
}

///|
test "the splices of code run when the code is made" {
  // an error raised in a splice is raised by what makes the code
  let src =
    #|suberror E { E }
    #|fn gen(b : Bool) -> Code[Int] raise E {
    #|  code { 1 + ${ if b { raise E }; code { 2 } } }
    #|}
    #|fn main {
    #|  let c = try gen(true) catch { E => code { 0 } }
    #|  println(c.run())
    #|  let d = try gen(false) catch { E => code { 0 } }
    #|  println(d.run())
    #|}
  inspect(
    expanded(src, "gen"),
    content=(
      #|(b) => code { 1 + ${ { match b { true => raise E; _ => () }; code { 2 } } } }
    ),
  )
  inspect(
    @mbtpp.run_source("t.mbtpp", src),
    content=(
      #|0
      #|3
      #|
    ),
  )
  // so is an effect performed in a splice
  inspect(
    @mbtpp.run_source(
      "t.mbtpp",
      (
        #|effect Fresh { Fresh() -> Int }
        #|fn name() -> Code[Int]!Fresh { let n = perform Fresh(); code { n } }
        #|fn gen() -> Code[Int]!Fresh { code { ${name()} * 10 + ${name()} } }
        #|fn main {
        #|  let mut k = 0
        #|  let c = try { gen() } catch { Fresh() => { k = k + 1; resume(k) } }
        #|  println(k)
        #|  println(c.run())
        #|}
      ),
    ),
    content=(
      #|2
      #|12
      #|
    ),
  )
}

///|
test "splices that cannot have effects" {
  // a splice that uses the variables of the code runs with the code
  inspect(
    @mbtpp.check_source(
      "t.mbtpp",
      (
        #|suberror E { E }
        #|fn f(c : Code[Int]) -> Code[Int] raise E { raise E }
        #|fn gen() -> Code[(Int) -> Int] raise E {
        #|  code { (y : Int) => ${ f(code { y }) } }
        #|}
      ),
    ),
    content=(
      #|t.mbtpp:4:27: error: this call may raise an error; use it inside `try` or in a function declared with `raise`
      #|hint: this splice uses variables of the code it is in, so it runs when that code does: it cannot raise errors or perform effects
    ),
  )
  // a splice in a definition runs when the program is checked
  inspect(
    @mbtpp.check_source(
      "t.mbtpp",
      (
        #|suberror E { E }
        #|fn f() -> Code[Int] raise E { raise E }
        #|fn g() -> Int { ${ f() } }
      ),
    ),
    content=(
      #|t.mbtpp:3:21: error: this call may raise an error; use it inside `try` or in a function declared with `raise`
      #|hint: a splice in a definition runs when the program is checked: it cannot raise errors or perform effects
    ),
  )
  inspect(
    @mbtpp.check_source(
      "t.mbtpp",
      (
        #|fn g(x : Int) -> Int { ${ x + 1 } }
      ),
    ),
    content=(
      #|t.mbtpp:1:27: error: x is not known when this splice runs: it is a variable of the generated code (it is bound at stage 0 and used at stage -1). Use it inside `code { }`
    ),
  )
}

///|
test "generators with mutable state, and let insertion" {
  let src =
    #|fn sum_code(n : Int, x : Code[Int]) -> Code[Int] {
    #|  let mut acc = code { 0 }
    #|  for i = 0; i < n; i = i + 1 {
    #|    let a = acc
    #|    acc = code { ${a} + ${x} * i }
    #|  }
    #|  acc
    #|}
    #|fn g(x : Int) -> Int { ${ sum_code(3, code { x }) } }
    #|
    #|// `let t = c; k(t)`: the code `c` is evaluated once
    #|fn genlet(c : Code[Int], k : (Code[Int]) -> Code[Int]) -> Code[Int] {
    #|  code { let t = ${c}; ${ k(code { t }) } }
    #|}
    #|fn square_sum(a : Code[Int], b : Code[Int]) -> Code[Int] {
    #|  genlet(code { ${a} + ${b} }, s => code { ${s} * ${s} })
    #|}
    #|fn f(x : Int, y : Int) -> Int { ${ square_sum(code { x }, code { y }) } }
    #|fn main { println(g(10)); println(f(1, 2)) }
  inspect(
    expanded(src, "g"),
    content=(
      #|(x) => ((0 + (x * 0)) + (x * 1)) + (x * 2)
    ),
  )
  inspect(
    expanded(src, "f"),
    content=(
      #|(x, y) => { let t = x + y; t * t }
    ),
  )
  inspect(
    @mbtpp.run_source("t.mbtpp", src),
    content=(
      #|30
      #|9
      #|
    ),
  )
}

///|
test "what the generator knows about types" {
  let src =
    #|enum Vector[T] : Nat -> Type {
    #|  Nil : Vector[T](0)
    #|  Cons[n : Nat](T, Vector[T](n)) : Vector[T](S(n))
    #|}
    #|// the length is known: no loop, and no case for Nil
    #|fn sum_n(n : Nat, v : Code[Vector[Int](n)]) -> Code[Int] {
    #|  match n {
    #|    Z => code { 0 }
    #|    S(k) => code { match ${v} { Cons(h, t) => h + ${sum_n(k, code { t })} } }
    #|  }
    #|}
    #|fn sum3(v : Vector[Int](3)) -> Int { ${ sum_n(3, code { v }) } }
    #|
    #|// the instance is known
    #|fn[T : Add] double(x : Code[T]) -> Code[T] { code { ${x} + ${x} } }
    #|fn twice(x : Int) -> Int { ${ double(code { x }) } }
    #|fn again(s : String) -> String { ${ double(code { s }) } }
    #|
    #|fn main {
    #|  println(sum3(Cons(1, Cons(2, Cons(3, Nil)))))
    #|  println(twice(4))
    #|  println(again("ab"))
    #|}
  inspect(
    expanded(src, "sum3"),
    content=(
      #|(v) => match v { Cons(_, h, t) => h + match t { Cons(_, h1, t1) => h1 + match t1 { Cons(_, h2, t2) => h2 + 0 } } }
    ),
  )
  inspect(
    expanded(src, "twice"),
    content=(
      #|(x) => x + x
    ),
  )
  inspect(
    expanded(src, "again"),
    content=(
      #|(s) => s + s
    ),
  )
  inspect(
    @mbtpp.run_source("t.mbtpp", src),
    content=(
      #|6
      #|8
      #|abab
      #|
    ),
  )
  inspect(
    fn_code(src, "twice"),
    content=(
      #|fn f_twice_t(x : Int) -> Int raise {
      #|(Add::add(x, x) : Int)
      #|}
      #|fn f_twice(a0 : Value) -> Value raise {
      #|  VInt(f_twice_t(as_int(a0)))
      #|}
    ),
  )
}

///|
test "splices in lambdas and arms, opaque generators, nested code" {
  let src =
    #|#opaque
    #|fn power(n : Nat, x : Code[Int]) -> Code[Int] {
    #|  match n {
    #|    Z => code { 1 }
    #|    S(k) => code { ${x} * ${power(k, x)} }
    #|  }
    #|}
    #|fn g(o : Option[Int]) -> (Int) -> Int {
    #|  match o {
    #|    None => y => ${ power(2, code { y }) }
    #|    Some(z) => y => ${ power(1, code { y + z }) }
    #|  }
    #|}
    #|#unfold(power)
    #|lemma g_none(y : Int) -> g(None)(y) === y * (y * 1) { Refl }
    #|fn main {
    #|  println(g(None)(5))
    #|  println(g(Some(1))(5))
    #|  let c = code { code { 1 + 2 } }
    #|  println(c.run().run())
    #|  let f = code { (x : Int) => x * 2 }
    #|  let d = code { $f(21) }
    #|  println(d.run())
    #|}
  inspect(
    expanded(src, "g"),
    content=(
      #|(o) => match o { None => (y) => y * (y * 1); Some(z) => (y) => (y + z) * 1 }
    ),
  )
  inspect(
    @mbtpp.run_source("t.mbtpp", src),
    content=(
      #|25
      #|6
      #|3
      #|42
      #|
    ),
  )
}

///|
test "generated code compiles to MoonBit" {
  let src =
    #|fn twice(c : Code[Int]) -> Code[Int] { code { ${c} + ${c} } }
    #|fn main {
    #|  let n = 20
    #|  println(twice(code { n + 1 }).run())
    #|}
  inspect(
    fn_code(src, "twice"),
    content=(
      #|fn f_twice(c : Value) -> Value raise {
      #|make_code({
      #|let s0 = c
      #|{
      #|let s1 = c
      #|VFun(j => match j {
      #|(VInt(0)) => (s0)
      #|(VInt(1)) => (s1)
      #|_ => rt_fail("no match")
      #|})
      #|}
    ),
  )
}

///|
test "generators use arrays and print" {
  // an array as the data of the generator
  let src =
    #|fn sum_code(xs : Array[Int], x : Code[Int]) -> Code[Int] {
    #|  let mut acc = code { 0 }
    #|  for k in xs { let a = acc; acc = code { ${a} + ${x} * k } }
    #|  acc
    #|}
    #|fn f(x : Int) -> Int { ${ sum_code([1, 2, 3], code { x }) } }
    #|
    #|// an array made by the generator: computed when the code is made
    #|fn table(n : Int) -> Array[Int] {
    #|  let t : Array[Int] = []
    #|  for i = 0; i < n; i = i + 1 { t.push(i * i) }
    #|  t
    #|}
    #|fn pick(i : Int) -> Code[Int] { let t = table(5); code { t[i] } }
    #|fn g() -> Int { ${ pick(3) } }
    #|
    #|// what a generator prints is printed when the program is checked
    #|fn say() -> Code[Int] { println("generating"); code { 1 } }
    #|fn h() -> Int { ${ say() } }
    #|fn main { println(f(10)); println(g()); println(h()) }
  @tt.staging_echo.val = false
  inspect(
    expanded(src, "f"),
    content=(
      #|(x) => ((0 + (x * 1)) + (x * 2)) + (x * 3)
    ),
  )
  inspect(
    expanded(src, "g"),
    content=(
      #|(_) => Array::op_get([0, 1, 4, 9, 16], 3)
    ),
  )
  inspect(
    @tt.staging_output,
    content=(
      #|[generating
      #|]
    ),
  )
  inspect(
    @mbtpp.run_source("t.mbtpp", src),
    content=(
      #|60
      #|9
      #|1
      #|
    ),
  )
  @tt.staging_echo.val = true
}

///|
/// A host that runs `demo` functions, in MoonBit (the real one is built by
/// moonpp, see ffi.mbt): `twice`, `rev` and `maybe`.
fn demo_host() -> @tt.FfiHost {
  {
    prepare: names => {
      if names.contains("fail_prepare") {
        Some("no driver")
      } else {
        None
      }
    },
    set_callback: _ => (),
    call: (name, args) => {
      match (name, args) {
        ("twice", "a1;i21;") => "oi42;"
        ("greet", _) => "os5:hello"
        ("rev", "a2;ua3;i1;i2;i3;") => "oa3;i3;i2;i1;"
        ("maybe", "a1;i0;") => "ok12:Option::None0;"
        ("maybe", "a1;i5;") => "ok12:Option::Some1;i5;"
        ("boom", _) => "r4:boom"
        _ =>
          "e" +
          (name + " " + args).length().to_string() +
          ":" +
          name +
          " " +
          args
      }
    },
  }
}

///|
test "generators call imported MoonBit functions through a host" {
  @tt.ffi_host.val = Some(demo_host())
  @tt.staging_echo.val = false
  let src =
    #|fn twice(x : Int) -> Int = "@mbt:demo.twice"
    #|fn greet() -> String = "@mbt:demo.greet"
    #|fn[T] rev(xs : Array[T]) -> Array[T] = "@mbt:demo.rev"
    #|fn maybe(x : Int) -> Int? = "@mbt:demo.maybe"
    #|
    #|fn gen(n : Int) -> Code[Int] { let k = twice(n); code { k + 1 } }
    #|fn f() -> Int { ${ gen(21) } }
    #|
    #|fn msg() -> String { ${ let s = greet(); code { s } } }
    #|fn order() -> Int { ${ let xs = rev([1, 2, 3]); code { xs[0] } } }
    #|fn opt() -> Int { ${ match maybe(5) { Some(v) => code { v }; None => code { 0 } } } }
    #|fn none() -> Int { ${ match maybe(0) { Some(v) => code { v }; None => code { -1 } } } }
    #|fn main { println(f()); println(msg()); println(order()); println(opt()); println(none()) }
  inspect(
    expanded(src, "f"),
    content=(
      #|(_) => 42 + 1
    ),
  )
  inspect(
    expanded(src, "msg"),
    content=(
      #|(_) => "hello"
    ),
  )
  inspect(
    expanded(src, "order"),
    content=(
      #|(_) => Array::op_get([3, 2, 1], 0)
    ),
  )
  inspect(
    expanded(src, "opt"),
    content=(
      #|(_) => 5
    ),
  )
  inspect(
    expanded(src, "none"),
    content=(
      #|(_) => -1
    ),
  )
  // an error raised by the MoonBit function is an error of the generator
  inspect(
    expanded(
      (
        #|fn boom() -> Int raise = "@mbt:demo.boom"
        #|fn gen() -> Code[Int] {
        #|  try { let x = boom(); code { x } } catch { _ => code { 0 } }
        #|}
        #|fn g() -> Int { ${ gen() } }
      ),
      "g",
    ),
    content=(
      #|(_) => 0
    ),
  )
  // an imported function that is not in the host
  inspect(
    @mbtpp.check_source(
      "t.mbtpp",
      (
        #|fn unknown(x : Int) -> Int = "@mbt:demo.unknown"
        #|fn g() -> Int { ${ let x = unknown(1); code { x } } }
      ),
    ),
    content=(
      #|t.mbtpp:2:1: error: the MoonBit function unknown could not be called: unknown a1;i1;
    ),
  )
  @tt.ffi_host.val = None
  @tt.staging_echo.val = true
}
