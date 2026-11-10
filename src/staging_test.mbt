///|
/// Staged metaprogramming: `code { e }`, `${ c }`, `Code[T]`
/// (doc/mbtpp/staging.md).

///|
/// The definition of `name` after the expansion of its splices.
fn expanded(src : String, name : String) -> String {
  @tt.check_program("t.mbtpp", src) catch {
    @tt.CheckError(msg) => return msg
  }
  @tt.show_global_body(name).unwrap_or("no definition of " + name)
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
    run_source("t.mbtpp", power_src),
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
    run_source("t.mbtpp", exp_src),
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
    run_source("t.mbtpp", src),
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
    check_source(
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
    check_source(
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
    check_source(
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
    run_source("t.mbtpp", src),
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
    check_source(
      "t.mbtpp",
      (
        #|fn gen(xs : Array[Int]) -> Code[Int] {
        #|  if xs.length() == 0 { code { 0 } } else { code { 1 } }
        #|}
        #|fn f() -> Int {
        #|  ${ gen([1, 2]) }
        #|}
      ),
    ),
    content=(
      #|t.mbtpp:5:3: error: this splice cannot be run when the program is checked: the code it makes is stuck on
      #|  gen([1, 2])
      #|(code generators cannot use arrays, `print`, imported MoonBit functions, or variables of the generated code; to run the code at run time instead, use .run())
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
    run_source("t.mbtpp", src),
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
    run_source("t.mbtpp", src),
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
    run_source("t.mbtpp", src),
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
      #|(x) => { let go = loop_code$go$4(code { x }, ()); go(4, 0) }
    ),
  )
  inspect(
    run_source("t.mbtpp", src),
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
    check_source(
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
