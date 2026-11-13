///|
/// Regression tests for bugs found by code review.

///|
test "return and break leave a try with ctl arms" {
  inspect(
    @mbtpp.run_source(
      "t.mbtpp",
      (
        #|effect Choose {
        #|  ctl Choose() -> Bool
        #|}
        #|fn r1() -> Int {
        #|  let x = try { if perform Choose() { return 42 }; 1 } catch { Choose() => resume(true) }
        #|  x + 100
        #|}
        #|fn r2() -> Int {
        #|  let mut n = 0
        #|  while n < 10 {
        #|    try { if perform Choose() { break }; () } catch { Choose() => resume(n >= 3) }
        #|    n = n + 1
        #|  }
        #|  n
        #|}
        #|fn r3() -> Int {
        #|  let x = try { if perform Choose() { 1 } else { 2 } } catch { Choose() => return 7 }
        #|  x
        #|}
        #|lemma l1() -> r1() === 42 { Refl }
        #|fn main { println(r1()); println(r2()); println(r3()) }
      ),
    ),
    content=(
      #|42
      #|3
      #|7
      #|
    ),
  )
}

///|
test "a ctl call in tail position saves let mut" {
  inspect(
    @mbtpp.run_source(
      "t.mbtpp",
      (
        #|effect Choose {
        #|  ctl Choose() -> Bool
        #|}
        #|fn g(get : () -> Int!Choose, set : (Int) -> Unit!Choose) -> Int!Choose {
        #|  set(1)
        #|  let _b = perform Choose()
        #|  set(get() + 10)
        #|  get()
        #|}
        #|fn tailcall() -> Int!Choose {
        #|  let mut x = 0
        #|  g(() => x, v => { x = v })
        #|}
        #|fn main {
        #|  println(try { Cons(tailcall(), Nil) } catch { Choose() => resume(true).append(resume(false)) })
        #|}
      ),
    ),
    content=(
      #|Cons(11, Cons(11, Nil))
      #|
    ),
  )
}

///|
test "a function performing a handled effect cannot leave its try" {
  inspect(
    @mbtpp.check_source(
      "t.mbtpp",
      (
        #|effect Ask {
        #|  Ask() -> Int
        #|}
        #|fn leak() -> (Unit) -> Int!Ask {
        #|  try { (_u : Unit) => perform Ask() } catch { Ask() => resume(1) }
        #|}
      ),
    ),
    content=(
      #|t.mbtpp:5:3: error: the result of this try has the type (Unit) -> Int!Ask, which performs Ask: a function performing an effect cannot leave the try that handles it
    ),
  )
}

///|
test "let mut variables are not refined by patterns" {
  inspect(
    @mbtpp.run_source(
      "t.mbtpp",
      (
        #|fn f(n : Int) -> String {
        #|  let mut x = n
        #|  match x {
        #|    0 => { x = 1; match x { 1 => "one"; _ => "other" } }
        #|    _ => "nonzero"
        #|  }
        #|}
        #|fn main {
        #|  println(f(0))
        #|  let opt : Option[Int] = Some(1)
        #|  match opt { None => println("n"); Some(a) => println(a) }
        #|}
      ),
    ),
    content=(
      #|one
      #|1
      #|
    ),
  )
}

///|
test "with abstracts the hypotheses too" {
  inspect(
    @mbtpp.check_source(
      "t.mbtpp",
      (
        #|lemma l(x : Int, h : (x <= 3) === true) -> (x <= 3) === true {
        #|  match x <= 3 { true => Refl; false => h }
        #|}
        #|fn g(n : Int) -> Int { if n > 0 { 1 } else { 0 } }
        #|lemma l0(n : Int) -> g(n) * g(n) === g(n) {
        #|  match n > 0 { true => Refl; false => Refl }
        #|}
      ),
    ),
    content=(
      #|ok
    ),
  )
}

///|
test "an implicit proposition must be a proposition" {
  inspect(
    @mbtpp.check_source(
      "t.mbtpp",
      (
        #|enum Void {}
        #|lemma pi[A : Prop](x : A, y : A) -> x === y { Refl }
        #|lemma tf(p : true === false) -> Void { match p {} }
        #|lemma bad() -> Void { tf(pi(true, false)) }
      ),
    ),
    content=(
      #|t.mbtpp:4:28: error: expected a proposition (a type in Prop), got Bool
    ),
  )
}

///|
test "floating-point literals are compared by their bits" {
  inspect(
    @mbtpp.check_source(
      "t.mbtpp",
      (
        #|lemma nan() -> 0.0 / 0.0 === 0.0 / 0.0 { Refl }
        #|lemma zero() -> -0.0 === 0.0 { Refl }
      ),
    ),
    content=(
      #|t.mbtpp:2:32: error: type mismatch
      #|  expected: 0 === 0
      #|  actual:   ?870(_) === ?870(_)
    ),
  )
}

///|
test "loop variables are fresh in each iteration" {
  inspect(
    @mbtpp.run_source(
      "t.mbtpp",
      (
        #|fn main {
        #|  let fs : Array[() -> Int] = []
        #|  for i = 0; i < 3; i = i + 1 { fs.push(() => i) }
        #|  let mut s = ""
        #|  for f in fs { s = s + f().to_string() }
        #|  println(s)
        #|  println(fs[0]())
        #|}
      ),
    ),
    content=(
      #|012
      #|0
      #|
    ),
  )
}

///|
test "literals and precedence as in MoonBit" {
  inspect(
    @mbtpp.run_source(
      "t.mbtpp",
      (
        #|fn main {
        #|  println(0.3)
        #|  println(1.0e20)
        #|  println(2.5e-3)
        #|  println(-2147483648)
        #|  let s = "x"
        #|  println("a\{ s + "}" }b")
        #|  println((6 & 3) == 2)
        #|}
      ),
    ),
    content=(
      #|0.3
      #|100000000000000000000
      #|0.0025
      #|-2147483648
      #|ax}b
      #|true
      #|
    ),
  )
  inspect(
    @mbtpp.check_source("t.mbtpp", "fn f() -> Int { 3000000000 }"),
    content=(
      #|t.mbtpp:1:17: parse error: the integer literal 3000000000 is out of range for Int
    ),
  )
  inspect(
    @mbtpp.check_source("t.mbtpp", "fn f() -> Bool { 1 | 2 == 3 }"),
    content=(
      #|t.mbtpp:1:24: error: type mismatch
      #|  expected: Int
      #|  actual:   Bool
    ),
  )
  inspect(
    @mbtpp.check_source("t.mbtpp", "fn f() -> Byte { b'\\xZZ' }"),
    content=(
      #|t.mbtpp:1:18: parse error: expected two hexadecimal digits after \x
    ),
  )
  inspect(
    @mbtpp.check_source("t.mbtpp", "fn f() -> String { \"abc\\"),
    content=(
      #|t.mbtpp:1:20: parse error: unterminated string literal
    ),
  )
}

///|
test "check-time execution: inline lambdas, aborts, attribute order" {
  inspect(
    @mbtpp.check_source(
      "t.mbtpp",
      (
        #|fn once(f : (Int) -> Unit) -> Unit { f(1) }
        #|fn d() -> Int { let mut s = 0; once(x => { s = s + x }); s }
        #|lemma ld() -> d() === 1 { Refl }
        #|#opaque
        #|fn sq(n : Int) -> Int { n * n }
        #|#unfold(sq)
        #|#timelimit(5)
        #|lemma b() -> sq(3) === 9 { Refl }
        #|fn k() -> Int { let _u : Int = abort("boom"); 5 }
        #|lemma lk() -> k() === 5 { Refl }
      ),
    ),
    content=(
      #|t.mbtpp:10:27: error: type mismatch
      #|  expected: k(()) === 5
      #|  actual:   ?875(_) === ?875(_)
    ),
  )
}
