///|
/// Behaviour of the MoonBit syntax: each program prints what MoonBit would.
fn run(src : String) -> String {
  @mbtpp.run_source("t.mbtpp", src)
}

///|
/// Run the `test` blocks of a program: one line per test.
fn run_tests(src : String) -> String {
  @parser.test_names.clear()
  @tt.check_program("t.mbtpp", src) catch {
    @tt.CheckError(msg) => return msg
  }
  let out : Array[String] = []
  for name, display in @parser.test_names {
    let res = try {
      @interp.run_global(name, _ => ())
      "ok"
    } catch {
      @interp.RunError(msg) => "failed: " + msg
    }
    out.push(display + ": " + res)
  }
  out.join("\n")
}

///|
test "guards are tried in order and fall through" {
  inspect(
    run(
      (
        #|fn f(n : Int) -> String {
        #|  match n {
        #|    x if x > 10 => "big"
        #|    x if x > 5 => "medium"
        #|    0 => "zero"
        #|    _ => "small"
        #|  }
        #|}
        #|fn main { println(f(11) + " " + f(6) + " " + f(0) + " " + f(3)) }
      ),
    ),
    content="big medium zero small\n",
  )
}

///|
test "nested or-patterns bind in every alternative" {
  inspect(
    run(
      (
        #|enum E { A(Int); B(Int); C }
        #|fn f(o : Option[E]) -> Int {
        #|  match o {
        #|    Some(A(x) | B(x)) => x
        #|    Some(C) | None => -1
        #|  }
        #|}
        #|fn main { println("\{f(Some(A(1)))} \{f(Some(B(2)))} \{f(Some(C))} \{f(None)}") }
      ),
    ),
    content="1 2 -1 -1\n",
  )
}

///|
test "is binds only where the test succeeded" {
  inspect(
    run(
      (
        #|fn f(a : Option[Int], b : Option[Int]) -> Int {
        #|  if a is Some(x) && b is Some(y) && x < y { y - x } else { 0 }
        #|}
        #|fn main { println("\{f(Some(1), Some(5))} \{f(Some(5), Some(1))} \{f(None, Some(1))}") }
      ),
    ),
    content="4 0 0\n",
  )
}

///|
test "guard keeps the bindings for the rest of the block" {
  inspect(
    run(
      (
        #|fn second(xs : List[Int]) -> Int {
        #|  guard xs is Cons(_, rest) else { return -1 }
        #|  guard rest is Cons(y, _) else { return -2 }
        #|  y
        #|}
        #|fn main { println("\{second(Nil)} \{second(Cons(1, Nil))} \{second(Cons(1, Cons(2, Nil)))}") }
      ),
    ),
    content="-1 -2 2\n",
  )
}

///|
test "noraise only runs without an error, and its errors are not caught" {
  inspect(
    run(
      (
        #|suberror E { E(Int) }
        #|fn g(n : Int) -> Int raise E { if n < 0 { raise E(n) }; n }
        #|fn f(n : Int) -> Int raise E {
        #|  try g(n) catch { E(k) => k * 10 } noraise { v => if v == 7 { raise E(99) } else { v + 1 } }
        #|}
        #|fn main {
        #|  println(try { f(1) } catch { E(k) => -k })
        #|  println(try { f(-2) } catch { E(k) => -k })
        #|  println(try { f(7) } catch { E(k) => -k })
        #|}
      ),
    ),
    content="2\n-20\n-99\n",
  )
}

///|
test "labelled continue goes on with the outer loop" {
  inspect(
    run(
      (
        #|fn main {
        #|  let out : Array[String] = []
        #|  outer~: for i = 0; i < 3; i = i + 1 {
        #|    for j = 0; j < 3; j = j + 1 {
        #|      if j > i { continue outer~ }
        #|      out.push("\{i}\{j}")
        #|    }
        #|  }
        #|  println(out)
        #|}
      ),
    ),
    content="[00, 10, 11, 20, 21, 22]\n",
  )
}

///|
test "break with a value from a nested loop, through a label" {
  inspect(
    run(
      (
        #|fn find(n : Int) -> (Int, Int) {
        #|  outer~: for i = 1; i < n; i = i + 1 {
        #|    for j = i; j < n; j = j + 1 {
        #|      if i * j == 12 { break outer~ (i, j) }
        #|    }
        #|  } nobreak {
        #|    (0, 0)
        #|  }
        #|}
        #|fn main {
        #|  let (a, b) = find(10)
        #|  let (c, d) = find(3)
        #|  println("\{a} \{b} \{c} \{d}")
        #|}
      ),
    ),
    content="2 6 0 0\n",
  )
}

///|
test "loop with guards and several values" {
  inspect(
    run(
      (
        #|fn gcd(a : Int, b : Int) -> Int {
        #|  loop a, b {
        #|    x, 0 => x
        #|    x, y if x < y => continue y, x
        #|    x, y => continue y, x % y
        #|  }
        #|}
        #|fn main { println("\{gcd(12, 18)} \{gcd(7, 5)} \{gcd(0, 4)}") }
      ),
    ),
    content="6 1 4\n",
  )
}

///|
test "defers run in reverse order, also on errors" {
  inspect(
    run(
      (
        #|fn f(fail : Bool) -> Int raise Failure {
        #|  defer println("first")
        #|  defer println("second")
        #|  if fail { raise Failure("boom") }
        #|  1
        #|}
        #|fn main {
        #|  println(try { f(false) } catch { _ => 0 })
        #|  println(try { f(true) } catch { _ => 0 })
        #|}
      ),
    ),
    content="second\nfirst\n1\nsecond\nfirst\n0\n",
  )
}

///|
test "a recursive local function sees the variables around it" {
  inspect(
    run(
      (
        #|fn powers(base : Int, n : Int) -> List[Int] {
        #|  fn go(k : Int, acc : Int) -> List[Int] {
        #|    if k == n { Nil } else { Cons(acc, go(k + 1, acc * base)) }
        #|  }
        #|  go(0, 1)
        #|}
        #|fn main { println(powers(3, 4)) }
      ),
    ),
    content="Cons(1, Cons(3, Cons(9, Cons(27, Nil))))\n",
  )
}

///|
test "array patterns: exact length, rest and suffix" {
  inspect(
    run(
      (
        #|fn f(xs : Array[Int]) -> String {
        #|  match xs {
        #|    [] => "empty"
        #|    [_] => "one"
        #|    [a, b] => "two \{a + b}"
        #|    [first, .. middle, last] => "\{first}..\{last} (\{middle.length()} inside)"
        #|  }
        #|}
        #|fn main {
        #|  println(f([]))
        #|  println(f([1]))
        #|  println(f([1, 2]))
        #|  println(f([1, 2, 3, 4]))
        #|}
      ),
    ),
    content="empty\none\ntwo 3\n1..4 (2 inside)\n",
  )
}

///|
test "array patterns on strings" {
  inspect(
    run(
      (
        #|fn f(s : String) -> String {
        #|  match s {
        #|    ['#', .. rest] => "comment: " + rest
        #|    [] => "empty"
        #|    _ => "other"
        #|  }
        #|}
        #|fn main { println(f("#hi")); println(f("")); println(f("x")) }
      ),
    ),
    content="comment: hi\nempty\nother\n",
  )
}

///|
test "range patterns: bounds included or not" {
  inspect(
    run(
      (
        #|fn f(n : Int) -> String {
        #|  match n {
        #|    _..<0 => "neg"
        #|    0..<10 => "digit"
        #|    10..=10 => "ten"
        #|    _ => "big"
        #|  }
        #|}
        #|fn main { println(f(-1) + f(0) + f(9) + f(10) + f(11)) }
      ),
    ),
    content="negdigitdigittenbig\n",
  )
}

///|
test "mutable fields are shared, updates copy them" {
  inspect(
    run(
      (
        #|struct Cell { mut v : Int; tag : String }
        #|fn bump(c : Cell) -> Unit { c.v += 1 }
        #|fn main {
        #|  let a = { v: 0, tag: "a" }
        #|  let b = a
        #|  bump(a)
        #|  bump(b)
        #|  let c = { ..a, tag: "c" }
        #|  bump(c)
        #|  println("\{a.v} \{b.v} \{c.v} \{c.tag}")
        #|}
      ),
    ),
    content="2 2 3 c\n",
  )
}

///|
test "tuple structs and newtypes" {
  inspect(
    run(
      (
        #|struct Pair(Int, String)
        #|type Id Int
        #|fn swap_id(p : Pair) -> Id { Id(p.0 + 1) }
        #|fn main {
        #|  let p = Pair(41, "x")
        #|  match p { Pair(n, s) => println(s + n.to_string()) }
        #|  println(swap_id(p).0)
        #|}
      ),
    ),
    content="x41\n42\n",
  )
}

///|
test "labelled constructor fields in any order" {
  inspect(
    run(
      (
        #|enum Shape { Rect(w~ : Int, h~ : Int) }
        #|fn area(s : Shape) -> Int { match s { Rect(h~, w~) => w * h } }
        #|fn wide(s : Shape) -> Bool { match s { Rect(w=10, ..) => true; _ => false } }
        #|fn main {
        #|  println(area(Rect(h=2, w=3)))
        #|  println("\{wide(Rect(w=10, h=1))} \{wide(Rect(w=9, h=1))}")
        #|}
      ),
    ),
    content="6\ntrue false\n",
  )
}

///|
test "default methods can be overridden" {
  inspect(
    run(
      (
        #|trait Greet { name(Self) -> String; hello(Self) -> String = _ }
        #|impl Greet with hello(self) { "hello " + self.name() }
        #|impl Greet for Int with name(self) { "n" + self.to_string() }
        #|impl Greet for Bool with name(_) { "b" }
        #|impl Greet for Bool with hello(_) { "hi" }
        #|fn main { println((1).hello() + ", " + true.hello()) }
      ),
    ),
    content="hello n1, hi\n",
  )
}

///|
test "numbers wrap around like MoonBit's" {
  inspect(
    run(
      (
        #|fn main {
        #|  println(0U - 1U)
        #|  println(9223372036854775807L + 1L)
        #|  println((255).to_byte() + (1).to_byte())
        #|  println(18446744073709551615UL + 1UL)
        #|  println(-7L / 2L)
        #|  println(-7L % 2L)
        #|  println(1L << 40)
        #|}
      ),
    ),
    content="4294967295\n-9223372036854775808\nb'\\x00'\n0\n-3\n-1\n1099511627776\n",
  )
}

///|
test "conversions between numeric types" {
  inspect(
    run(
      (
        #|fn main {
        #|  println((-1).to_uint())
        #|  println((300).to_byte().to_int())
        #|  println((1L << 33).to_int())
        #|  println((7).to_float().to_double() / 2.0)
        #|  println(b'A'.to_int())
        #|}
      ),
    ),
    content="4294967295\n44\n0\n3.5\n65\n",
  )
}

///|
test "maps keep the order of their keys" {
  inspect(
    run(
      (
        #|fn main {
        #|  let m = { "b": 1, "a": 2 }
        #|  m["c"] = 3
        #|  m["b"] = 10
        #|  m.remove("a")
        #|  println(m)
        #|  println("\{m.length()} \{m.contains("a")} \{m.get("c")}")
        #|  let keys : Array[String] = []
        #|  for k, v in m { keys.push(k + v.to_string()) }
        #|  println(keys)
        #|  let empty : Map[Int, Int] = {}
        #|  println("\{empty.is_empty()} \{empty[1]}")
        #|}
      ),
    ),
    content="{b: 10, c: 3}\n2 false Some(3)\n[b10, c3]\n" + "true None\n",
  )
}

///|
test "multiline strings keep their lines" {
  inspect(
    run(
      (
        #|fn main {
        #|  let n = 2
        #|  let s =
        #|    #|raw \{n} \n
        #|    $|interpolated \{n + 1}
        #|  println(s)
        #|}
      ),
    ),
    content="raw \\{n} \\n\ninterpolated 3\n",
  )
}

///|
test "test blocks: each test runs on its own" {
  inspect(
    run_tests(
      (
        #|fn inc(x : Int) -> Int { x + 1 }
        #|test "passes" { assert_eq(inc(1), 2) }
        #|test "fails" { assert_eq(inc(1), 3) }
        #|test "raises" { assert_true(inc(0) == 0) }
        #|test "not equal" { assert_not_eq(inc(1), 3) }
      ),
    ),
    content=(
      #|passes: ok
      #|fails: failed: uncaught error: Failure("`2 == 3`")
      #|raises: failed: uncaught error: Failure("`true` expected")
      #|not equal: ok
    ),
  )
}

///|
test "functions with loops compute in types" {
  inspect(
    @mbtpp.check_source(
      "t.mbtpp",
      (
        #|fn fact(n : Int) -> Int {
        #|  let mut acc = 1
        #|  for i = 2; i <= n; i = i + 1 { acc = acc * i }
        #|  acc
        #|}
        #|fn first_square_over(n : Int) -> Int {
        #|  loop 1 { k if k * k > n => k; k => continue k + 1 }
        #|}
        #|lemma a : fact(5) === 120 = Refl
        #|lemma b : first_square_over(50) === 8 = Refl
        #|fn main { let v : Array[Int] = Array::make(fact(3), 0); println(v.length()) }
      ),
    ),
    content="ok",
  )
}
