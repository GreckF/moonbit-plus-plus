///|
/// Programs using the MoonBit syntax that must be rejected, with the
/// reason, and run-time failures.

///|
test "break with a value outside of a loop" {
  inspect(
    check("fn f() -> Int { break 1 }"),
    content=(
      #|t.mbtpp:1:17: error: `break` with a value can only leave a `for`, `while` or `loop`
    ),
  )
}

///|
test "a label that no loop has" {
  inspect(
    check(
      (
        #|fn f() -> Unit {
        #|  outer~: for i = 0; i < 3; i = i + 1 {
        #|    break inner~
        #|  }
        #|}
      ),
    ),
    content=(
      #|t.mbtpp:3:5: error: no enclosing loop has the label inner~
    ),
  )
}

///|
test "continue with values outside of a loop expression" {
  inspect(
    check(
      (
        #|fn f() -> Unit {
        #|  while true { continue 1 }
        #|}
      ),
    ),
    content=(
      #|t.mbtpp:2:16: error: `continue` with values can only be used in a `loop`
    ),
  )
}

///|
test "the arms of a loop expression must cover its values" {
  inspect(
    check(
      (
        #|fn f(n : Int) -> Int {
        #|  loop n, 0 {
        #|    0, acc => acc
        #|  }
        #|}
      ),
    ),
    content=(
      #|t.mbtpp:2:3: error: match is not exhaustive; missing case(s):
      #|  (_, _)
    ),
  )
}

///|
test "a recursive local function cannot use a mutable variable" {
  inspect(
    check(
      (
        #|fn f(n : Int) -> Int {
        #|  let mut total = 0
        #|  fn go(k : Int) -> Int { if k == 0 { total } else { go(k - 1) } }
        #|  go(n)
        #|}
      ),
    ),
    content=(
      #|t.mbtpp:3:3: error: the recursive local function go cannot use the mutable variable total
    ),
  )
}

///|
test "defer takes a Unit expression" {
  inspect(
    check(
      (
        #|fn f() -> Int {
        #|  defer 1
        #|  2
        #|}
      ),
    ),
    content=(
      #|t.mbtpp:2:9: error: type mismatch
      #|  expected: Unit
      #|  actual:   Int
    ),
  )
}

///|
test "is does not bind in the else branch" {
  inspect(
    check(
      (
        #|fn f(o : Option[Int]) -> Int {
        #|  if o is Some(x) { x } else { x }
        #|}
      ),
    ),
    content=(
      #|t.mbtpp:2:32: error: unknown name x
    ),
  )
}

///|
test "guard does not bind in its else block" {
  inspect(
    check(
      (
        #|fn f(o : Option[Int]) -> Int {
        #|  guard o is Some(x) else { return x }
        #|  x
        #|}
      ),
    ),
    content=(
      #|t.mbtpp:2:36: error: unknown name x
    ),
  )
}

///|
test "the alternatives of a nested or-pattern bind the same variables" {
  inspect(
    check(
      (
        #|fn f(o : Option[(Int, Int)]) -> Int {
        #|  match o { Some((x, 0) | (0, y)) => 1; _ => 0 }
        #|}
      ),
    ),
    content=(
      #|t.mbtpp:2:25: error: the alternatives of an or-pattern must bind the same variables
    ),
  )
}

///|
test "a guarded arm does not make a match exhaustive" {
  inspect(
    check(
      (
        #|fn f(o : Option[Int]) -> Int {
        #|  match o { Some(x) if x > 0 => x; None => 0 }
        #|}
      ),
    ),
    content=(
      #|t.mbtpp:2:3: error: match is not exhaustive; missing case(s):
      #|  Some(_)
    ),
  )
}

///|
test "an array pattern in a let fails at run time when it does not match" {
  // as in MoonBit, a refutable `let` is accepted
  inspect(
    @mbtpp.run_source(
      "t.mbtpp",
      (
        #|fn f(xs : Array[Int]) -> Int { let [a, b] = xs; a + b }
        #|fn main { println(f([1, 2])); println(f([1])) }
      ),
    ),
    content=(
      #|3
      #|runtime error: no case of the match applies
    ),
  )
}

///|
test "a range pattern is between literals" {
  inspect(
    check("fn f(n : Int, k : Int) -> Int { match n { 0..=k => 1; _ => 0 } }"),
    content=(
      #|t.mbtpp:1:47: parse error: a range pattern is between literals
    ),
  )
}

///|
test "an array pattern has one rest" {
  inspect(
    check(
      "fn f(xs : Array[Int]) -> Int { match xs { [.., a, ..] => a; _ => 0 } }",
    ),
    content=(
      #|t.mbtpp:1:51: parse error: an array pattern has at most one `..`
    ),
  )
}

///|
test "only mutable fields can be assigned" {
  inspect(
    check(
      (
        #|struct P { x : Int; mut y : Int }
        #|fn f(p : P) -> Unit { p.x = 1 }
      ),
    ),
    content=(
      #|t.mbtpp:2:23: error: the field x is not mutable
    ),
  )
}

///|
test "a mutable field is not matched by a pattern" {
  inspect(
    check(
      (
        #|struct P { x : Int; mut y : Int }
        #|fn f(p : P) -> Int { match p { { x, y } => x + y } }
      ),
    ),
    content=(
      #|t.mbtpp:2:32: error: a pattern cannot look into the mutable field y
    ),
  )
}

///|
test "a struct pattern names all fields or has .." {
  inspect(
    check(
      (
        #|struct P { x : Int; y : Int }
        #|fn f(p : P) -> Int { match p { { x } => x } }
      ),
    ),
    content=(
      #|t.mbtpp:2:32: error: missing field y in the pattern (add `..` to omit it)
    ),
  )
}

///|
test "a struct pattern names existing fields" {
  inspect(
    check(
      (
        #|struct P { x : Int; y : Int }
        #|fn f(p : P) -> Int { match p { { z, .. } => z } }
      ),
    ),
    content=(
      #|t.mbtpp:2:32: error: struct P has no field z
    ),
  )
}

///|
test "a record update needs a struct" {
  inspect(
    check("fn f(n : Int) -> Int { { ..n, x: 1 } }"),
    content=(
      #|t.mbtpp:1:24: error: `..` needs a struct, not Int
    ),
  )
}

///|
test "a tuple struct is built with all its fields" {
  inspect(
    check(
      (
        #|struct P(Int, Int)
        #|fn f() -> P { P(1) }
      ),
    ),
    content=(
      #|t.mbtpp:2:16: error: expected 2 argument(s), got 1
    ),
  )
}

///|
test "a labelled field that the constructor does not have" {
  inspect(
    check(
      (
        #|enum S { R(w~ : Int) }
        #|fn f(s : S) -> Int { match s { R(h~) => h } }
      ),
    ),
    content=(
      #|t.mbtpp:2:34: error: R has no field labelled h
    ),
  )
}

///|
test "an impl without a method that has no default" {
  inspect(
    check(
      (
        #|trait T { a(Self) -> Int; b(Self) -> Int = _ }
        #|impl T with b(_) { 0 }
        #|impl T for Int
      ),
    ),
    content=(
      #|t.mbtpp:3:1: error: missing method a in impl of T
    ),
  )
}

///|
test "numeric types do not mix" {
  inspect(
    check("fn f() -> Int64 { 1L + 1 }"),
    content=(
      #|t.mbtpp:1:24: error: type mismatch
      #|  expected: Int64
      #|  actual:   Int
    ),
  )
  inspect(
    check("fn f() -> Int { 0xFFU }"),
    content=(
      #|t.mbtpp:1:17: error: type mismatch
      #|  expected: Int
      #|  actual:   UInt
    ),
  )
}

///|
test "the keys of a map literal have one type" {
  inspect(
    check("fn f() -> Unit { let m = { \"a\": 1, 2: 3 }; () }"),
    content=(
      #|t.mbtpp:1:36: error: type mismatch
      #|  expected: (String, Int)
      #|  actual:   (Int, Int)
    ),
  )
}

///|
test "a time limit is a positive number of seconds" {
  inspect(
    check("#timelimit(0)\nfn f() -> Int { 1 }"),
    content=(
      #|t.mbtpp:1:12: parse error: a time limit is a positive number of seconds or `none`
    ),
  )
}

///|
test "division by zero fails at run time" {
  inspect(
    @mbtpp.run_source("t.mbtpp", "fn main { let z = 0L; println(1L / z) }"),
    content=(
      #|runtime error: division by zero
    ),
  )
  inspect(
    @mbtpp.run_source(
      "t.mbtpp", "fn main { let m = { 1: 2 }; println(m.get(1)); println(m[2]) }",
    ),
    content=(
      #|Some(2)
      #|None
      #|
    ),
  )
}

///|
test "a failed guard statement aborts" {
  inspect(
    @mbtpp.run_source(
      "t.mbtpp",
      (
        #|fn f(o : Option[Int]) -> Int { guard o is Some(x); x }
        #|fn main { println(f(Some(1))); println(f(None)) }
      ),
    ),
    content=(
      #|1
      #|runtime error: guard failed
    ),
  )
}

///|
test "a match on an array that no arm covers aborts" {
  inspect(
    @mbtpp.run_source(
      "t.mbtpp",
      (
        #|fn f(xs : Array[Int]) -> Int { match xs { [a] => a; [a, b] => a + b } }
        #|fn main { println(f([1, 2])); println(f([])) }
      ),
    ),
    content=(
      #|3
      #|runtime error: no case of the match applies
    ),
  )
}

///|
test "an async function passed to a function makes the call async" {
  inspect(
    check(
      (
        #|async fn g(x : Int) -> Int noraise { x }
        #|fn apply(f : (Int) -> Int) -> Int { f(1) }
        #|fn h() -> Int { apply(g) }
      ),
    ),
    content=(
      #|t.mbtpp:3:22: error: this calls an async function, which can only be done in an async function
    ),
  )
}

///|
test "break does not cross a lambda" {
  inspect(
    check(
      (
        #|fn f(xs : Array[Int]) -> Unit {
        #|  for x in xs {
        #|    let g = (y : Int) => { if y > 0 { break }; () }
        #|    g(x)
        #|  }
        #|}
      ),
    ),
    content=(
      #|t.mbtpp:3:39: error: break/continue outside of a loop
    ),
  )
}

///|
test "continue of a loop expression gives all its values" {
  inspect(
    check(
      (
        #|fn f(n : Int) -> Int {
        #|  loop n, 0 {
        #|    0, acc => acc
        #|    k, acc => continue k - 1
        #|  }
        #|}
      ),
    ),
    content=(
      #|t.mbtpp:4:26: error: type mismatch
      #|  expected: (Int, Int)
      #|  actual:   Int
    ),
  )
}
