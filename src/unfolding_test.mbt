///|
/// Controlled unfolding (see doc/mbtpp/unfolding.md).

///|
let plus_src : String =
  #|#opaque
  #|fn plus(m : Nat, n : Nat) -> Nat {
  #|  match m {
  #|    Z => n
  #|    S(k) => S(plus(k, n))
  #|  }
  #|}
  #|

///|
test "an opaque function is not unfolded" {
  inspect(
    check_source(
      "t.mbtpp",
      plus_src +
      (
        #|lemma bad() -> plus(1, 1) === 2 { Refl }
      ),
    ),
    content=(
      #|t.mbtpp:8:35: error: type mismatch
      #|  expected: plus(1, 1) === 2
      #|  actual:   ?868(_) === ?868(_)
      #|hint: plus is opaque here; if the definition is needed, add #unfold(plus) to the declaration, or use unfold(plus) { … }
    ),
  )
}

///|
test "unfolding by declaration, block and tactic" {
  inspect(
    run_source(
      "t.mbtpp",
      plus_src +
      (
        #|#unfold(plus)
        #|lemma plus_z(n : Nat) -> plus(Z, n) === n { Refl }
        #|
        #|#unfold(plus)
        #|lemma plus_s(m : Nat, n : Nat) -> plus(S(m), n) === S(plus(m, n)) { Refl }
        #|
        #|// only the lemmas
        #|lemma plus_zero(n : Nat) -> plus(n, Z) === n {
        #|  match n {
        #|    Z => plus_z(Z)
        #|    S(k) => Id::trans(plus_s(k, Z), Id::cong(S, plus_zero(k)))
        #|  }
        #|}
        #|
        #|lemma two() -> plus(1, 1) === 2 { unfold(plus) { Refl } }
        #|
        #|lemma two_t : plus(1, 1) === 2 = proof {
        #|  unfold plus
        #|  rfl
        #|}
        #|
        #|fn main { println(plus(2, 3).to_int()) }
      ),
    ),
    content=(
      #|5
      #|
    ),
  )
}

///|
test "unfolding is transitive" {
  inspect(
    run_source(
      "t.mbtpp",
      plus_src +
      (
        #|enum Vec[T] : Nat -> Type {
        #|  VNil : Vec[T](0)
        #|  VCons[n : Nat](T, Vec[T](n)) : Vec[T](S(n))
        #|}
        #|
        #|#opaque
        #|#unfold(plus)
        #|fn[T, m : Nat, n : Nat] app(u : Vec[T](m), v : Vec[T](n)) -> Vec[T](plus(m, n)) {
        #|  match u {
        #|    VNil => v
        #|    VCons(x, r) => VCons(x, app(r, v))
        #|  }
        #|}
        #|
        #|// unfolding app unfolds plus too
        #|#unfold(app)
        #|lemma app_nil[T, n : Nat](v : Vec[T](n)) -> app(VNil, v) === unfold(plus) { v } {
        #|  Refl
        #|}
        #|
        #|fn main {
        #|  println(unfold(plus) { app(VCons(1, VNil), VCons(2, VNil)) is VCons(1, _) })
        #|}
      ),
    ),
    content=(
      #|true
      #|
    ),
  )
}

///|
test "a transparent function that unfolds an opaque one" {
  inspect(
    check_source(
      "t.mbtpp",
      plus_src +
      (
        #|#unfold(plus)
        #|fn double(n : Nat) -> Nat { plus(n, n) }
        #|
        #|lemma ok() -> double(1) === 2 { unfold(plus) { Refl } }
        #|lemma bad() -> double(1) === 2 { Refl }
      ),
    ),
    content=(
      #|t.mbtpp:12:34: error: type mismatch
      #|  expected: double(1) === 2
      #|  actual:   ?870(_) === ?870(_)
      #|hint: plus is opaque here; if the definition is needed, add #unfold(plus) to the declaration, or use unfold(plus) { … }
    ),
  )
}

///|
test "an opaque function is not run during checking" {
  let src =
    #|#opaque
    #|fn sum_to(n : Int) -> Int {
    #|  let mut acc = 0
    #|  for i = 1; i <= n; i = i + 1 { acc = acc + i }
    #|  acc
    #|}
    #|
  inspect(
    check_source(
      "t.mbtpp",
      src +
      (
        #|#unfold(sum_to)
        #|lemma ok() -> sum_to(10) === 55 { Refl }
        #|lemma bad() -> sum_to(10) === 55 { Refl }
      ),
    ),
    content=(
      #|t.mbtpp:9:36: error: type mismatch
      #|  expected: sum_to(10) === 55
      #|  actual:   ?870(_) === ?870(_)
      #|hint: sum_to is opaque here; if the definition is needed, add #unfold(sum_to) to the declaration, or use unfold(sum_to) { … }
    ),
  )
}

///|
test "names that cannot be unfolded" {
  let src =
    #|#opaque(sealed)
    #|fn secret(n : Nat) -> Nat {
    #|  match n { Z => Z; S(k) => secret(k) }
    #|}
    #|
  inspect(
    check_source(
      "t.mbtpp",
      src +
      (
        #|#unfold(secret)
        #|lemma x() -> secret(1) === 0 { Refl }
      ),
    ),
    content=(
      #|t.mbtpp:5:9: error: secret is #opaque(sealed): it cannot be unfolded
    ),
  )
  inspect(
    check_source(
      "t.mbtpp",
      (
        #|lemma x() -> 1 === 1 { unfold(nosuch) { Refl } }
      ),
    ),
    content=(
      #|t.mbtpp:1:31: error: unknown function nosuch
    ),
  )
  inspect(
    check_source(
      "t.mbtpp",
      (
        #|#opaque
        #|enum E { A }
      ),
    ),
    content=(
      #|t.mbtpp:1:1: parse error: #opaque applies to functions and lemmas
    ),
  )
}
