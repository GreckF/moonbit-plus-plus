///|
fn run_example(name : String) -> String {
  let path = "examples/" + name
  let src = @fs.read_file_to_string(path) catch {
    @fs.IOError(msg) => return msg
  }
  run_source(path, src)
}

///|
test "example basic" {
  inspect(run_example("basic.mbtpp"), content="3\n")
}

///|
test "example vector" {
  inspect(
    run_example("vector.mbtpp"),
    content=(
      #|1
      #|2
      #|Cons(1, Cons(2, Cons(3, Cons(10, Cons(20, Cons(30, Nil))))))
      #|true
      #|
    ),
  )
}

///|
test "example struct_proof" {
  inspect(
    run_example("struct_proof.mbtpp"),
    content=(
      #|2
      #|[1, 2, 3]
      #|
    ),
  )
}

///|
test "example monad" {
  inspect(
    run_example("monad.mbtpp"),
    content=(
      #|Some(3)
      #|None
      #|Cons(10, Cons(20, Cons(20, Cons(40, Nil))))
      #|None
      #|
    ),
  )
}

///|
test "example errors" {
  inspect(
    run_example("errors.mbtpp"),
    content=(
      #|caught: division by zero
      #|0
      #|Ok(5)
      #|5050
      #|8
      #|i = 6
      #|0 42 0 
      #|
    ),
  )
}

///|
test "example dependent" {
  inspect(
    run_example("dependent.mbtpp"),
    content=(
      #|6
      #|2
      #|8
      #|
    ),
  )
}

///|
test "example traits" {
  inspect(
    run_example("traits.mbtpp"),
    content=(
      #|square with area 9
      #|rect with area 10
      #|square with area 4, volume 8
      #|<1><2><3>
      #|
    ),
  )
}

///|
test "example proofs" {
  inspect(
    run_example("proofs.mbtpp"),
    content=(
      #|Cons(1, Cons(2, Cons(1, Cons(2, Cons(1, Cons(2, Nil))))))
      #|Cons(1, Cons(2, Cons(3, Nil)))
      #|
    ),
  )
}

///|
test "example stlc" {
  inspect(
    run_example("stlc.mbtpp"),
    content=(
      #|tt after 1 steps
      #|tt after 2 steps
      #|tt after 2 steps
      #|(fn wk(tt)) after 1 steps
      #|((fn (#0 tt)) (fn #0)) ~> ((fn #0) tt) ~> tt
      #|(((fn (fn #1)) tt) tt) ~> ((fn wk(tt)) tt) ~> tt
      #|(fn wk(tt))
      #|
    ),
  )
}

///|
test "example labelled" {
  inspect(
    run_example("labelled.mbtpp"),
    content=(
      #|7
      #|42
      #|0
      #|10
      #|20
      #|Hello, Alice
      #|Hello, Mr. Bob
      #|Hello, Dr. Carol
      #|0
      #|10
      #|Cons(x, Cons(x, Cons(x, Nil)))
      #|
    ),
  )
}

///|
test "example mbt_types" {
  inspect(
    run_example("mbt_types.mbtpp"),
    content=(
      #|25
      #|10
      #|0
      #|2510
      #|Some(5)
      #|None
      #|4
      #|
    ),
  )
}

///|
test "example derive" {
  inspect(
    run_example("derive.mbtpp"),
    content=(
      #|Rect(1, 2)
      #|true
      #|-1
      #|Node(Leaf, 1, Node(Leaf, 2, Leaf))
      #|{x: 1, y: 2} != {x: 1, y: 3}
      #|{x: 1, y: 3}
      #|Some(3)
      #|{x: 0, y: 1}
      #|-7
      #|{x: 0, y: 0}
      #|
    ),
  )
}

///|
test "example trait_objects" {
  inspect(
    run_example("trait_objects.mbtpp"),
    content=(
      #|10
      #|circle
      #|square
      #|circle
      #|<42>
      #|<hi>
      #|1
      #|two
      #|true
      #|Some(3)
      #|#7
      #|7
      #|
    ),
  )
}

///|
test "example patterns" {
  inspect(
    run_example("patterns.mbtpp"),
    content=(
      #|polygon, big circle, circle
      #|true
      #|true false
      #|9 0 0
      #|3
      #|42 5
      #|tiny seven other
      #|6 -3
      #|ok 8, bad, very bad
      #|3
      #|
    ),
  )
}

///|
test "async functions run in the interpreter" {
  inspect(
    run_source(
      "t.mbtpp",
      (
        #|async fn twice(f : async (Int) -> Int, x : Int) -> Int { f(f(x)) }
        #|async fn inc(x : Int) -> Int noraise { x + 1 }
        #|async fn main {
        #|  let g = async fn(x : Int) -> Int { inc(x) * 2 }
        #|  println(twice(g, 1))
        #|  println(twice(x => inc(x), 5))
        #|}
      ),
    ),
    content=(
      #|10
      #|7
      #|
    ),
  )
}

///|
test "example syntax" {
  inspect(
    run_example("syntax.mbtpp"),
    content=(
      #|55
      #|2 -1
      #|2 * 6
      #|55
      #|cleanup 3
      #|6
      #|cleanup 0
      #|-1
      #|same ends around 2
      #|starts with 4
      #|lower upper digit
      #|2
      #|280
      #|two lines,
      #|the second with 6
      #|
    ),
  )
}

///|
test "example data" {
  inspect(
    run_example("data.mbtpp"),
    content=(
      #|clicks 12, copy 13
      #|3
      #|5
      #|7
      #|{x: 3, y: 10}
      #|13
      #|<point>
      #|
    ),
  )
}

///|
test "example numbers" {
  inspect(
    run_example("numbers.mbtpp"),
    content=(
      #|7000000000000
      #|52
      #|18446744073709551615
      #|100
      #|zero small big
      #|1.5
      #|-9223372036854775808
      #|{ann: 31, bob: 27, cy: 40}
      #|Some(27)
      #|ann 31
      #|bob 27
      #|cy 40
      #|{x: 2, y: 1}
      #|
    ),
  )
}

///|
test "example unfolding" {
  inspect(
    run_example("unfolding.mbtpp"),
    content=(
      #|7
      #|5050
      #|
    ),
  )
}

///|
test "example effects_dt" {
  inspect(
    run_example("effects_dt.mbtpp"),
    content=(
      #|http://localhost:8080
      #|4 + 5 = nine
      #|compare 1 2
      #|compare 3 1
      #|compare 3 2
      #|Cons(1, Cons(2, Cons(3, Nil)))
      #|16
      #|
    ),
  )
}

///|
test "Nat runs as a BigInt" {
  inspect(
    run_source(
      "t.mbtpp",
      (
        #|fn fact(n : Nat) -> Nat {
        #|  match n {
        #|    Z => 1
        #|    S(k) => n * fact(k)
        #|  }
        #|}
        #|
        #|fn pred2(n : Nat) -> Nat {
        #|  match n {
        #|    S(S(k)) => k
        #|    S(Z) as one => one
        #|    _ => 0
        #|  }
        #|}
        #|
        #|lemma fact3 : fact(3) === 6 = Refl
        #|
        #|fn main {
        #|  println(fact(30))
        #|  println(fact(10).to_int())
        #|  println("\{pred2(5)} \{pred2(1)} \{pred2(0)}")
        #|  println((3 : Nat) == 3)
        #|  println((2 : Nat).compare(5))
        #|  println(int_to_nat(100000) + int_to_nat(-5))
        #|  println([1, 2, 3].size())
        #|  let xs : List[Nat] = Cons((1 : Nat), Cons((2 : Nat), Nil))
        #|  println(xs.map(S))
        #|}
      ),
    ),
    content=(
      #|265252859812191058636308480000000
      #|3628800
      #|3 1 0
      #|true
      #|-1
      #|100000
      #|3
      #|Cons(2, Cons(3, Nil))
      #|
    ),
  )
}

///|
/// A literal sub-pattern refines its field in the types of the later fields
/// (bugs/001 of moonlit).
test "a literal in a constructor pattern refines the later fields" {
  inspect(
    run_source(
      "t.mbtpp",
      (
        #|enum Maybe[P : Prop] {
        #|  Yes(P)
        #|  No
        #|}
        #|
        #|enum Sing(x : Bool) {
        #|  MkSing(y : Bool, eq : x === y)
        #|}
        #|
        #|enum SingI(x : Int) {
        #|  MkSingI(y : Int, eq : x === y)
        #|}
        #|
        #|fn lit(x : Bool, s : Sing(x)) -> Maybe[x === true] {
        #|  match s {
        #|    MkSing(true, e) => Yes(e)
        #|    MkSing(false, _) => No
        #|  }
        #|}
        #|
        #|fn lit_int(x : Int, s : SingI(x)) -> Maybe[x === 0] {
        #|  match s {
        #|    MkSingI(0, e) => Yes(e)
        #|    MkSingI(_, _) => No
        #|  }
        #|}
        #|
        #|fn main {
        #|  match lit(true, MkSing(true, Refl)) {
        #|    Yes(_) => println("yes")
        #|    No => println("no")
        #|  }
        #|  match lit_int(3, MkSingI(3, Refl)) {
        #|    Yes(_) => println("yes")
        #|    No => println("no")
        #|  }
        #|}
      ),
    ),
    content=(
      #|yes
      #|no
      #|
    ),
  )
  // `_` does not know the value
  inspect(
    run_source(
      "t.mbtpp",
      (
        #|enum Maybe[P : Prop] {
        #|  Yes(P)
        #|  No
        #|}
        #|
        #|enum Sing(x : Bool) {
        #|  MkSing(y : Bool, eq : x === y)
        #|}
        #|
        #|fn lit(x : Bool, s : Sing(x)) -> Maybe[x === true] {
        #|  match s {
        #|    MkSing(_, e) => Yes(e)
        #|  }
        #|}
        #|
        #|fn main {
        #|  ()
        #|}
      ),
    ),
    content=(
      #|t.mbtpp:12:25: error: type mismatch
      #|  expected: x === true
      #|  actual:   x === _
    ),
  )
}

///|
test "Nat operations and BigInt" {
  inspect(
    run_source(
      "t.mbtpp",
      (
        #|lemma sub_ok : (7 : Nat) - 3 === 4 = Refl
        #|lemma sub_trunc : (3 : Nat) - 7 === 0 = Refl
        #|lemma div_ok : (17 : Nat) / 5 === 3 = Refl
        #|lemma mod_ok : (17 : Nat) % 5 === 2 = Refl
        #|lemma div0 : (17 : Nat) / 0 === 0 = Refl
        #|lemma gcd_ok : (12 : Nat).gcd(18) === 6 = Refl
        #|lemma land_ok : ((12 : Nat) & 10) === 8 = Refl
        #|lemma lor_ok : ((12 : Nat) | 10) === 14 = Refl
        #|lemma lxor_ok : ((12 : Nat) ^ 10) === 6 = Refl
        #|lemma shl_ok : (3 : Nat) << 2 === 12 = Refl
        #|lemma shr_ok : (13 : Nat) >> 2 === 3 = Refl
        #|lemma pow_ok : (2 : Nat).pow(5) === 32 = Refl
        #|lemma log2_ok : (9 : Nat).log2() === 3 = Refl
        #|
        #|fn main {
        #|  ()
        #|}
      ),
    ),
    content="",
  )
  inspect(
    run_source(
      "t.mbtpp",
      (
        #|fn main {
        #|  let a = int_to_nat(1000000)
        #|  let b : Nat = 7
        #|  println("\{a - b} \{b - a} \{a / b} \{a % b} \{a / 0} \{a % 0}")
        #|  println("\{a.gcd(int_to_nat(2500))} \{a & int_to_nat(255)} \{a | b} \{a ^ b}")
        #|  println(b << int_to_nat(100))
        #|  println("\{b.pow(int_to_nat(40))} \{a.log2()} \{b < a}")
        #|  println(a.to_bigint() * BigInt::from_int(-3))
        #|  println(Nat::of_bigint(BigInt::from_int(-5)))
        #|  let x = BigInt::from_int(1) << 70
        #|  println("\{x} \{x / BigInt::from_int(3)} \{-x % BigInt::from_int(1000)}")
        #|}
      ),
    ),
    content=(
      #|999993 0 142857 1 0 1000000
      #|2500 64 1000007 1000007
      #|8873554201597605810476922437632
      #|6366805760909027985741435139224001 19 true
      #|-3000000
      #|0
      #|1180591620717411303424 393530540239137101141 -424
      #|
    ),
  )
}

///|
/// Decidable equality with proofs, `derive(DecEq)`, `ptr_deq`.
test "deq, DecEq and physical equality" {
  inspect(
    run_source(
      "t.mbtpp",
      (
        #|enum Color {
        #|  Red
        #|  Rgb(Int, Int, Int)
        #|} derive(DecEq, Show)
        #|
        #|struct Key {
        #|  name : String
        #|  id : Nat
        #|} derive(DecEq)
        #|
        #|lemma int_yes : Int::deq(3, 3) === Yes(Refl) = Refl
        #|lemma int_no : (Int::deq(3, 4) is No(_)) === true = Refl
        #|lemma nat_yes : Nat::deq(5, 5) === Yes(Refl) = Refl
        #|
        #|// a value looked up by a key comes with a proof that the key is the one asked
        #|fn[K : DecEq, V] find(k : K, xs : List[(K, V)]) -> Option[V] {
        #|  match xs {
        #|    Nil => None
        #|    Cons((k2, v), rest) =>
        #|      match DecEq::deq(k, k2) {
        #|        Yes(_) => Some(v)
        #|        No(_) => find(k, rest)
        #|      }
        #|  }
        #|}
        #|
        #|fn[T] cast(p : Int::deq(1, 1) === Yes(Refl), x : T) -> T {
        #|  let _ = p
        #|  x
        #|}
        #|
        #|fn[P : Prop] yes(d : Dec[P]) -> Bool {
        #|  d is Yes(_)
        #|}
        #|
        #|fn main {
        #|  println(yes(Int::deq(3, 3)))
        #|  println(yes("ab".deq("a" + "b")))
        #|  println(yes('x'.deq('y')))
        #|  println(yes(true.deq(true)))
        #|  println(yes(().deq(())))
        #|  println(yes(int_to_nat(1000000).deq(int_to_nat(1000000))))
        #|  println(yes(BigInt::from_int(7).deq(BigInt::from_int(8))))
        #|  println(yes(DecEq::deq(Some(Cons(1, Nil)), Some(Cons(1, Nil)))))
        #|  println(yes(DecEq::deq((1, "a", true), (1, "a", false))))
        #|  println(yes(DecEq::deq(Rgb(1, 2, 3), Rgb(1, 2, 3))))
        #|  println(yes(DecEq::deq(Red, Rgb(0, 0, 0))))
        #|  println(Rgb(1, 2, 3) == Rgb(1, 2, 3))
        #|  let k : Key = { name: "a", id: 3 }
        #|  println(yes(DecEq::deq(k, { name: "a", id: 3 })))
        #|  println(k == { name: "a", id: 4 })
        #|  println(find(2, Cons((1, "one"), Cons((2, "two"), Nil))))
        #|  let xs = [1, 2]
        #|  println(physical_equal(xs, xs))
        #|  println(physical_equal(xs, [1, 2]))
        #|  println(ptr_deq(xs, xs) is Proved(_))
        #|}
      ),
    ),
    content=(
      #|true
      #|true
      #|false
      #|true
      #|true
      #|true
      #|false
      #|true
      #|false
      #|true
      #|false
      #|true
      #|true
      #|false
      #|Some(two)
      #|true
      #|false
      #|true
      #|
    ),
  )
}

///|
test "HashMap" {
  inspect(
    run_source(
      "t.mbtpp",
      (
        #|fn main {
        #|  let m : HashMap[String, Int] = {}
        #|  m["a"] = 1
        #|  m["b"] = 2
        #|  m["a"] = 3
        #|  println(m)
        #|  println("\{m["a"]} \{m["zz"]}")
        #|  m.remove("a")
        #|  println(m.contains("a"))
        #|  m["a"] = 9
        #|  for k, v in m {
        #|    println(k + "=" + v.to_string())
        #|  }
        #|  let big : HashMap[(Int, Int), Int] = HashMap::new()
        #|  for i = 0; i < 300; i = i + 1 {
        #|    big[(i, i % 7)] = i
        #|  }
        #|  for i = 0; i < 200; i = i + 2 {
        #|    big.remove((i, i % 7))
        #|  }
        #|  println("\{big.length()} \{big[(201, 201 % 7)]} \{big[(2, 2)]}")
        #|  let lit : HashMap[String, Int] = { "x": 1, "y": 2 }
        #|  println(lit)
        #|}
      ),
    ),
    content=(
      #|{a: 3, b: 2}
      #|Some(3) None
      #|false
      #|b=2
      #|a=9
      #|200 Some(201) None
      #|{x: 1, y: 2}
      #|
    ),
  )
}

///|
/// A type of the program with the name of a Prelude type replaces it, with
/// everything of the Prelude that uses it.
test "a type of the program replaces the Prelude's" {
  inspect(
    run_source(
      "t.mbtpp",
      (
        #|struct HashMap[K, V] {
        #|  mut items : Array[(K, V)]
        #|}
        #|
        #|fn[K, V] HashMap::new() -> HashMap[K, V] {
        #|  { items: [] }
        #|}
        #|
        #|fn[K : Eq, V] HashMap::set(self : HashMap[K, V], k : K, v : V) -> Unit {
        #|  self.items.push((k, v))
        #|}
        #|
        #|fn[K, V] HashMap::length(self : HashMap[K, V]) -> Int {
        #|  self.items.length()
        #|}
        #|
        #|enum Nat {
        #|  Zero
        #|  Succ(Nat, String)
        #|}
        #|
        #|fn Nat::count(self : Nat) -> Int {
        #|  match self {
        #|    Zero => 0
        #|    Succ(n, _) => n.count() + 1
        #|  }
        #|}
        #|
        #|fn main {
        #|  let m : HashMap[String, Int] = HashMap::new()
        #|  m.set("a", 1)
        #|  m.set("b", 2)
        #|  println(m.length())
        #|  println(Succ(Succ(Zero, "x"), "y").count())
        #|}
      ),
    ),
    content=(
      #|2
      #|2
      #|
    ),
  )
}

///|
/// A large `Nat` literal is not unfolded into constructors unless needed
/// (bugs/002 of moonlit).
test "large Nat literals" {
  inspect(
    run_source(
      "t.mbtpp",
      (
        #|fn f(b : Nat) -> Bool {
        #|  b > 16777216
        #|}
        #|
        #|lemma same : (1000000 : Nat) === int_to_nat(1000000) = Refl
        #|lemma small : (100 : Nat) - 98 === 2 = Refl
        #|
        #|fn main {
        #|  println(f(int_to_nat(20000000)))
        #|  let x : Nat = 1000000
        #|  println(x + 1)
        #|}
      ),
    ),
    content=(
      #|true
      #|1000001
      #|
    ),
  )
}

///|
/// The expected type determines the implicit arguments of a constructor
/// before its arguments are checked (bugs/003 of moonlit).
test "implicit arguments from the expected type" {
  inspect(
    run_source(
      "t.mbtpp",
      (
        #|fn f(n : Nat) -> Nat {
        #|  n
        #|}
        #|
        #|enum IsZ : (Nat) -> Type {
        #|  MkIsZ[n : Nat](h : f(n) === Z) : IsZ(n)
        #|}
        #|
        #|enum K2 : (Nat) -> Type {
        #|  KZero[n : Nat](k : (Nat) -> f(n) === Z) : K2(n)
        #|}
        #|
        #|fn direct() -> IsZ(Z) {
        #|  MkIsZ(Refl)
        #|}
        #|
        #|fn lam() -> K2(Z) {
        #|  KZero(_ => Refl)
        #|}
        #|
        #|fn main {
        #|  let _ = direct()
        #|  let _ = lam()
        #|  let x : K2(Z) = KZero(rho => Refl)
        #|  let _ = x
        #|  println("ok")
        #|}
      ),
    ),
    content=(
      #|ok
      #|
    ),
  )
}

///|
/// A parameter that is a function returning a proof has no effects: neither
/// the effect variable added to callbacks nor `!pure` is an error
/// (bugs/004 of moonlit).
test "callbacks returning proofs" {
  inspect(
    run_source(
      "t.mbtpp",
      (
        #|enum Box : (Nat) -> Type {
        #|  MkBox[n : Nat](e : (u : Unit) -> n === n) : Box(n)
        #|}
        #|
        #|struct Cert {
        #|  up : (rho : Int) -> rho === rho
        #|}
        #|
        #|fn use_cb(n : Nat, e : (u : Unit) -> n === n) -> Box(n) {
        #|  MkBox(e)
        #|}
        #|
        #|fn use_pure(n : Nat, e : (u : Unit) -> n === n!pure) -> Box(n) {
        #|  MkBox(e)
        #|}
        #|
        #|fn flat(c : Cert, f : (rho : Int) -> rho === rho) -> Cert {
        #|  { up: rho => match (c.up)(rho) { Refl => f(rho) } }
        #|}
        #|
        #|fn main {
        #|  match use_cb(3, _ => Refl) {
        #|    MkBox(_) => println("ok")
        #|  }
        #|  let _ = use_pure(2, _ => Refl)
        #|  let _ = flat({ up: _ => Refl }, _ => Refl)
        #|}
      ),
    ),
    content=(
      #|ok
      #|
    ),
  )
}

///|
/// `No` carries a refutation: properties of functions defined with `deq`
/// are provable on variables.
test "refutations in Dec" {
  inspect(
    run_source(
      "t.mbtpp",
      (
        #|fn upd(rho : (String) -> Nat, p : String, m : Nat) -> (String) -> Nat {
        #|  n => match String::deq(n, p) {
        #|    Yes(_) => m
        #|    No(_) => rho(n)
        #|  }
        #|}
        #|
        #|lemma upd_same(rho : (String) -> Nat, p : String, m : Nat) -> upd(rho, p, m)(p) === m {
        #|  match String::deq(p, p) {
        #|    Yes(_) => Refl
        #|    No(nope) => absurd(nope(Refl))
        #|  }
        #|}
        #|
        #|enum Color {
        #|  Red
        #|  Rgb(Int, Int, Int)
        #|} derive(DecEq)
        #|
        #|lemma color_refl(c : Color) -> (DecEq::deq(c, c) is Yes(_)) === true {
        #|  match DecEq::deq(c, c) {
        #|    Yes(_) => Refl
        #|    No(nope) => absurd(nope(Refl))
        #|  }
        #|}
        #|
        #|enum NatLe : (Nat, Nat) -> Prop {
        #|  LeZ[n : Nat] : NatLe(0, n)
        #|  LeS[a : Nat, b : Nat](NatLe(a, b)) : NatLe(S(a), S(b))
        #|}
        #|
        #|lemma move[a : Nat, b : Nat, c : Nat](h : NatLe(a, b), e : b === c) -> NatLe(a, c) {
        #|  Id::subst_prop(e, x => NatLe(a, x), h)
        #|}
        #|
        #|fn main {
        #|  let r = upd(_ => 0, "x", 5)
        #|  println(r("x") + r("y"))
        #|  println(DecEq::deq(Red, Rgb(1, 2, 3)) is No(_))
        #|  println(Nat::deq(3, 4) is No(_))
        #|}
      ),
    ),
    content=(
      #|5
      #|true
      #|true
      #|
    ),
  )
}

///|
/// `T?` followed by a comma in type arguments is a type, not a tagged
/// argument (bugs/006 of moonlit).
test "option types in type arguments" {
  inspect(
    run_source(
      "t.mbtpp",
      (
        #|fn f() -> Result[Int?, String] {
        #|  Ok(None)
        #|}
        #|
        #|fn g(x : Result[String?, Int?]) -> Int {
        #|  match x {
        #|    Ok(_) => 1
        #|    Err(_) => 2
        #|  }
        #|}
        #|
        #|fn opt(a : Int, title? : String) -> String {
        #|  match title {
        #|    Some(t) => t
        #|    None => a.to_string()
        #|  }
        #|}
        #|
        #|fn main {
        #|  println(f())
        #|  println(g(Err(None)))
        #|  let title : String? = Some("t")
        #|  println(opt(1, title?))
        #|}
      ),
    ),
    content=(
      #|Ok(None)
      #|2
      #|t
      #|
    ),
  )
}

///|
test "example staging" {
  inspect(
    run_example("staging.mbtpp"),
    content=(
      #|27
      #|4
      #|0
      #|30
      #|42
      #|1024
      #|
    ),
  )
}
