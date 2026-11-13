///|
/// Programs that must be rejected, and a few small positive checks.
fn check(src : String) -> String {
  @mbtpp.check_source("t.mbtpp", src)
}

///|
test "non-exhaustive match" {
  inspect(
    check(
      (
        #|fn f(n : Nat) -> Int {
        #|  match n {
        #|    Z => 0
        #|  }
        #|}
      ),
    ),
    content=(
      #|t.mbtpp:2:3: error: match is not exhaustive; missing case(s):
      #|  S(_)
    ),
  )
}

///|
test "impossible case that is possible" {
  inspect(
    check(
      (
        #|fn f(n : Nat) -> Int {
        #|  match n {
        #|    Z
        #|    S(_) => 1
        #|  }
        #|}
      ),
    ),
    content="t.mbtpp:3:5: error: this pattern is not impossible",
  )
}

///|
test "type mismatch" {
  inspect(
    check("fn f(x : Int) -> String { x }"),
    content=(
      #|t.mbtpp:1:27: error: type mismatch
      #|  expected: String
      #|  actual:   Int
    ),
  )
}

///|
test "uncurried: too few arguments" {
  inspect(
    check(
      (
        #|fn add(a : Int, b : Int) -> Int { a + b }
        #|fn main { println(add(1)(2)) }
      ),
    ),
    content="t.mbtpp:2:22: error: expected 2 argument(s), got 1",
  )
}

///|
test "uncurried: curried function called with two arguments" {
  inspect(
    check(
      (
        #|fn add(a : Int) -> (Int) -> Int { b => a + b }
        #|fn main { println(add(1, 2)) }
      ),
    ),
    content="t.mbtpp:2:22: error: expected 1 argument(s), got 2",
  )
}

///|
test "uncurried: groups are different types" {
  inspect(
    check(
      (
        #|fn f(g : (Int, Int) -> Int) -> Int { g(1, 2) }
        #|fn h(a : Int) -> (Int) -> Int { b => a }
        #|fn main { println(f(h)) }
      ),
    ),
    content=(
      #|t.mbtpp:3:21: error: type mismatch
      #|  expected: (Int, Int) -> Int
      #|  actual:   (a : Int) -> (Int) -> Int
    ),
  )
}

///|
test "prop elimination into Type" {
  inspect(
    check(
      (
        #|enum Or[A : Prop, B : Prop] : Prop {
        #|  Inl(A)
        #|  Inr(B)
        #|}
        #|fn[A : Prop, B : Prop] which(p : Or[A, B]) -> Bool {
        #|  match p {
        #|    Inl(_) => true
        #|    Inr(_) => false
        #|  }
        #|}
      ),
    ),
    content="t.mbtpp:6:3: error: cannot eliminate a proof of Or into a type that is not a proposition",
  )
}

///|
test "prop elimination into Prop is fine" {
  inspect(
    check(
      (
        #|enum Or[A : Prop, B : Prop] : Prop {
        #|  Inl(A)
        #|  Inr(B)
        #|}
        #|fn[A : Prop, B : Prop] swap(p : Or[A, B]) -> Or[B, A] {
        #|  match p {
        #|    Inl(a) => Inr(a)
        #|    Inr(b) => Inl(b)
        #|  }
        #|}
      ),
    ),
    content="ok",
  )
}

///|
test "proof irrelevance" {
  inspect(
    check(
      (
        #|fn[P : Prop] irrelevant(p : P, q : P) -> p === q { Refl }
      ),
    ),
    content="ok",
  )
}

///|
test "raise outside a raising function" {
  inspect(
    check("fn f() -> Int { raise Failure(\"x\") }"),
    content="t.mbtpp:1:17: error: `raise` outside of a function declared with `raise`",
  )
}

///|
test "calling a raising function" {
  inspect(
    check(
      (
        #|fn f() -> Int raise Failure { fail("x") }
        #|fn g() -> Int { f() }
      ),
    ),
    content="t.mbtpp:2:18: error: this call may raise an error; use it inside `try` or in a function declared with `raise`",
  )
}

///|
test "assignment to an immutable variable" {
  inspect(
    check("fn f() -> Unit { let x = 1; x = 2 }"),
    content="t.mbtpp:1:29: error: x is not a mutable variable",
  )
}

///|
test "missing instance" {
  inspect(
    check(
      (
        #|enum Color { Red }
        #|fn main { println(Red) }
      ),
    ),
    content="t.mbtpp:2:18: error: no instance of Show(Color)",
  )
}

///|
test "wrong index" {
  inspect(
    check(
      (
        #|enum Vector[T] : Nat -> Type {
        #|  Nil : Vector[T](0)
        #|  Cons[n : Nat](T, Vector[T](n)) : Vector[T](S(n))
        #|}
        #|fn bad() -> Vector[Int](2) { Cons(1, Nil) }
      ),
    ),
    content=(
      #|t.mbtpp:5:38: error: type mismatch
      #|  expected: Vector[Int](1)
      #|  actual:   Vector[?870(_)](0)
    ),
  )
}

///|
test "type-level computation" {
  inspect(
    check(
      (
        #|fn two() -> Nat { 1 + 1 }
        #|lemma two_eq : two(()) === 2 = Refl
        #|lemma plus_comm_ex : plus(2, 3) === plus(3, 2) = Refl
      ),
    ),
    content="ok",
  )
}

///|
test "functions with mutation are run in types" {
  inspect(
    check(
      (
        #|fn one() -> Int { let mut x = 0; x = x + 1; x }
        #|fn sum_to(n : Int) -> Int {
        #|  let mut i = 0
        #|  let mut acc = 0
        #|  while i < n { i = i + 1; acc = acc + i }
        #|  acc
        #|}
        #|suberror Neg { Neg(Int) }
        #|fn checked(x : Int) -> Int raise Neg { if x < 0 { raise Neg(x) }; x }
        #|fn safe(x : Int) -> Int { try checked(x) catch { Neg(k) => k - 100 } }
        #|fn inc(x : Int) -> Int { let mut y = x; y = y + 1; y }
        #|lemma a : one(()) === 1 = Refl
        #|lemma b : sum_to(10) === 55 = Refl
        #|lemma c : safe(-5) === -105 = Refl
        #|lemma d[x : Int] : inc(x) === x + 1 = Refl
      ),
    ),
    content="ok",
  )
}

///|
test "a run that cannot finish keeps the call folded" {
  // a decision on a variable
  inspect(
    check(
      (
        #|fn abs(x : Int) -> Int { if x < 0 { return -x }; x }
        #|lemma bad[x : Int] : abs(x) === x = Refl
      ),
    ),
    content=(
      #|t.mbtpp:2:37: error: type mismatch
      #|  expected: abs(x) === x
      #|  actual:   ?868(x) === ?868(x)
    ),
  )
  // arrays are mutable
  inspect(
    check(
      (
        #|fn first() -> Int { let a = [1, 2]; a[0] }
        #|lemma bad : first(()) === 1 = Refl
      ),
    ),
    content=(
      #|t.mbtpp:2:31: error: type mismatch
      #|  expected: first(()) === 1
      #|  actual:   ?869 === ?869
    ),
  )
}

///|
test "time limit of a declaration" {
  inspect(
    check(
      (
        #|fn spin(n : Int) -> Int { let mut i = n; while true { i = i + 1 }; i }
        #|#timelimit(1)
        #|lemma bad : spin(0) === 0 = Refl
      ),
    ),
    content=(
      #|t.mbtpp:3:1: error: checking bad took more than 1 s (while evaluating spin); a definition that does not terminate? Raise the limit with #timelimit(seconds) or #timelimit(none)
    ),
  )
}

///|
test "implicit binder defaults to Type" {
  inspect(
    check("fn[T] id(x : T) -> T { x }\nlemma t : id(3) === 3 = Refl"),
    content="ok",
  )
}

///|
test "unsolved goals" {
  inspect(
    check("lemma l : forall n : Nat, plus(n, 0) === n = proof { intros n }"),
    content=(
      #|t.mbtpp:1:54: error: unsolved goal(s); the first is
      #|  plus(n, 0) === n
      #|in context n
    ),
  )
}

///|
let stlc_prelude : String =
  #|enum Vector[T] : Nat -> Type {
  #|  Nil : Vector[T](0)
  #|  Cons[n : Nat](T, Vector[T](n)) : Vector[T](S(n))
  #|}
  #|enum Fin : (Nat) -> Type {
  #|  FZ[n : Nat] : Fin(S(n))
  #|  FS[n : Nat](Fin(n)) : Fin(S(n))
  #|}
  #|enum Ty {
  #|  TInt
  #|  TArr(Ty, Ty)
  #|}
  #|enum Ctx {
  #|  Empty
  #|  Ext(Ctx, Ty)
  #|}
  #|enum Elem : (Ctx, Ty) -> Type {
  #|  Here[g : Ctx, t : Ty] : Elem(Ext(g, t), t)
  #|  There[g : Ctx, t : Ty, s : Ty](Elem(g, t)) : Elem(Ext(g, s), t)
  #|}
  #|enum Term : (Ctx, Ty) -> Type {
  #|  Var[g : Ctx, t : Ty](Elem(g, t)) : Term(g, t)
  #|  Lit[g : Ctx](Int) : Term(g, TInt)
  #|  App[g : Ctx, a : Ty, b : Ty](Term(g, TArr(a, b)), Term(g, a)) : Term(g, b)
  #|}
  #|

///|
test "regression: a variable of a built-in type is not empty" {
  inspect(
    check(
      (
        #|fn f(x : Int, n : Nat) -> Int {
        #|  match n {
        #|    Z => 0
        #|  }
        #|}
      ),
    ),
    content=(
      #|t.mbtpp:2:3: error: match is not exhaustive; missing case(s):
      #|  S(_)
    ),
  )
}

///|
test "empty index type makes a case impossible" {
  inspect(
    check(
      stlc_prelude +
      (
        #|fn[T, n : Nat] get(v : Vector[T](n), i : Fin(n)) -> T {
        #|  match (v, i) {
        #|    (Nil, _)
        #|    (Cons(x, _), FZ) => x
        #|    (Cons(_, xs), FS(j)) => get(xs, j)
        #|  }
        #|}
      ),
    ),
    content="ok",
  )
}

///|
test "indexing an empty vector" {
  inspect(
    check(
      stlc_prelude +
      (
        #|fn[T, n : Nat] get(v : Vector[T](n), i : Fin(n)) -> T {
        #|  match (v, i) {
        #|    (Cons(x, _), FZ) => x
        #|    (Cons(_, xs), FS(j)) => get(xs, j)
        #|  }
        #|}
        #|fn bad() -> Int { get(Vector::Nil, FZ) }
      ),
    ),
    content=(
      #|t.mbtpp:32:36: error: type mismatch
      #|  expected: Fin(0)
      #|  actual:   Fin(S(?874(_)))
    ),
  )
}

///|
test "ill-typed object term" {
  inspect(
    check(
      stlc_prelude + "fn bad() -> Term(Empty, TInt) { App(Lit(1), Lit(2)) }",
    ),
    content=(
      #|t.mbtpp:26:40: error: type mismatch
      #|  expected: Term(Empty, TArr(?869(_), TInt))
      #|  actual:   Term(?871(_), TInt)
    ),
  )
}

///|
test "unbound object variable" {
  inspect(
    check(stlc_prelude + "fn bad() -> Term(Empty, TInt) { Var(Here) }"),
    content=(
      #|t.mbtpp:26:37: error: type mismatch
      #|  expected: Elem(Empty, TInt)
      #|  actual:   Elem(Ext(?870(_), ?871(_)), ?871(_))
    ),
  )
}

///|
test "no termination check: a looping proof is accepted (by design)" {
  inspect(check("lemma bad(n : Nat) -> n === S(n) { bad(n) }"), content="ok")
}

///|
let labelled_prelude : String =
  #|fn f(x : Int, a~ : Int, b~ : Int = 1, c? : Int) -> Int { x + a + b }
  #|

///|
test "tagged: missing labelled argument" {
  inspect(
    check(labelled_prelude + "fn main { println(f(1)) }"),
    content="t.mbtpp:2:20: error: missing labelled argument a~",
  )
}

///|
test "tagged: unknown label" {
  inspect(
    check(labelled_prelude + "fn main { println(f(1, a=2, d=3)) }"),
    content="t.mbtpp:2:29: error: no labelled parameter d",
  )
}

///|
test "tagged: argument given twice" {
  inspect(
    check(labelled_prelude + "fn main { println(f(1, a=2, a=3)) }"),
    content="t.mbtpp:2:29: error: argument a is given twice",
  )
}

///|
test "tagged: `?=` on a parameter that is not optional" {
  inspect(
    check(labelled_prelude + "fn main { println(f(1, a?=Some(2))) }"),
    content="t.mbtpp:2:24: error: `a?=` is only for parameters declared `a?`",
  )
}

///|
test "tagged: too many positional arguments" {
  inspect(
    check(labelled_prelude + "fn main { println(f(1, 2, a=3)) }"),
    content="t.mbtpp:2:20: error: too many positional arguments",
  )
}

///|
test "tagged: wrong type for an optional argument" {
  inspect(
    check(labelled_prelude + "fn main { println(f(1, a=2, c=\"x\")) }"),
    content=(
      #|t.mbtpp:2:31: error: type mismatch
      #|  expected: Int
      #|  actual:   String
    ),
  )
}

///|
test "tagged: lambdas cannot have labelled parameters" {
  inspect(
    check("fn main { let g = fn(x~ : Int) { x }; println(g(x=1)) }"),
    content="t.mbtpp:1:22: error: only top-level functions can have labelled parameters",
  )
}

///|
test "tagged: all accepted call forms" {
  inspect(
    check(
      labelled_prelude +
      (
        #|fn main {
        #|  let a = 2
        #|  let c : Int? = None
        #|  println(f(1, a~))
        #|  println(f(b=5, a=1, 0))
        #|  println(f(1, a=2, c=3))
        #|  println(f(1, a=2, c?))
        #|  println(f(1, a=2, c?=Some(4)))
        #|}
      ),
    ),
    content="ok",
  )
}

///|
test "mbt: translatable declarations" {
  inspect(
    check(
      (
        #|#mbt
        #|enum Tree[T] {
        #|  Leaf
        #|  Node(Tree[T], T, Tree[T])
        #|}
        #|#mbt
        #|struct Point { x : Double; y : Double }
        #|#mbt
        #|trait Size { size(Self) -> Int; zero() -> Self }
        #|impl[T : Size] Size for Tree[T] with size(self) {
        #|  match self {
        #|    Leaf => 0
        #|    Node(l, x, r) => l.size() + x.size() + r.size()
        #|  }
        #|}
        #|impl[T : Size] Size for Tree[T] with zero() { Leaf }
        #|impl Size for Int with size(self) { self }
        #|impl Size for Int with zero() { 0 }
        #|fn main { println(Node(Leaf, 3, Leaf).size()) }
      ),
    ),
    content="ok",
  )
}

///|
test "mbt: indexed types are rejected" {
  inspect(
    check(
      (
        #|#mbt
        #|enum Vec[T] : (n : Nat) -> Type {
        #|  VNil : Vec[T](Z)
        #|}
      ),
    ),
    content="t.mbtpp:1:1: error: #mbt Vec: indexed types have no MoonBit type",
  )
}

///|
test "mbt: fields need MoonBit types" {
  inspect(
    check("#mbt\nstruct P { n : Nat }"),
    content="t.mbtpp:1:1: error: #mbt P: the field n of P::mk has type Nat, which has no MoonBit type",
  )
  inspect(
    check("#mbt\nenum E { A(Int); b }"),
    content="t.mbtpp:1:1: error: #mbt E: constructor E::b must start with an upper case letter",
  )
  inspect(
    check("#mbt\nenum Value { A }"),
    content=(
      #|t.mbtpp:1:1: error: #mbt Value: Value cannot be the name of a generated MoonBit type (use #mbt("name") for an existing one)
    ),
  )
}

///|
test "mbt: traits" {
  inspect(
    check("#mbt\ntrait T { fn[A] m(Self, A) -> Int }"),
    content="t.mbtpp:1:1: error: #mbt T: the method m is generic",
  )
  inspect(
    check("trait S { s(Self) -> Int }\n#mbt\ntrait T : S { m(Self) -> Int }"),
    content="t.mbtpp:2:1: error: #mbt T: the supertrait S is not #mbt",
  )
  inspect(
    check(
      (
        #|#mbt
        #|trait T { m(Self) -> Int }
        #|impl T for Nat with m(self) { 0 }
      ),
    ),
    content="t.mbtpp:3:1: error: impl of #mbt trait T: the type Nat has no MoonBit type",
  )
  inspect(
    check(
      (
        #|#mbt("Hash")
        #|trait H { m(Self) -> Int }
        #|impl H for Int with m(self) { 0 }
      ),
    ),
    content="t.mbtpp:3:1: error: impl of #mbt trait H: MoonBit does not allow implementing the existing trait Hash for a type that is not generated by this program",
  )
}

///|
test "mbt: functions" {
  inspect(
    check("#mbt\nfn f(n : Nat) -> Int { 0 }"),
    content="t.mbtpp:1:1: error: #mbt fn f: the parameter n has type Nat, which has no MoonBit type",
  )
  inspect(
    check("#mbt\nfn[T : Show] f(x : T) -> String { x.to_string() }"),
    content=(
      #|ok
    ),
  )
  inspect(
    check("#mbt\nfn Nat::twice(self : Nat) -> Nat { self + self }"),
    content="t.mbtpp:1:1: error: #mbt fn Nat::twice: a method must belong to a type generated by this program (a #mbt type without a name)",
  )
  inspect(
    check("#mbt\nfn f(x~ : Int = 1) -> Int { x }"),
    content="t.mbtpp:1:1: error: #mbt fn f: default arguments are not supported",
  )
  inspect(
    check("#mbt\nfn f(xs : Array[Int]) -> Int { 0 }"),
    content=(
      #|ok
    ),
  )
}

///|
fn check_files(files : Array[(String, String)]) -> String {
  @tt.check_package(files) catch {
    @tt.CheckError(msg) => return msg
  }
  "ok"
}

///|
test "file order: a hint when a later file's function is needed" {
  let shapes = (
    "shapes.mbtpp", "enum Shape { Sq(Int) }\nfn Shape::area(self : Shape) -> Int { match self { Sq(n) => n * n } }",
  )
  let facts = ("facts.mbtpp", "lemma area3 : Sq(3).area() === 9 = Refl")
  inspect(
    check_files([facts, shapes]),
    content=(
      #|facts.mbtpp:1:36: error: type mismatch
      #|  expected: Shape::area(Sq(3)) === 9
      #|  actual:   ?868 === ?868
      #|hint: Shape::area is defined in shapes.mbtpp, which is checked after facts.mbtpp, so its definition could not be used here; the error may come from that. Files are checked in dictionary order; to check shapes.mbtpp first, list it in the package's moon.pkg: options("mbtpp-order": [ "shapes.mbtpp", ... ])
    ),
  )
  inspect(check_files([shapes, facts]), content="ok")
}

///|
/// The `pub` declarations of a checked program that could be `#mbt`.
fn mbt_hints(src : String) -> String {
  @tt.check_program("a.mbtpp", src) catch {
    @tt.CheckError(msg) => return msg
  }
  @tt.mbt_hints(names => @codegen.native_fns([], names))
  .map(h => h.line.to_string() + " " + h.kind + " " + h.name)
  .join("\n")
}

///|
test "#mbt hints: pub declarations that translate" {
  let src =
    #|pub enum Shape { Circle(Double); Rect(Double, Double) }
    #|pub struct Point { x : Int; y : Int }
    #|pub enum Vec : Nat -> Type {
    #|  VNil : Vec(0)
    #|  VCons[n : Nat](Int, Vec(n)) : Vec(S(n))
    #|}
    #|pub struct Holder { v : Vec(0) }
    #|pub struct Pair { s : Shape; p : Point }
    #|pub trait Area { area(Self) -> Double }
    #|pub trait Len { len(Self) -> Nat }
    #|pub fn norm1(p : Point) -> Int { p.x + p.y }
    #|pub fn[n : Nat] vlen(v : Vec(n)) -> Int { 0 }
    #|pub fn nat_len(n : Nat) -> Nat { n }
    #|fn private_one(p : Point) -> Int { p.x }
    #|#mbt
    #|pub fn marked(x : Int) -> Int { x }
    #|pub lemma l : 1 === 1 = Refl
  inspect(
    mbt_hints(src),
    content=(
      #|1 type Shape
      #|2 type Point
      #|8 type Pair
      #|9 trait Area
      #|11 fn norm1
    ),
  )
  // the tentative marks are removed
  inspect(@tt.mbt_info("Shape") is None, content="true")
  inspect(@tt.mbt_fns.contains("norm1"), content="false")
}

///|
test "editor info: names and goals" {
  let src =
    #|struct Point { x : Int; y : Int }
    #|fn norm1(p : Point) -> Int { p.x + p.y }
    #|lemma zero_add : forall n : Nat, (0 : Nat) + n === n = proof {
    #|  intros n
    #|  rfl
    #|}
  @tt.check_program("a.mbtpp", src)
  let names = @tt.name_infos
    .filter(n => @tt.split_pos(n.pos).1 == 2)
    .map(n => (n.show)() + (if n.global is Some(_) { " (global)" } else { "" }))
  inspect(
    names.join("\n"),
    content=(
      #|Point : Type (global)
      #|Int : Type (global)
      #|p : Point
      #|Point::x : (self : Point) -> Int (global)
      #|p : Point
      #|Point::y : (self : Point) -> Int (global)
    ),
  )
  inspect(
    @tt.decl_pos.get("Point").map(p => @tt.split_pos(p)),
    content="Some((0, 1))",
  )
  let pr = @tt.proof_infos[0]
  let show = (gs : Array[@tt.GoalInfo]) => {
    gs.map(g => g.hyps.join(", ") + " |- " + g.goal).join("; ")
  }
  inspect(show(pr.start), content=" |- (n : Nat) -> (0 + n) === n")
  inspect(
    pr.tactics
    .map(t => {
      @tt.split_pos(t.0).1.to_string() +
      ": " +
      t.1.map(show).unwrap_or("failed")
    })
    .join("\n"),
    content=(
      #|4: n : Nat |- (0 + n) === n
      #|5: 
    ),
  )
}

///|
test "derive: what is not supported" {
  inspect(
    check("enum V : Nat -> Type { N : V(0) } derive(Show)"),
    content=(
      #|t.mbtpp:1:42: error: derive is not supported for indexed types (V)
    ),
  )
  inspect(
    check("enum E { A } derive(Arbitrary)"),
    content=(
      #|t.mbtpp:1:21: error: derive(Arbitrary) is not supported (only Show, Eq, Compare, Hash, DecEq, ToJson, FromJson, Debug)
    ),
  )
  inspect(
    check("enum E2 { A } derive(ToJson)"),
    content=(
      #|t.mbtpp:1:22: error: derive(ToJson) uses MoonBit's derive, so E2 must be #mbt
    ),
  )
  inspect(
    check("struct F { f : (Int) -> Int } derive(Show)"),
    content=(
      #|t.mbtpp:1:61: error: no instance of Show((Int) -> Int)
    ),
  )
  inspect(
    check("enum G[T] { G(T) } derive(Compare)"),
    content=(
      #|t.mbtpp:1:1: error: missing instance Eq(G[T]) required by Compare
    ),
  )
  inspect(check("enum H[T] { H(T) } derive(Eq, Compare)"), content="ok")
}

///|
test "trait objects: object safety" {
  inspect(
    check("fn f(x : &Eq) -> Bool { true }"),
    content=(
      #|t.mbtpp:1:10: error: &Eq is not a trait object type: the method op_equal does not take Self as its first parameter only
    ),
  )
  inspect(
    check("fn f(x : &Monad) -> Int { 0 }"),
    content=(
      #|t.mbtpp:1:10: error: &Monad is not a trait object type: its Self is not a type
    ),
  )
  inspect(
    check("fn f(x : &Int) -> Int { 0 }"),
    content=(
      #|t.mbtpp:1:10: error: Int is not a trait
    ),
  )
  inspect(
    check("trait T { m(Self) -> Int }\nfn f() -> &T { 1 }"),
    content=(
      #|t.mbtpp:2:16: error: no instance of T(Int)
    ),
  )
}

///|
test "or-pattern alternatives bind different variables" {
  inspect(
    check(
      (
        #|fn f(o : Option[Int]) -> Int {
        #|  match o { Some(x) | None => 0 }
        #|}
      ),
    ),
    content="t.mbtpp:2:21: error: the alternatives of an or-pattern must bind the same variables",
  )
}

///|
test "guarded clauses do not count for coverage" {
  inspect(
    check(
      (
        #|fn f(n : Int) -> Int {
        #|  match n { x if x > 0 => 1 }
        #|}
      ),
    ),
    content=(
      #|t.mbtpp:2:3: error: match is not exhaustive; missing case(s):
      #|  n
    ),
  )
}

///|
test "async functions are called in async functions" {
  inspect(
    check(
      (
        #|async fn inc(x : Int) -> Int noraise { x + 1 }
        #|fn bad() -> Int { inc(1) }
      ),
    ),
    content="t.mbtpp:2:22: error: this calls an async function, which can only be done in an async function",
  )
  inspect(
    check(
      (
        #|async fn inc(x : Int) -> Int noraise { x + 1 }
        #|fn f() -> Int { let g : Int = inc; 0 }
      ),
    ),
    content=(
      #|t.mbtpp:2:31: error: type mismatch
      #|  expected: Int
      #|  actual:   async (x : Int) -> Int noraise
    ),
  )
}
