# Staged Metaprogramming

With staged metaprogramming a program makes the code of another: `code { e }` is the code of the
expression `e`, and `${ c }` puts the code `c` where it stands. A splice written in a function runs
**when the program is checked** and is replaced by the code it makes, so what the generator computes
is not left for run time.

```moonbit
// x to the power n: the recursion on n is done by the generator
fn power(n : Nat, x : Code[Int]) -> Code[Int] {
  match n {
    Z => code { 1 }
    S(k) => code { ${x} * ${power(k, x)} }
  }
}

// once checked, the definition of cube is x * (x * (x * 1))
fn cube(x : Int) -> Int {
  ${ power(3, code { x }) }
}

lemma cube_2 : cube(2) === 8 = Refl

fn main {
  println(cube(3))
}
```

- `Code[T]` is the type of code of type `T`.
- `code { e }` has type `Code[T]`, where `T` is the type of `e`. `code` is not a keyword: it is a
  quotation only when `{` follows.
- `${ c }` needs `c : Code[T]`, and has type `T`. When `c` is a variable it can be written `$c`.

Compiled to MoonBit, `cube` is `x * (x * (x * 1))`: no loop, and no call of `power`.

## Stages

The code in `code { }` runs later, the code in `${ }` runs first. The checker gives every piece of
code a stage: the body of a declaration is at stage 0, `code { }` adds one, `${ }` subtracts one. A
variable cannot be used at a stage lower than the one it is bound at, where its value is not known
yet:

```text
fn bad(n : Nat, x : Int) -> Int {
  ${ power(n, code { x }) }
}
// error: n is not known when this splice runs: it is a variable of the
// generated code (it is bound at stage 0 and used at stage -1). Use it
// inside `code { }`
```

The other way is always fine: a value the generator knows can be written in the code, whether it is
a number, a string, a value of a datatype, a function or a trait instance.

```moonbit
enum Color { Red; Green } derive(Show)

fn label(c : Color, prefix : String) -> Code[String] {
  code { prefix + c.to_string() }
}

// "is " + Green.to_string()
fn green() -> String {
  ${ label(Green, "is ") }
}

fn main {
  println(green())
}
```

Types and proofs are erased, so they can be used at any stage. A `let mut` variable cannot be used
across stages; copy it with `let` first.

## Generators

A generator is an ordinary function returning `Code[T]`: it can recurse, match, call other
generators, and use `let mut` and loops. The code it makes can have loops and mutable variables too:

```moonbit
// the code of body(0), …, body(n - 1), in order
fn repeat(n : Int, body : (Int) -> Code[Unit]) -> Code[Unit] {
  if n == 0 { code { () } } else {
    code { ${repeat(n - 1, body)}; ${body(n - 1)} }
  }
}

// s = s + 0 * m; s = s + 1 * m; s = s + 2 * m
fn weighted(m : Int) -> Int {
  let mut s = 0
  ${ repeat(3, i => code { s = s + i * m }) }
  s
}

// code accumulated in a mutable variable
fn sum_code(n : Int, x : Code[Int]) -> Code[Int] {
  let mut acc = code { 0 }
  for i = 0; i < n; i = i + 1 {
    let a = acc
    acc = code { ${a} + ${x} * i }
  }
  acc
}

fn g(x : Int) -> Int {
  ${ sum_code(3, code { x }) }
}

fn main {
  println(weighted(10))
  println(g(10))
}
```

Code that is spliced twice is computed twice. To compute it once, generate a `let`, and take the
rest of the code as a function:

```moonbit
fn genlet(c : Code[Int], k : (Code[Int]) -> Code[Int]) -> Code[Int] {
  code { let t = ${c}; ${ k(code { t }) } }
}

fn square_sum(a : Code[Int], b : Code[Int]) -> Code[Int] {
  genlet(code { ${a} + ${b} }, s => code { ${s} * ${s} })
}

// { let t = x + y; t * t }
fn f(x : Int, y : Int) -> Int {
  ${ square_sum(code { x }, code { y }) }
}

fn main {
  println(f(1, 2))
}
```

## With dependent types

A generator runs when the program is checked, so it can use what only the type checker knows. The
evaluator of a typed expression language, once staged, is its compiler, and the code it makes has no
run-time type tags:

```moonbit
enum Exp : [T] -> Type {
  IntLit(Int) : Exp[Int]
  Arg : Exp[Int]
  Add(Exp[Int], Exp[Int]) : Exp[Int]
  Less(Exp[Int], Exp[Int]) : Exp[Bool]
  If[T](Exp[Bool], Exp[T], Exp[T]) : Exp[T]
}

fn[T] Exp::compile(self : Exp[T], arg : Code[Int]) -> Code[T] {
  match self {
    IntLit(n) => code { n }
    Arg => arg
    Add(l, r) => code { ${l.compile(arg)} + ${r.compile(arg)} }
    Less(l, r) => code { ${l.compile(arg)} < ${r.compile(arg)} }
    If[_](c, t, f) =>
      code { if ${c.compile(arg)} { ${t.compile(arg)} } else { ${f.compile(arg)} } }
  }
}

// if x < 10 { x + 1 } else { 0 }
fn step(x : Int) -> Int {
  ${ If(Less(Arg, IntLit(10)), Add(Arg, IntLit(1)), IntLit(0)).compile(code { x }) }
}

fn main {
  println(step(3))
  println(step(30))
}
```

A vector whose length is known needs no loop, and no case for `Nil`:

```moonbit
enum Vector[T] : Nat -> Type {
  Nil : Vector[T](0)
  Cons[n : Nat](T, Vector[T](n)) : Vector[T](S(n))
}

fn sum_n(n : Nat, v : Code[Vector[Int](n)]) -> Code[Int] {
  match n {
    Z => code { 0 }
    S(k) => code { match ${v} { Cons(h, t) => h + ${sum_n(k, code { t })} } }
  }
}

fn sum3(v : Vector[Int](3)) -> Int {
  ${ sum_n(3, code { v }) }
}

fn main {
  println(sum3(Cons(1, Cons(2, Cons(3, Nil)))))
}
```

## What code means

Without its `code { }` and `${ }`, a program has the same result. That is how the type checker
computes: `${ code { e } }` is `e`, and `c.run()` is what `c` holds. So properties of generators and
of generated functions can be proved:

```moonbit
fn inc(c : Code[Int]) -> Code[Int] {
  code { ${c} + 1 }
}

lemma inc_run(c : Code[Int]) -> inc(c).run() === c.run() + 1 { Refl }

lemma eta(c : Code[Int]) -> code { ${c} } === c { Refl }
```

## Making code at run time

Code can also be made at run time, and run with `run`. What the generator computes is then computed
when the code is made, not again when it runs:

```moonbit
fn power(n : Nat, x : Code[Int]) -> Code[Int] {
  match n {
    Z => code { 1 }
    S(k) => code { ${x} * ${power(k, x)} }
  }
}

fn main {
  let n = 10
  // the recursion on n happens here
  let c = power(int_to_nat(n), code { 2 })
  // only multiplications here
  println(c.run())
}
```

Code at run time is a closure, not MoonBit source, so it is slower than a splice written in a
function (which is expanded to native code).

## Splices and effects

A splice `a` in `code { … ${a} … }` runs when that code is made, not when it runs. So the errors `a`
raises and the effects it performs are those of the generator:

```moonbit
suberror TooBig { TooBig }

fn small(n : Int) -> Code[Int] raise TooBig {
  if n > 9 { raise TooBig }
  code { n }
}

fn pair(a : Int, b : Int) -> Code[Int] raise TooBig {
  code { ${small(a)} * 10 + ${small(b)} }
}

fn main {
  let c = try pair(1, 20) catch { TooBig => code { 0 } }
  println(c.run())
}
```

Two kinds of splices cannot have effects (they cannot `raise`, nor perform operations):

- a splice written in a function, outside of `code { }`: it runs when the program is checked;
- a splice that uses the variables of the code it is in, such as
  `code { (y : Int) => ${ f(code { y }) } }`: it can only run when the code does.

Code that raises errors when it runs has type `Code[T raise E]`:

```moonbit
suberror DivError { DivError(String) }

fn div(a : Int, b : Int) -> Int raise DivError {
  if b == 0 { raise DivError("div by zero") }
  a / b
}

fn half_of(c : Code[Int]) -> Code[Int raise DivError] {
  code { div(${c}, 2) }
}

fn f(x : Int) -> Int raise DivError {
  ${ half_of(code { x }) }
}

fn main {
  try { println(f(8)) } catch { DivError(m) => println(m) }
}
```

## Limitations

- A splice written in a function is run by the type checker, so generators cannot use arrays,
  `print` or imported MoonBit functions. When a splice cannot be computed, the error shows the
  expression it is stuck on.
- Code cannot be inspected or taken apart: a `Code[T]` can only be spliced and run.
- `Code[T]` uses the uniform representation in compiled programs.
