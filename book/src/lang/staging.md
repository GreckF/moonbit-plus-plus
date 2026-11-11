# 分阶段元编程

分阶段元编程让一个程序生成另一个程序的代码：`code { e }` 是表达式 `e` 的代码，`${ c }` 把代码 `c`
放在它所在的位置。写在函数里的拼接在**检查程序时**运行，被它生成的代码替换，所以生成器做的计算
不会留到运行时。

```moonbit
// x 的 n 次方：对 n 的递归由生成器完成
fn power(n : Nat, x : Code[Int]) -> Code[Int] {
  match n {
    Z => code { 1 }
    S(k) => code { ${x} * ${power(k, x)} }
  }
}

// 检查之后，cube 的定义是 x * (x * (x * 1))
fn cube(x : Int) -> Int {
  ${ power(3, code { x }) }
}

lemma cube_2 : cube(2) === 8 = Refl

fn main {
  println(cube(3))
}
```

- `Code[T]` 是类型为 `T` 的代码的类型。
- `code { e }` 的类型是 `Code[T]`，其中 `T` 是 `e` 的类型。`code` 不是关键字，只有后面紧跟 `{` 时
  才是引用。
- `${ c }` 要求 `c : Code[T]`，它的类型是 `T`。`c` 是一个变量时可以写成 `$c`。

`cube` 编译成 MoonBit 之后是 `x * (x * (x * 1))`，没有循环，也没有 `power` 的调用。

## 阶段

`code { }` 里的代码以后才运行，`${ }` 里的代码要先运行。检查器给每段代码一个阶段：声明的定义体
在阶段 0，`code { }` 加一，`${ }` 减一。变量不能在比绑定它的阶段更低的阶段使用——那时它的值还
不知道：

```text
fn bad(n : Nat, x : Int) -> Int {
  ${ power(n, code { x }) }
}
// error: n is not known when this splice runs: it is a variable of the
// generated code (it is bound at stage 0 and used at stage -1). Use it
// inside `code { }`
```

反过来总是可以的：生成器知道的值可以直接写进代码，不管它是数、字符串、构造子的值、函数还是
trait 实例。

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

类型和证明会被擦除，所以在任何阶段都可以使用。`let mut` 变量不能跨阶段使用，先用 `let` 复制。

## 生成器

生成器就是返回 `Code[T]` 的普通函数，可以递归、匹配、调用其他生成器，可以用 `let mut` 和循环。
生成的代码也可以有循环和可变变量：

```moonbit
// 依次是 body(0)、…、body(n - 1) 的代码
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

// 用可变变量累积代码
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

一段代码被拼接两次就会被计算两次。要只计算一次，就生成一个 `let`，并把后面的代码作为函数传入：

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

## 与依赖类型一起使用

生成器在检查时运行，所以它可以利用只有类型检查器才知道的信息。带类型的表达式语言的求值器，
分阶段之后就是它的编译器，而且生成的代码里没有运行时的类型标签：

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

长度已知的向量可以不用循环、也不用处理 `Nil`：

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

## 代码的含义

去掉 `code { }` 和 `${ }` 之后，程序的结果不变。类型检查器就是这样计算的：`${ code { e } }` 是
`e`，`c.run()` 是 `c` 的内容。所以可以证明生成器和生成的函数的性质：

```moonbit
fn inc(c : Code[Int]) -> Code[Int] {
  code { ${c} + 1 }
}

lemma inc_run(c : Code[Int]) -> inc(c).run() === c.run() + 1 { Refl }

lemma eta(c : Code[Int]) -> code { ${c} } === c { Refl }
```

## 在运行时生成代码

代码也可以在运行时生成，并用 `run` 运行。此时生成器的计算在生成代码时完成，运行代码时不再重复：

```moonbit
fn power(n : Nat, x : Code[Int]) -> Code[Int] {
  match n {
    Z => code { 1 }
    S(k) => code { ${x} * ${power(k, x)} }
  }
}

fn main {
  let n = 10
  // 这里做对 n 的递归
  let c = power(int_to_nat(n), code { 2 })
  // 这里只做乘法
  println(c.run())
}
```

运行时的代码是闭包，不是 MoonBit 源代码，所以它比写在函数里的拼接（被展开成原生代码）慢。

## 拼接与效应

`code { … ${a} … }` 里的拼接 `a` 在这段代码被生成时运行，不是在代码运行时。所以 `a` 抛出的错误和
执行的效应属于生成器：

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

有两种拼接不能有效应（不能 `raise`，不能执行效应操作）：

- 写在函数里、不在 `code { }` 里的拼接：它在检查程序时运行；
- 用到所在代码的变量的拼接，例如 `code { (y : Int) => ${ f(code { y }) } }`：它只能在代码运行时
  运行。

会在运行时抛出错误的代码，类型是 `Code[T raise E]`：

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

## 在生成器中使用数组、`print` 和 MoonBit 函数

写在函数里的拼接在检查程序时运行。运行时的状态是真的：数组是可变的值，`print` 在检查时输出，
生成的数组被写进代码里：

```moonbit
fn table(n : Int) -> Array[Int] {
  let t : Array[Int] = []
  for i = 0; i < n; i = i + 1 {
    t.push(i * i)
  }
  t
}

// 数组在生成代码时算好，代码里是 [0, 1, 4, 9, 16][3]
fn pick(i : Int) -> Code[Int] {
  let t = table(5)
  println("generating")
  code { t[i] }
}

fn nine() -> Int {
  ${ pick(3) }
}

fn main {
  println(nine())
}
```

导入的 MoonBit 函数在检查器里没有定义，只有类型。写在函数里的拼接调用它们时，moonpp 会把这些函数
编译成一个 MoonBit 程序（`mbtpp_out/driver`，单个文件时是 `_mbtpp_build/driver`），用 `moon` 编成
JavaScript 并加载，检查器通过它调用：

```text
// requires moonbitlang/core/math
fn norm_code(x : Double, y : Double) -> Code[Double] {
  let d = @math.hypot(x, y)     // 由 MoonBit 在生成代码时计算
  code { d * 2.0 }
}

fn norm() -> Double {
  ${ norm_code(3.0, 4.0) }       // 检查后：10.0
}
```

- 数、字符串、数组、数据类型的值（`Option`、`Result`、元组、`#mbt` 类型）按值传递；MoonBit 里
  没有定义的类型（`Queue` 之类）的值留在 MoonBit 一侧，检查器拿着它的句柄，可以传给后面的调用；
  传给 MoonBit 的函数会被 MoonBit 回调，回调在检查器里运行。
- 要有 `moon` 命令，要用 `moonpp`（`check`、`run`、`build`）：playground 和编辑器（`moonpp ide`）
  不能构建这个程序，那里这样的拼接会报告“算不出来”。导入的包要能编译到 JavaScript 目标。
- 调用在求值到它时发生。有副作用的 MoonBit 函数请写成语句（`q.push(x)`），不要放在
  纯函数的参数里。
- 函数的签名要能被编译器的 FFI 转换（见[调用 MoonBit 函数](../interop/ffi.md)）；不能的函数
  报告原因。

## 限制

- 导入的 MoonBit 函数只能在 `moonpp` 里调用（需要 `moon`），playground 和编辑器里的拼接
  算不出来时会报错，并显示卡住的表达式。
- 生成器不能使用生成代码的变量；不能检查或拆开一段代码：`Code[T]` 只能被拼接和运行。
- `Code[T]` 在编译后的程序里使用统一表示。
