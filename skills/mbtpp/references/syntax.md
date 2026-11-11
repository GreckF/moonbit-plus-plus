# MoonBit++ 语法速查

和 MoonBit 相同的部分（表达式、语句、循环、struct、trait、错误、async）只列要点；MoonBit++ 特有的
部分（依赖类型、证明、效应）给出例子。详细说明见文档 `book/src/lang/`。

## 目录

- [基础](#基础)
- [函数](#函数)
- [类型](#类型)
- [enum 与索引类型](#enum-与索引类型)
- [struct](#struct)
- [模式匹配](#模式匹配)
- [依赖匹配](#依赖匹配)
- [命题与证明](#命题与证明)
- [策略](#策略)
- [受控展开](#受控展开)
- [trait](#trait)
- [可变状态与检查时执行](#可变状态与检查时执行)
- [错误](#错误)
- [async](#async)
- [代数效应](#代数效应)
- [与 MoonBit 交互](#与-moonbit-交互)
- [Prelude](#prelude)

## 基础

- 注释 `// …`（没有块注释）；语句用换行或 `;` 分隔。
- 字面量：`42`、`0xFF`、`1_000`、`1.5`、`1e-7`、`1L`（`Int64`）、`1U`、`1UL`、`1.5F`、`b'a'`、
  `'a'`、`"s"`、`true`、`()`、`[1, 2]`、`(1, "a")`、`{ "a": 1 }`（`Map`）。
- 字符串插值 `"\{e}"`；多行字符串用连续的 `#|`（原样）或 `$|`（可转义、插值）行。
- `let x = e`、`let x : T = e`、`let mut x = e`、`let (a, b) = pair`。
- `if c { a } else { b }` 是表达式；块的值是最后一个表达式。
- lambda：`x => e`、`(x, y) => e`、`(x : Int) => e`、`fn(x : Int) { … }`。
- 管道 `e |> f(a)` 即 `f(e, a)`；级联 `xs..push(1)..push(2)`；类型注解 `(e : T)`；洞 `_`。
- `pub`、`priv`、`derive(...)` 的可见性含义被忽略：一个包是一个作用域（`pub` 只用于 `#mbt` 提示）。

## 函数

```moonbit
fn add(x : Int, y : Int) -> Int { x + y }

fn[T] twice(f : (T) -> T, x : T) -> T { f(f(x)) }   // [T] 隐式参数

fn greet(name~ : String, greeting~ : String = "Hello", title? : String) -> String {
  match title {
    Some(t) => greeting + ", " + t + " " + name
    None => greeting + ", " + name
  }
}

fn main {
  println(twice[Int](x => x * 2, add(1, 2)))   // 显式给隐式参数
  println(greet(name="Alice", title="Dr."))
}
```

- 隐式参数 `[T]` 即 `[T : Type]`；`[n : Nat]` 是值参数；`[T : Show + Eq]` 是 trait 约束（冒号右边
  是 trait 时为约束，是类型时为隐式参数）。调用时一般推断，`f[a, _](x)` 按位置显式给出。
- 方法：`fn Type::m(self : Type, …)`，调用 `x.m(a)` 或 `Type::m(x, a)`。
- 运算符是方法：`op_add`、`op_sub`、`op_mul`、`op_div`、`op_mod`、`op_neg`、`op_equal`、`op_lt`、
  `op_le`、`op_gt`、`op_ge`、`op_land`、`op_lor`、`op_lxor`、`op_shl`、`op_shr`。
- 局部函数 `fn name(…) { … }` 可以递归，但不能用外层的 `let mut` 变量。
- 只有顶层函数（含方法）能有带标签参数。

## 类型

- `Type : Type`（逻辑不一致，有意的取舍）；`Prop : Type` 是命题的宇宙，证明无关。
- 函数类型：`(Int, Int) -> Int`、依赖的 `(n : Nat, v : Vector[Int](n)) -> Int`、
  `forall x y : A, P(x, y)`、`[T](x : T) -> T`、`(A) -> B raise E`、`(A) -> B!E`（效应）。
- 类型就是值：`Array[Int]`、`Vector[T](n)` 是普通应用，`[...]` 给隐式参数，`(...)` 给显式参数。
- `T?` 即 `Option[T]`；`const N : Int = 3`；`typealias Pair[A] = (A, A)`。
- 返回 `Type` 的函数是类型层函数，检查时会被计算：

```moonbit
fn NAry(n : Nat) -> Type {
  match n {
    Z => Int
    S(k) => (Int) -> NAry(k)
  }
}

fn sum_n(n : Nat, acc : Int) -> NAry(n) {
  match n as m return NAry(m) {
    Z => acc
    S(k) => x => sum_n(k, acc + x)
  }
}
```

## enum 与索引类型

```text
enum 名字[隐式参数](显式参数) : 索引 -> 宇宙 { 构造子 }
```

```moonbit
enum Vector[T] : Nat -> Type {
  Nil : Vector[T](0)
  Cons[n : Nat](T, Vector[T](n)) : Vector[T](S(n))
}

enum Exp : [T] -> Type {          // 索引写在 [] 中：GADT
  IntLit(Int) : Exp[Int]
  BoolLit(Bool) : Exp[Bool]
  If[T](Exp[Bool], Exp[T], Exp[T]) : Exp[T]
}

enum Sigma[A](P : (A) -> Type) {  // 后面的字段可以引用前面的字段
  MkSigma(fst : A, snd : P(fst))
}
```

- 参数在所有构造子中固定；索引随构造子变化。宇宙是 `Type` 或 `Prop`。
- 数据类型的参数总是推断的；`Cons[n](x, xs)` 中的 `[n]` 是构造子自己的隐式参数。
- 重名构造子按期望类型区分，或写 `Vector::Cons`。
- 带标签的字段：`Rect(width~ : Int)`，构造 `Rect(width=2)`，模式 `Rect(width~)`、`Circle(r, ..)`。
- `derive(Show, Eq, Compare, Hash)` 只用于只有类型参数的类型（不支持索引类型和 GADT）。

## struct

```moonbit
struct Vec[T, n : Nat] {
  to_array : Array[T]
  length_to_array : to_array.size() === n   // 依赖字段：证明
}

fn[T] Vec::from_array(xs : Array[T]) -> Vec[T, xs.size()] {
  { to_array: xs, length_to_array: Refl }
}
```

- 构造 `{ x: 1, y: 2 }`（类型由期望类型决定），更新 `{ ..p, x: 3 }`，访问 `p.x`。
- `mut` 字段：`p.x = v`；模式中只能是 `_`。元组结构体 `struct P(Int, Int)`，`type Meters Int`。
- `xs.size()` 返回 `Nat`（可以出现在类型中），`xs.length()` 返回 `Int`。

## 模式匹配

- 变量、`_`、构造子、字面量、元组、或模式 `p | q`、`p as x`、守卫 `p if c =>`、数组模式
  `[a, .. rest, z]`、区间 `'a'..='z'`、`_..<60`。
- `e is p` 是 `Bool`，在 `if`、`while`、`guard` 中绑定变量；`guard xs is Cons(h, _) else { return d }`。
- 每个 `match` 必须覆盖所有情况；带守卫的分支不计入覆盖。
- 含数组模式（或守卫中有 `is`）的 `match` 不做覆盖检查，也不细化类型。

## 依赖匹配

- 匹配变量时，构造子的索引与变量类型合一，细化上下文和目标类型。
- 合一失败的分支不可能出现，可以省略；也可以只写模式不写 `=>`，检查器确认它不可能。
- 空类型的匹配可以没有分支：`match p {}`。
- `match e as x in D[_](i) return P(i, x) { … }`：Rocq 风格，显式动机，不细化上下文。
- 匹配函数调用的结果，结果类型中的索引关系同样细化目标。

```moonbit
enum Vector[T] : Nat -> Type {
  Nil : Vector[T](0)
  Cons[n : Nat](T, Vector[T](n)) : Vector[T](S(n))
}

enum Fin : (Nat) -> Type {
  FZ[n : Nat] : Fin(S(n))
  FS[n : Nat](Fin(n)) : Fin(S(n))
}

fn[T, n : Nat] Vector::get(self : Vector[T](n), i : Fin(n)) -> T {
  match (self, i) {           // 不需要 Nil 分支：Fin(0) 是空类型
    (Cons(x, _), FZ) => x
    (Cons(_, xs), FS(j)) => xs.get(j)
  }
}
```

- **证明中的 with 抽象**：目标是命题时，被匹配的表达式（如 `x <= y`、`f(x)`）在目标中的出现被
  替换为各分支的模式，也会到目标提到的函数的定义里找。只替换匹配那一刻能找到的出现，之后计算中
  新出现的不替换。字面量模式也细化被匹配的变量。

```moonbit
fn insert(x : Int, xs : List[Int]) -> List[Int] {
  match xs {
    Nil => Cons(x, Nil)
    Cons(y, rest) => if x <= y { Cons(x, xs) } else { Cons(y, insert(x, rest)) }
  }
}

fn length(xs : List[Int]) -> Nat {
  match xs {
    Nil => Z
    Cons(_, r) => S(length(r))
  }
}

lemma insert_length(x : Int, xs : List[Int]) -> length(insert(x, xs)) === S(length(xs)) {
  match xs {
    Nil => Refl
    Cons(y, rest) =>
      match x <= y {
        true => Refl
        false => Id::cong(S, insert_length(x, rest))
      }
  }
}
```

- 匹配 `Prop` 中的证明，结果也必须在 `Prop` 中；例外是子单例（至多一个构造子、字段都是证明，
  如 `===`），匹配 `Refl` 可以改写任意类型。

## 命题与证明

- `a === b` 即 `Id[_](a)(b)`，唯一构造子 `Refl : x === x`。两边规范化后相同就用 `Refl`。
- 等式引理：`Id::sym(p)`、`Id::trans(p, q)`、`Id::cong(f, p)`、`Id::subst(p, motive, px)`。
- 两种写法：`lemma 名字[隐式](参数) -> 命题 { 证明 }`、`lemma 名字[隐式] : 命题 = 证明表达式`。
- 递归调用就是归纳假设，不检查终止。

```moonbit
lemma two_plus_two : (2 : Nat) + 2 === 4 = Refl

lemma plus_succ(n : Nat, m : Nat) -> n + S(m) === S(n + m) {
  match n {
    Z => Refl
    S(k) => Id::cong(S, plus_succ(k, m))
  }
}

lemma append_nil[T](xs : List[T]) -> xs.append(Nil) === xs {
  match xs {
    Nil => Refl
    Cons(x, rest) => Id::cong(r => List::Cons(x, r), append_nil(rest))
  }
}

enum And[A : Prop, B : Prop] : Prop {    // 自定义命题
  Conj(A, B)
}

enum Void {}

lemma zero_ne_one(p : (0 : Nat) === 1) -> Void { match p {} }
```

## 策略

`proof { … }` 每行一条策略，结果与手写的项相同：

| 策略 | 作用 |
| --- | --- |
| `intros x y`（`intro`） | 引入假设，`_` 忽略 |
| `exact e` | 用 `e` 完成目标 |
| `rfl` | 用 `Refl` 完成目标 |
| `destruct x`（`cases`） | 分情况，字段命名为 `x_0`、`x_1`… |
| `rewrite e`、`rewrite <- e`（`rw`） | 用等式改写目标 |
| `apply f` | 把目标归约为 `f` 的参数 |
| `assume h : P`（`have`） | 先假设 `P`，之后再证明 |
| `unfold f, g` | 之后可以展开 `#opaque` 函数 |

```moonbit
lemma plus_zero(n : Nat) -> n + 0 === n {
  match n {
    Z => Refl
    S(k) => Id::cong(S, plus_zero(k))
  }
}

lemma plus_succ(n : Nat, m : Nat) -> n + S(m) === S(n + m) {
  match n {
    Z => Refl
    S(k) => Id::cong(S, plus_succ(k, m))
  }
}

lemma plus_comm : forall n m : Nat, n + m === m + n = proof {
  intros n m
  destruct n
  rewrite plus_zero(m)
  rfl
  rewrite plus_succ(m, n_0)
  rewrite plus_comm(n_0, m)
  rfl
}
```

## 受控展开

```moonbit
#opaque
fn add(m : Nat, n : Nat) -> Nat {
  match m {
    Z => n
    S(k) => S(add(k, n))
  }
}

#unfold(add)
lemma add_z(n : Nat) -> add(Z, n) === n { Refl }

lemma two() -> add(1, 1) === 2 { unfold(add) { Refl } }
```

- `#opaque` 的函数在检查时不展开（也不执行），运行和编译不受影响。
- 展开：`#unfold(f)` 写在声明前（作用于定义体）；`unfold(f) { e }`（可以在类型中）；策略 `unfold f`。
- 展开是传递的：展开 `g` 时，`g` 所 `#unfold` 的函数也展开。
- `#opaque(sealed)`：除自己的定义体外不能展开。
- 可以和 `#mbt`、`#timelimit` 一起写。

## 分阶段元编程

```moonbit
fn power(n : Nat, x : Code[Int]) -> Code[Int] {
  match n {
    Z => code { 1 }
    S(k) => code { ${x} * ${power(k, x)} }
  }
}

// 检查时展开为 x * (x * (x * 1))
fn cube(x : Int) -> Int { ${ power(3, code { x }) } }

fn main {
  println(cube(3))
  println(power(10, code { 2 }).run())   // 运行时生成并运行
}
```

- `code { e }`：`e` 的代码，类型 `Code[T]`；`${ c }`（变量可写 `$c`）：拼接代码；`c.run()`：运行时运行。
- 写在函数里的拼接在检查时运行，被生成的代码替换；生成器是返回 `Code[T]` 的普通函数。
- 阶段：拼接里不能用运行时才知道的变量（把它写进 `code { }`）；生成器知道的值可以直接写进代码；
  `let mut` 变量不能跨 `code { }`。
- 效应：`code { }` 里不依赖其变量的拼接在代码生成时运行，效应属于生成器；函数里的拼接和用到代码
  变量的拼接必须是纯的。运行时有效应的代码是 `Code[T raise E]`、`Code[T!Eff]`。
- 生成器不能用数组、`print` 和导入的 MoonBit 函数；`Code` 不能被匹配。

## trait

```moonbit
trait Shape {
  area(Self) -> Int
  name(Self) -> String = _          // 有默认实现
}

impl Shape with name(_) { "shape" }  // 默认实现：不写 for

struct Square {
  side : Int
}

impl Shape for Square with area(self) { self.side * self.side }

fn[S : Shape] describe(s : S) -> String { "\{s.name()} \{s.area()}" }
```

- 每个方法一条 `impl Tr for T with m(…) { … }`；泛型实例 `impl[T : Show] Show for Box[T] with …`。
- 父 trait：`trait Solid : Shape { … }`。
- trait 对象 `&Tr`：需要 `&Tr` 的地方自动打包，如 `Array[&Show]`。
- 高阶 trait：`Monad`（`Self : [T] -> Type`），`monad { let x <- m; … }`，表达式中 `<- m`。
- Prelude trait：`Show`、`Eq`、`Compare`、`Add`、`Sub`、`Mul`、`Div`、`Mod`、`Neg`、`Default`、`Hash`、
  `ToJson`、`BitAnd`、`BitOr`、`BitXOr`、`Shl`、`Shr`、`Monad`。
- `Array` 和元组没有 `Compare` 实例。

## 可变状态与检查时执行

- `let mut`、`=`、`+=`、`while`、`for i = 0; i < n; i = i + 1`、`for x in xs`、`for i, x in xs`、
  `for k in a..<b`、`loop a, b { 模式 => … }`、`break e`、`continue`、`nobreak { … }`、标签
  `outer~:`、`defer e`。循环变量不能在循环体中赋值。
- 使用可变状态、循环、`raise`、`try` 的函数在**检查时被执行**：能跑完（判断都确定）就换成结果，
  否则保持不展开。用到数组、导入函数、async 函数或捕获 `let mut` 的 lambda 时不执行。
- 所以 `sum_to(10) === 55` 能用 `Refl` 证明，但关于变量参数的一般性质不能。

## 错误

```moonbit
suberror DivError {
  DivError(String)
}

fn div(a : Int, b : Int) -> Int raise DivError {
  if b == 0 {
    raise DivError("division by zero")
  }
  a / b
}

fn main {
  let r = try div(10, 0) catch {
    DivError(msg) => { println(msg); 0 }
  } noraise {
    v => v
  }
  println(r)
  println(try? div(10, 2))
}
```

- `raise` 不写类型即 `Error`；`fail(msg)` 抛出 `Failure`；`e catch { … }` 要在同一行。
- 检查时会抛出的调用计算为值 `raise e`，可以写进类型：`head(Nil) === raise Empty`。
- 返回证明的函数不能声明 `raise`。

## async

- `async fn f(…)`、`async fn(…) { … }`、类型 `async (A) -> B`；默认可抛任何错误，`noraise` 限定。
- async 函数只能在 async 函数中调用；`async fn main`。
- 类型上 `async` 是效应 `Async` 的糖：`-> T!Async`。
- 解释器同步执行（无并发）；编译时只编译成原生 MoonBit async。
- `moonbitlang/async`：`@async.sleep`、`@async.with_task_group(fn(g) { g.spawn_bg(…) })`，需要
  `moonpp run --compiled`。

## 代数效应

```moonbit
effect Yield[T] {
  Yield(T) -> Unit              // 默认：尾恢复，编译为普通调用
}

fn[T] iter_array(xs : Array[T]) -> Unit!Yield[T] {
  for x in xs {
    perform Yield(x)
  }
}

effect Choose {
  ctl Choose() -> Bool          // ctl：可以不恢复、恢复多次
}

fn count_trues() -> Int!Choose {
  let mut n = 0
  if perform Choose() { n = n + 1 }
  n
}

fn main {
  try { iter_array([1, 2]) } catch { Yield(x) => { println(x); resume() } }
  println(try { Cons(count_trues(), Nil) } catch {
    Choose() => resume(true).append(resume(false))
  })
}
```

- 效应行写在返回类型后：`-> T!E1 + E2`；`raise E` 即 `!Raise[E]`。
- 尾恢复操作的分支必须每条路径都以 `resume(…)` 结束，否则用 `ctl`。
- 效应变量 `fn[T, e] each(xs : List[T], f : (T) -> Unit!e) -> Unit!e`；只被调用或转传的回调可以省略
  `!e`（自动推导）；逃逸的回调要写出；`!pure` 要求纯。
- 处理器是词法的、深的。执行效应的函数不能离开处理它的 `try`。
- 限制：一个 `try` 不能同时处理错误和 `ctl` 操作；返回命题的函数不能有效应；效应不能跨包使用。

## 与 MoonBit 交互

- 导入：`moon.pkg` 的 `import { "moonbitlang/core/math", "moonbitlang/core/string" @str }`，
  用 `@math.hypot(x, y)`、`@pkg.T`、`@pkg.T::C`、`x.m()`。
- 导入的函数在检查时只有类型，解释器不能运行。
- `loc~ : SourceLoc` 等自动填充参数调用时不写。
- `#mbt` 标在 enum、struct、trait、fn 上：直接对应 MoonBit 类型、trait、公开函数（只有类型参数、
  字段是 MoonBit 类型等条件）。`#mbt("名字")` 对应已有的 MoonBit 名字。`moonpp fix` 自动加。

## Prelude

- 类型：`Int`、`Int64`、`UInt`、`UInt64`、`Byte`、`Float`、`Double`、`Bool`、`Char`、`String`、
  `Unit`、`Array[T]`、`Map[K, V]`、`Nat`（`Z`、`S`）、`Option[T]`、`Result[T, E]`、`List[T]`（`Nil`、
  `Cons`）、元组、`Error`、`Failure`。
- 函数：`println`、`print`、`abort(msg)`、`panic()`、`fail(msg)`、`not(b)`、`int_to_nat(i)`、
  `n.to_int()`、`assert_eq`、`assert_true` 等。
- `List`：`append`、`reverse`、`length`、`map`、`flat_map`（效应多态）。
- `Nat` 在检查时是一进制的，运行时（解释器和编译后）是任意精度整数：`+`、`-`（截断）、`*`、`/`、`%`
  （除以 0 得 0 / 原数）、比较、`&`、`|`、`^`、`<<`、`>>`、`gcd`、`pow`、`log2`、`to_int`、`to_bigint`、
  `Nat::of_bigint` 都是原生运算，`S(k)` 模式是减一，可以放心做大数算术。
- `BigInt`：内建的任意精度整数（导入 `moonbitlang/core/bigint` 时 `@bigint.BigInt` 就是它），
  `BigInt::from_int`、算术、位运算、比较、`pow`；检查时不计算。
- `HashMap[K, V]`（键要 `Hash + Eq`）：哈希表，接口同 `Map`；`Map` 的查找是线性的，大表用 `HashMap`。
- 元组有 `Show`、`Eq`、`Compare`、`Hash`；`ignore(x)` 丢弃一个值。
- 可判定相等：`T::deq(a, b) : Dec[a === b]`（`Yes(证明)` 或 `No(反驳)`，反驳是 `Not(P) = (P) -> False`，
  用 `absurd(nope(Refl))` 排除不可能的 `No`），基本类型（`Double` 除外）、
  `Nat`、`Option`、`List`、元组都有；trait `DecEq`；`derive(DecEq)`（同时 derive `Eq`）。
  `reflect(b) : Reflect(b)` 给出布尔值连同证明。
- `physical_equal(a, b)`、`ptr_deq(a, b) : Known[a === b]`：同一个对象时为真 / 给出证明（检查时不计算）。
- `Id::subst_prop(p, motive, px)`：`motive` 返回 `Prop` 的 `subst`。
- 程序中与 Prelude 同名的类型取代 Prelude 的（连同其方法与实例）。
- `moonpp --no-prelude` 关闭 Prelude。
