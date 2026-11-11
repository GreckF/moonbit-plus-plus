---
name: mbtpp
description: Write, check, run, and compile MoonBit++ (.mbtpp) programs with the moonpp tool, and report MoonBit++ bugs. MoonBit++ is MoonBit with dependent types, proofs (lemma, ===, proof tactics), indexed enums, algebraic effects, and compilation to MoonBit. Use when editing .mbtpp files, working in a project with moon.pkg plus .mbtpp sources, running moonpp commands, debugging moonpp errors, or writing an issue for GreckF/mbtpp. 编写、检查、运行、编译 MoonBit++ 程序，使用 moonpp，报告问题。
---

# MoonBit++

MoonBit++ 是带依赖类型的 MoonBit：表达式、语句、trait、错误处理与 MoonBit 一致，另外有类型层计算、
索引类型（GADT）、依赖模式匹配、命题与证明、代数效应。`moonpp` 是它的工具：类型检查、用解释器
运行、编译成 MoonBit 项目。

- 文档：https://greckf.github.io/mbtpp/book/ （源码仓库 `book/src`）
- Playground：https://greckf.github.io/mbtpp/
- 仓库与 issue：https://github.com/GreckF/mbtpp

## 按任务读参考文件

| 任务 | 读 |
| --- | --- |
| 写或改 `.mbtpp` 代码 | [references/syntax.md](references/syntax.md) |
| 建项目、跑命令、加依赖、编译、看懂报错 | [references/moonpp.md](references/moonpp.md) |
| 报 bug、写 issue | [references/issues.md](references/issues.md) |

## 最小例子

```moonbit
enum Vector[T] : Nat -> Type {
  Nil : Vector[T](0)
  Cons[n : Nat](T, Vector[T](n)) : Vector[T](S(n))
}

// 只接受非空向量：不需要 Nil 分支
fn[T, n : Nat] Vector::head(self : Vector[T](S(n))) -> T {
  match self {
    Cons(x, _) => x
  }
}

lemma plus_zero(n : Nat) -> n + 0 === n {
  match n {
    Z => Refl
    S(k) => Id::cong(S, plus_zero(k))
  }
}

fn main {
  let v : Vector[String](2) = Cons("Hello", Cons("MoonBit++", Nil))
  println(v.head())
}
```

```bash
moonpp check main.mbtpp    # 类型检查（也检查证明）
moonpp run main.mbtpp      # 解释执行
```

## 工作流程

1. 改代码后先 `moonpp check [路径]`。检查器遇到**第一个错误就停止**，一次只报一个错误：修完再检查。
2. `moonpp run` 用解释器运行；用到导入的 MoonBit 函数（`@pkg.f`）时，必须 `moonpp run --compiled`。
3. 要得到 MoonBit 代码时 `moonpp build`，结果在 `mbtpp_out/<包名>`，可以直接 `moon run`。

## 容易出错的地方

- **导入包要两步**：`moonpp add user/module` 只把依赖写进 `moon.mod`；还要在用它的包的
  `moon.pkg` 的 `import { … }` 中列出具体的包（如 `"moonbitlang/async"`），否则报
  `unknown name @async.sleep: package @async is not imported`。
- **解释器不运行导入函数**：报 `cannot run the imported MoonBit function … in the interpreter`
  时，用 `moonpp run --compiled`。
- **隐式参数只写在 `fn` 后**：`fn[T] f(x : T)`，不能写 `fn f[T](x : T)`。
- **不柯里化**：`(Int, Int) -> Int` 和 `(Int) -> (Int) -> Int` 是不同的类型，没有部分应用。
- **三种等号**：`=` 定义，`==` 是 `Bool`，`===` 是命题（`Prop`），只能用证明（如 `Refl`）构造。
- **数字字面量**：在 `Nat` 处展开为 `S(…S(Z))`，类型不明时要标注，如 `(2 : Nat) + 2 === 4`；
  字面量不按期望类型重载，`Int64` 要写 `3L`。
- **证明靠计算**：两边规范化后相同就是 `Refl`；变量上的性质（`n + 0 === n`）要用 `match` 加递归
  归纳。没有 `simp`、`omega`、`auto`。
- **证明中的条件**：在目标是命题时，`match x <= y { true => …; false => … }` 会把目标中出现的
  `x <= y` 替换掉（自动的 with 抽象）。只替换匹配时能找到的出现。
- **`#opaque` 函数**在检查时不展开，需要定义时加 `#unfold(f)`、`unfold(f) { e }` 或策略
  `unfold f`；报错的 `hint:` 行会提示。
- **分阶段元编程**：`code { e }` 是 `e` 的代码（`Code[T]`），`${ c }` 拼接代码；写在函数里的拼接
  在检查时运行并被生成的代码替换。拼接里不能用运行时才知道的变量（报
  `x is not known when this splice runs`，把它放进 `code { }`）；生成器不能用数组、`print` 和导入的
  函数；`let mut` 变量不能跨 `code { }`，先 `let` 复制；运行时用 `c.run()`。
- **跨文件计算**：同一个包的文件按文件名字典序检查，证明要计算另一个文件中的函数时，用
  `moon.pkg` 的 `options("mbtpp-order": [ "x.mbtpp" ])` 让那个文件先检查（报错会给出 hint）。
- **`catch` 写在同一行**：`e catch { … }`；`raise Empty === x` 解析为 `raise (Empty === x)`，
  要写 `(raise Empty) === x`。
- **没有终止检查**：可以“证明”假命题；非终止的定义会在 30 秒检查时限后报错，用
  `#timelimit(秒)` 或 `#timelimit(none)` 调整。
- **Windows 上编译后运行**：`moon` 的 native 目标需要 MSVC；没有时在生成的项目里用
  `moon run main --target js`。

已知限制的完整列表在文档的“已知限制”一章（`book/src/limitations.md`）。遇到不符合文档的行为，
按 [references/issues.md](references/issues.md) 判断并报告。
