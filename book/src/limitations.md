# 已知限制

## 语言

- 没有终止检查和严格正性检查（按设计）：可以“证明”假命题。
- 没有 `simp`、`omega`、`auto` 等自动化策略。代数效应的限制见[代数效应](lang/effects.md#限制)。
- 递归的局部函数不能使用外层的 `let mut` 变量。
- `Show` 不给容器中的字符串和字符加引号：`println(Some("x"))` 输出 `Some(x)`，MoonBit 输出
  `Some("x")`。
- 泛型实例与更具体的实例重叠时（`impl[T] Tr for Array[T]` 和 `impl Tr for Array[Int]`），不报错，
  使用先找到的泛型实例；MoonBit 拒绝这样的程序。同一类型的同一方法实现两次会报错。
- `Array` 没有 `Compare` 实例；整数字面量不按期望类型重载（`let x : Int64 = 3` 要写 `3L`）。
- 对证明（非子单例的 `Prop`）的匹配可以出现在结果是证明的地方，但分支中的副作用（输出、修改
  变量）在编译后的程序中不会发生，因为证明被擦除。
- 比较运算符可以连写（`a == b == c` 按左结合解析），MoonBit 不允许。
- 含数组模式的 `match` 不做覆盖检查，也不细化类型。
- `Map` 和 `HashMap` 是 Prelude 用 MoonBit++ 实现的（`Map` 的查找是线性的，大的表用 `HashMap`），不是
  MoonBit 的 `Map`、`HashMap`：参数或返回值是 MoonBit 的这些类型的导入函数不能调用。
- 没有 `BigInt` 字面量（`1N`）、`Int16`、`UInt16`；导入的 `@bigint` 中与 Prelude 同名的 `BigInt` 方法（如带
  `radix?` 的 `to_string`）被 Prelude 的取代；`Float` 的方法只有运算、比较和转换。
- 类型检查时执行非纯函数时，用到数组、导入函数或捕获 `let mut` 的 lambda 的调用不执行（见[可变状态与循环](lang/mutation.md)）。
- 分阶段元编程的限制见[分阶段元编程](lang/staging.md#限制)：写在函数里的拼接由检查器运行，生成器不能用
  数组、`print` 和导入的函数；用到所在代码变量的拼接不能有效应；生成代码里嵌套在另一个局部递归函数中的
  局部递归函数不会被特化（它的拼接留到运行时）。
- 检查时限按实际时间计算，同一个文件在较慢的机器上可能超时（见[检查时限](lang/type-level.md#检查时限)）。

## 导入

- 解释器不能运行导入的 MoonBit 函数，只能在编译后调用。
- `moonpp test` 不能使用只为测试导入的包（`for "test"`）。
- 导入 `moonbitlang/core/builtin` 会让检查器崩溃。
- 解释器同步执行 async 函数，没有并发；async 函数只编译成原生代码（见 [async 函数](lang/async.md)）。
- 返回 trait 对象 `&Tr` 的导入函数还不能编译；其他不导入的项见[类型对应与不导入的项](interop/types.md)。

## 编译器

- `Hash` 的值在解释器和编译后的程序中不同（编译后用 MoonBit 的哈希）。
- 统一表示与原生代码之间按值转换，频繁跨边界传递大型数据会慢。
- 原生代码中的运行时错误（越界、除以零等）直接终止程序，不执行 `defer`；解释器和统一表示会先执行
  `defer`。

## 工具

- 生成的项目总是 main 包，不能生成库包。
- 需要新版 `moon`（使用 `moon.mod` / `moon.pkg`）。
