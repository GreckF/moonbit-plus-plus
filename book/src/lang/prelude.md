# Prelude

每个程序都自动加载 Prelude（`moonpp --no-prelude` 可以关闭）。程序中与 Prelude 的类型或 trait 同名的
声明取代它：Prelude 中这个类型的方法、实例和用到它的定义都不再存在（例如自己定义的 `HashMap`）。

| 名字 | 说明 |
| --- | --- |
| `Int`、`Double`、`Bool`、`Char`、`String`、`Unit`、`Array[T]`、`Error` | 内置类型 |
| `Int64`、`UInt`、`UInt64`、`Byte`、`Float` | 其他数值类型：算术、比较、位运算（整数）、`to_string`、`hash`；`to_int`、`to_double`，`Int` 的 `to_int64`、`to_uint`、`to_uint64`、`to_byte`、`to_float` 等转换 |
| `Map[K, V]` | 按插入顺序的映射：`Map::new()`、`Map::from_array`、`get`、`set`、`m[k]`（`V?`）、`m[k] = v`、`contains`、`remove`、`length`、`keys`、`values`、`to_array`；`for k, v in m`。查找是线性的 |
| `HashMap[K, V]` | 哈希表（键要有 `Hash + Eq`），按插入顺序迭代；方法与 `Map` 相同，期望类型是 `HashMap` 时 `{}`、`{ k: v }` 构造它 |
| `assert_eq`、`assert_not_eq`、`assert_true`、`assert_false` | 测试断言（抛出 `Failure`） |
| `Nat`（`Z`、`S`） | 自然数，整数字面量在 `Nat` 处展开；`+`、`-`（截断：不够减时为 0）、`*`、`/`、`%`（`n / 0` 是 0，`n % 0` 是 `n`）、`==`、`<` 等比较、`compare`、`&`、`\|`、`^`、`<<`、`>>`（移位量是 `Nat`）、`n.gcd(m)`、`n.pow(m)`、`n.log2()`（`log2(0)` 是 0）、`n.to_int()`、`int_to_nat(i)`、`n.to_bigint()`、`Nat::of_bigint(b)`（负数为 0）。检查时按一元定义计算，运行时是任意精度整数（见[编译到 MoonBit](../interop/compile.md#nat)） |
| `BigInt` | 任意精度整数（MoonBit 的 `BigInt`；导入 `moonbitlang/core/bigint` 时 `@bigint.BigInt` 就是它）：`BigInt::from_int`、`from_int64`、`to_int`、`to_int64`、算术、位运算、比较、`pow`、`to_string`、`hash`。没有字面量；检查时不计算 |
| `Id[T](x)(y)`、`===`、`Refl` | 命题相等；`Id::sym`、`Id::trans`、`Id::cong`、`Id::subst`、`Id::subst_prop` |
| `False`、`Not(P)`、`absurd`；`Dec[P]`（`Yes(P)`、`No(Not(P))`）、`T::deq`、`DecEq`、`reflect`；`physical_equal`、`ptr_deq`（`Known[P]`） | 否定、可判定相等与指针相等（见[命题相等](equality.md#可判定相等)） |
| `Code[T]`、`run` | 代码（`code { e }`）与在运行时运行它（见[分阶段元编程](staging.md)） |
| `Option[T]`（`None`、`Some`）、`T?` | 可选值 |
| `Result[T, E]`（`Ok`、`Err`） | 结果 |
| `List[T]`（`Nil`、`Cons`） | 链表：`append`、`reverse`、`length`、`map`、`flat_map` |
| `(a, b)`、`(a, b, c)` | 元组（`Tuple2`、`Tuple3`）；元素满足约束时有 `Show`、`Eq`、`Compare`、`Hash` |
| `Failure`、`fail(msg)` | 通用错误 |
| `Show`、`Eq`、`Compare`、`Add`、`Sub`、`Mul`、`Div`、`Mod`、`Neg`、`Default`、`Monad` | trait（见 [trait](traits.md)） |
| `println`、`print`、`print_string` | 输出（`println` 和 `print` 需要 `Show`） |
| `abort(msg)`、`panic()` | 终止程序 |
| `not(b)` | 布尔取反 |
| `ignore(x)` | 丢弃一个值 |

内置类型的方法：

| 类型 | 方法 |
| --- | --- |
| `Int` | 算术与比较运算符、`compare`、`to_string`、`to_double`、`unsafe_to_char` |
| `Double` | 算术与比较运算符、`compare`、`to_string`、`to_int` |
| `String` | `+`、`==`、`compare`、`length`、`s[i]`、`substring(start, end)`、`to_string` |
| `Char` | `==`、`compare`、`to_int`、`to_string` |
| `Bool` | `==`、`not`、`to_string` |
| `Array[T]` | `Array::make(n, x)`、`Array::new()`、`length`、`size`（`Nat`）、`xs[i]`、`xs[i] = v`、`push` |
