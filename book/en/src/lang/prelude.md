# Prelude

The Prelude is loaded automatically into every program (`moonpp --no-prelude` turns it off). A
declaration of the program with the name of a Prelude type or trait replaces it: the Prelude's
methods and instances of that type, and its definitions using it, are gone (your own `HashMap`,
say).

| Name | Description |
| --- | --- |
| `Int`, `Double`, `Bool`, `Char`, `String`, `Unit`, `Array[T]`, `Error` | Built-in types |
| `Int64`, `UInt`, `UInt64`, `Byte`, `Float` | Other numeric types: arithmetic, comparison, bitwise operators (integers), `to_string`, `hash`; conversions `to_int`, `to_double`, and `Int`'s `to_int64`, `to_uint`, `to_uint64`, `to_byte`, `to_float`, etc. |
| `Map[K, V]` | A map in insertion order: `Map::new()`, `Map::from_array`, `get`, `set`, `m[k]` (a `V?`), `m[k] = v`, `contains`, `remove`, `length`, `keys`, `values`, `to_array`; `for k, v in m`. Lookups are linear |
| `HashMap[K, V]` | A hash table (keys with `Hash + Eq`), iterated in insertion order; the same methods as `Map`, and `{}`, `{ k: v }` build one where a `HashMap` is expected |
| `assert_eq`, `assert_not_eq`, `assert_true`, `assert_false` | Test assertions (they raise `Failure`) |
| `Nat` (`Z`, `S`) | Natural numbers; integer literals expand at type `Nat`; `+`, `-` (truncated: 0 when the subtrahend is larger), `*`, `/`, `%` (`n / 0` is 0, `n % 0` is `n`), `==`, `<` and the other comparisons, `compare`, `&`, `\|`, `^`, `<<`, `>>` (shifting by a `Nat`), `n.gcd(m)`, `n.pow(m)`, `n.log2()` (`log2(0)` is 0), `n.to_int()`, `int_to_nat(i)`, `n.to_bigint()`, `Nat::of_bigint(b)` (negative numbers give 0). Unary definitions when checking, arbitrary-precision integers at run time (see [Compiling to MoonBit](../interop/compile.md#nat)) |
| `BigInt` | Arbitrary-precision integers (MoonBit's `BigInt`; `@bigint.BigInt` is this type when `moonbitlang/core/bigint` is imported): `BigInt::from_int`, `from_int64`, `to_int`, `to_int64`, arithmetic, bitwise operators, comparisons, `pow`, `to_string`, `hash`. No literals; not computed during checking |
| `Id[T](x)(y)`, `===`, `Refl` | Propositional equality; `Id::sym`, `Id::trans`, `Id::cong`, `Id::subst`, `Id::subst_prop` |
| `False`, `Not(P)`, `absurd`; `Dec[P]` (`Yes(P)`, `No(Not(P))`), `T::deq`, `DecEq`, `reflect`; `physical_equal`, `ptr_deq` (`Known[P]`) | Negation, decidable and pointer equality (see [Propositional Equality](equality.md#decidable-equality)) |
| `Code[T]`, `run` | Code (`code { e }`) and running it at run time (see [Staged Metaprogramming](staging.md)) |
| `Option[T]` (`None`, `Some`), `T?` | Optional values |
| `Result[T, E]` (`Ok`, `Err`) | Results |
| `List[T]` (`Nil`, `Cons`) | Linked lists: `append`, `reverse`, `length`, `map`, `flat_map` |
| `(a, b)`, `(a, b, c)` | Tuples (`Tuple2`, `Tuple3`); `Show`, `Eq`, `Compare`, `Hash` when their elements have them |
| `Failure`, `fail(msg)` | General-purpose error |
| `Show`, `Eq`, `Compare`, `Add`, `Sub`, `Mul`, `Div`, `Mod`, `Neg`, `Default`, `Monad` | Traits (see [Traits](traits.md)) |
| `println`, `print`, `print_string` | Output (`println` and `print` require `Show`) |
| `abort(msg)`, `panic()` | Terminate the program |
| `not(b)` | Boolean negation |
| `ignore(x)` | Discards a value |

Methods on built-in types:

| Type | Methods |
| --- | --- |
| `Int` | Arithmetic and comparison operators, `compare`, `to_string`, `to_double`, `unsafe_to_char` |
| `Double` | Arithmetic and comparison operators, `compare`, `to_string`, `to_int` |
| `String` | `+`, `==`, `compare`, `length`, `s[i]`, `substring(start, end)`, `to_string` |
| `Char` | `==`, `compare`, `to_int`, `to_string` |
| `Bool` | `==`, `not`, `to_string` |
| `Array[T]` | `Array::make(n, x)`, `Array::new()`, `length`, `size` (`Nat`), `xs[i]`, `xs[i] = v`, `push` |
