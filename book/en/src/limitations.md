# Known Limitations

## Language

- No termination checking or strict positivity checking (by design): you can "prove" false propositions.
- No automation tactics such as `simp`, `omega`, or `auto`. For the limits of algebraic effects, see [Algebraic Effects](lang/effects.md#limitations).
- Recursive local functions cannot use the `let mut` variables around them.
- `Show` does not quote strings and characters inside containers: `println(Some("x"))` prints
  `Some(x)`, where MoonBit prints `Some("x")`.
- A generic instance overlapping a more specific one (`impl[T] Tr for Array[T]` and
  `impl Tr for Array[Int]`) is not an error, and the generic one found first is used; MoonBit
  rejects such programs. Implementing the same method twice for the same type is an error.
- `Array` has no `Compare` instance; integer literals are not overloaded by the expected
  type (`let x : Int64 = 3` needs `3L`).
- A match on a proof (of a `Prop` that is not a subsingleton) may appear where the result is a
  proof, but the side effects of its arms (output, assignments) do not happen in the compiled
  program, where proofs are erased.
- Comparison operators can be chained (`a == b == c` parses left-associatively); MoonBit does not
  allow it.
- A `match` with array patterns is not checked for coverage and does not refine types.
- `Map` and `HashMap` are implemented in MoonBit++ by the Prelude (`Map` has linear lookups; use
  `HashMap` for large tables); they are not MoonBit's `Map` and `HashMap`, so imported functions
  taking or returning those MoonBit types cannot be called.
- There are no `BigInt` literals (`1N`), `Int16` or `UInt16`; the methods of the imported `@bigint`
  named like the Prelude's `BigInt` methods (`to_string` with `radix?`) give way to the Prelude's; `Float` only has its operators,
  comparisons and conversions.
- When functions with mutable state are run during type checking, calls that use arrays, imported functions or lambdas capturing `let mut` variables are not run (see [Mutable State and Loops](lang/mutation.md)).
- The limitations of staged metaprogramming are in [Staged Metaprogramming](lang/staging.md#limitations): a splice written in a function is run by the checker, so generators cannot use arrays, `print` or imported functions; a splice that uses the variables of the code it is in cannot have effects; in generated code, a recursive local function nested in another one is not specialized (its splices are left for run time).
- Time limits are measured in wall-clock time, so a file may time out on a slower machine (see [Time limits](lang/type-level.md#time-limits)).

## Imports

- The interpreter cannot run imported MoonBit functions; they can only be called after compilation.
- `moonpp test` cannot use packages imported for tests only (`for "test"`).
- Importing `moonbitlang/core/builtin` crashes the checker.
- The interpreter runs async functions synchronously, without concurrency; async functions are only compiled to native code (see [async Functions](lang/async.md)).
- Imported functions returning a trait object `&Tr` cannot be compiled yet; for the other items that are not imported, see [Type mapping and items not imported](interop/types.md).

## Compiler

- `Hash` values differ between the interpreter and the compiled program (which uses MoonBit's hashes).
- Values are converted by value between the uniform representation and native code, so frequently passing large data across the boundary is slow.
- A runtime error in native code (an index out of bounds, a division by zero, ...) stops the program
  without running `defer`s; the interpreter and the uniform code run them first.

## Tooling

- The generated project is always a main package; library packages cannot be generated.
- Requires a recent `moon` (one that uses `moon.mod` / `moon.pkg`).
