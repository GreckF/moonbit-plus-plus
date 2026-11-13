///|
/// Per-check state of the type checker.
///
/// The rule: every top-level mutable value of `tt` that must start in its
/// initial state at each check is declared with `map`, `array`, `cell` or
/// `state`, which registers its reset here; `reset_all` (called by `setup`)
/// runs them all. Declaring such state and resetting it are the same act, so
/// a reset cannot be forgotten. A mutable global that is NOT declared this way
/// has another lifetime (host configuration, reset at another moment, ...),
/// which its doc comment says. The resets are independent of each other: their
/// order does not matter.
///
/// The registry lives in its own package so that it is initialised before the
/// top-level values of the packages that import it (inside one package the
/// order of top-level initialisers does not follow calls of functions).

///|
/// The resets of the registered state, in order of declaration.
let resets : Array[() -> Unit] = []

///|
/// A registered value, put back to its initial state by `reset` at each
/// `reset_all` (the general form of the constructors below).
pub fn[T] state(value : T, reset : (T) -> Unit) -> T {
  resets.push(() => reset(value))
  value
}

///|
/// A registered map, emptied by `reset_all`.
pub fn[K : Hash + Eq, V] map() -> Map[K, V] {
  state(Map([]), m => m.clear())
}

///|
/// A registered array, emptied by `reset_all`.
pub fn[T] array() -> Array[T] {
  state([], a => a.clear())
}

///|
/// A registered reference, set back to `init` by `reset_all` (`init` must be
/// an immutable value).
pub fn[T] cell(init : T) -> Ref[T] {
  state(Ref(init), r => r.val = init)
}

///|
/// Reset all the registered state.
pub fn reset_all() -> Unit {
  for reset in resets {
    reset()
  }
}

///|
/// The number of registered resets.
pub fn count() -> Int32 {
  resets.length()
}
