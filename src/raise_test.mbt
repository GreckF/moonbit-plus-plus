///|
/// Errors as values of the logic (see src/tt/raise.mbt).

///|
test "errors are values of the logic" {
  inspect(
    check(
      (
        #|suberror Empty
        #|suberror Other
        #|fn head(xs : List[Int]) -> Int raise Empty {
        #|  match xs {
        #|    Nil => raise Empty
        #|    Cons(x, _) => x
        #|  }
        #|}
        #|fn const0(x : Int) -> Int { 0 }
        #|lemma head_nil() -> head(Nil) === raise Empty { Refl }
        #|lemma head_cons(x : Int, xs : List[Int]) -> head(Cons(x, xs)) === x { Refl }
        #|lemma caught() -> (try { head(Nil); true } catch { _ => false }) === false { Refl }
        #|lemma not_raised(x : Int, xs : List[Int]) ->
        #|  (try { head(Cons(x, xs)); true } catch { _ => false }) === true { Refl }
        #|lemma passed_on() -> (try { head(Nil) } catch { Other => 0 }) === raise Empty { Refl }
        #|lemma propagates() -> const0(head(Nil)) + 1 === raise Empty { Refl }
        #|lemma in_match() -> (match head(Nil) { _ => 0 }) === raise Empty { Refl }
        #|lemma sym() -> (raise Empty) === head(Nil) { Id::sym(head_nil()) }
        #|lemma variables_are_values(x : Int) -> const0(x) === 0 { Refl }
        #|enum Void {}
        #|lemma not_a_value(p : head(Nil) === 0) -> Void { match p {} }
      ),
    ),
    content=(
      #|ok
    ),
  )
}

///|
test "a call on an argument that may raise is not unfolded" {
  inspect(
    check(
      (
        #|suberror Empty
        #|suberror Other
        #|fn head(xs : List[Int]) -> Int raise Empty {
        #|  match xs {
        #|    Nil => raise Empty
        #|    Cons(x, _) => x
        #|  }
        #|}
        #|fn const0(x : Int) -> Int { 0 }
        #|lemma bad(xs : List[Int]) -> const0(head(xs)) === 0 { Refl }
      ),
    ),
    content=(
      #|t.mbtpp:10:55: error: type mismatch
      #|  expected: const0(head(xs)) === 0
      #|  actual:   ?868(xs) === ?868(xs)
    ),
  )
}

///|
test "an error is not a value" {
  inspect(
    check(
      (
        #|suberror Empty
        #|suberror Other
        #|fn head(xs : List[Int]) -> Int raise Empty {
        #|  match xs {
        #|    Nil => raise Empty
        #|    Cons(x, _) => x
        #|  }
        #|}
        #|fn const0(x : Int) -> Int { 0 }
        #|lemma bad() -> head(Nil) === 0 { Refl }
      ),
    ),
    content=(
      #|t.mbtpp:10:34: error: type mismatch
      #|  expected: head(Nil) === 0
      #|  actual:   ?869(_) === ?869(_)
    ),
  )
}

///|
test "errors are compared" {
  inspect(
    check(
      (
        #|suberror Empty
        #|suberror Other
        #|fn head(xs : List[Int]) -> Int raise Empty {
        #|  match xs {
        #|    Nil => raise Empty
        #|    Cons(x, _) => x
        #|  }
        #|}
        #|fn const0(x : Int) -> Int { 0 }
        #|lemma bad() -> head(Nil) === raise Other { Refl }
      ),
    ),
    content=(
      #|t.mbtpp:10:44: error: type mismatch
      #|  expected: head(Nil) === (raise Other)
      #|  actual:   ?869(_) === ?869(_)
    ),
  )
}

///|
test "a lambda does not catch the error of its argument" {
  inspect(
    check(
      (
        #|suberror Empty
        #|suberror Other
        #|fn head(xs : List[Int]) -> Int raise Empty {
        #|  match xs {
        #|    Nil => raise Empty
        #|    Cons(x, _) => x
        #|  }
        #|}
        #|fn const0(x : Int) -> Int { 0 }
        #|lemma bad() -> ((x : Int) => 0)(head(Nil)) === 0 { Refl }
      ),
    ),
    content=(
      #|t.mbtpp:10:52: error: type mismatch
      #|  expected: (raise Empty) === 0
      #|  actual:   ?871(_) === ?871(_)
    ),
  )
}

///|
test "a match does not catch the error of its scrutinee" {
  inspect(
    check(
      (
        #|suberror Empty
        #|suberror Other
        #|fn head(xs : List[Int]) -> Int raise Empty {
        #|  match xs {
        #|    Nil => raise Empty
        #|    Cons(x, _) => x
        #|  }
        #|}
        #|fn const0(x : Int) -> Int { 0 }
        #|lemma bad() -> (match head(Nil) { _ => 0 }) === 0 { Refl }
      ),
    ),
    content=(
      #|t.mbtpp:10:53: error: type mismatch
      #|  expected: (raise Empty) === 0
      #|  actual:   ?870(_) === ?870(_)
    ),
  )
}

///|
test "the implicit arguments of a lemma are values" {
  inspect(
    check(
      (
        #|suberror Empty
        #|suberror Other
        #|fn head(xs : List[Int]) -> Int raise Empty {
        #|  match xs {
        #|    Nil => raise Empty
        #|    Cons(x, _) => x
        #|  }
        #|}
        #|fn const0(x : Int) -> Int { 0 }
        #|lemma zero[n : Int]() -> const0(n) === 0 { Refl }
        #|lemma bad() -> const0(head(Nil)) === 0 { zero() }
      ),
    ),
    content=(
      #|t.mbtpp:11:46: error: type mismatch
      #|  expected: const0(head(Nil)) === 0
      #|  actual:   const0(?870(_)) === 0
    ),
  )
}

///|
test "a function that returns a proof cannot raise" {
  inspect(
    check(
      (
        #|suberror Empty
        #|suberror Other
        #|fn head(xs : List[Int]) -> Int raise Empty {
        #|  match xs {
        #|    Nil => raise Empty
        #|    Cons(x, _) => x
        #|  }
        #|}
        #|fn const0(x : Int) -> Int { 0 }
        #|fn bad() -> 1 === 1 raise Empty { Refl }
      ),
    ),
    content=(
      #|t.mbtpp:10:27: error: a function that returns a proof cannot raise errors (proofs are erased at run time)
    ),
  )
}

///|
test "a proof cannot call a function that raises" {
  inspect(
    check(
      (
        #|suberror Empty
        #|suberror Other
        #|fn head(xs : List[Int]) -> Int raise Empty {
        #|  match xs {
        #|    Nil => raise Empty
        #|    Cons(x, _) => x
        #|  }
        #|}
        #|fn const0(x : Int) -> Int { 0 }
        #|lemma bad() -> head(Nil) === head(Nil) { let _ = head(Nil); Refl }
      ),
    ),
    content=(
      #|t.mbtpp:10:54: error: this call may raise an error; use it inside `try` or in a function declared with `raise`
    ),
  )
}

///|
test "at run time, the error of the argument comes first" {
  inspect(
    run_source(
      "t.mbtpp",
      (
        #|suberror Empty
        #|suberror Other
        #|fn head(xs : List[Int]) -> Int raise Empty {
        #|  match xs {
        #|    Nil => raise Empty
        #|    Cons(x, _) => x
        #|  }
        #|}
        #|fn const0(x : Int) -> Int { 0 }
        #|fn main {
        #|  println(try { const0(head(Nil)) } catch { Empty => -1 })
        #|  println(try { const0(head(Cons(1, Nil))) } catch { Empty => -1 })
        #|}
      ),
    ),
    content=(
      #|-1
      #|0
      #|
    ),
  )
}

///|
test "the raise analysis is not remembered between checks" {
  let raising =
    #|suberror E
    #|fn fN(x : Int) -> Int raise E { if x == 0 { raise E } else { x } }
    #|fn const0(x : Int) -> Int { 0 }
    #|lemma l(x : Int) -> const0(fN(x)) === 0 { Refl }
  let pure_ =
    #|fn fN(x : Int) -> Int { if x == 0 { 1 } else { x } }
    #|fn const0(x : Int) -> Int { 0 }
    #|lemma l(x : Int) -> const0(fN(x)) === 0 { Refl }
  // a function of the same name is pure in one program and raises in another
  let a = check(raising.replace_all(old="fN", new="fa"))
  inspect(a.contains("type mismatch"), content="true")
  inspect(check(pure_.replace_all(old="fN", new="fb")), content="ok")
  let c = check(raising.replace_all(old="fN", new="fb"))
  inspect(c.contains("type mismatch"), content="true")
}
