///|
/// Matching on an expression that occurs in the goal of a proof abstracts it
/// (as Agda's `with`), and literal patterns refine the scrutinee.

///|
test "matching on a comparison inside the goal" {
  inspect(
    @mbtpp.check_source(
      "t.mbtpp",
      (
        #|fn insert(x : Int, xs : List[Int]) -> List[Int] {
        #|  match xs {
        #|    Nil => Cons(x, Nil)
        #|    Cons(y, rest) => if x <= y { Cons(x, xs) } else { Cons(y, insert(x, rest)) }
        #|  }
        #|}
        #|
        #|fn length(xs : List[Int]) -> Nat {
        #|  match xs {
        #|    Nil => Z
        #|    Cons(_, r) => S(length(r))
        #|  }
        #|}
        #|
        #|lemma insert_length(x : Int, xs : List[Int]) -> length(insert(x, xs)) === S(length(xs)) {
        #|  match xs {
        #|    Nil => Refl
        #|    Cons(y, rest) =>
        #|      match x <= y {
        #|        true => Refl
        #|        false => Id::cong(S, insert_length(x, rest))
        #|      }
        #|  }
        #|}
      ),
    ),
    content="ok",
  )
}

///|
test "a literal pattern refines a variable" {
  inspect(
    @mbtpp.check_source(
      "t.mbtpp",
      (
        #|fn pick(b : Bool) -> Int { if b { 1 } else { 0 } }
        #|
        #|lemma pick_01(b : Bool) -> Id[Bool](pick(b) == 1)(b) {
        #|  match b {
        #|    true => Refl
        #|    false => Refl
        #|  }
        #|}
      ),
    ),
    content="ok",
  )
}
