///|
/// The signatures of the functions generated for a program (the lines
/// starting with `fn`, without the numbering of the identifiers), and the
/// native enums.
fn signatures(src : String) -> String {
  @tt.check_program("t.mbtpp", src) catch {
    @tt.CheckError(msg) => return msg
  }
  let code = @codegen.generate([]) catch {
    @codegen.CodegenError(msg) => return msg
  }
  let out : Array[String] = []
  for line in code.split("\n") {
    let l = line.to_owned()
    // `async fn f` is shown as such, and filtered as `fn f`
    let is_async = l.has_prefix("async fn")
    let l = if is_async {
      l.unsafe_substring(start=6, end=l.length())
    } else {
      l
    }
    if (
        l.has_prefix("fn") &&
        !l.contains("_v()") &&
        !l.contains("_to_value") &&
        !l.contains("_of_value") &&
        !l.contains("fn con_name") &&
        !l.contains("fn con_fields") &&
        !l.has_prefix("fn init")
      ) ||
      l.has_prefix("enum E_") ||
      l.has_prefix("struct E_") {
      out.push((if is_async { "async " } else { "" }) + strip_counters(l))
    }
  }
  out.join("\n")
}

///|
/// Drop the counters of generated names: f12_fib -> f_fib, x_34 -> x.
fn strip_counters(l : String) -> String {
  let buf = StringBuilder()
  let cs : Array[Char] = l.iter().collect()
  let mut i = 0
  while i < cs.length() {
    let c = cs[i]
    if (c == '_' || (c == 'f' && (i == 0 || !is_word(cs[i - 1])))) &&
      i + 1 < cs.length() &&
      cs[i + 1] >= '0' &&
      cs[i + 1] <= '9' &&
      (c == 'f' || (i > 0 && is_word(cs[i - 1]))) {
      buf.write_char(if c == 'f' { 'f' } else { ' ' })
      i = i + 1
      while i < cs.length() && cs[i] >= '0' && cs[i] <= '9' {
        i = i + 1
      }
      if c == '_' {
        // `x_34` -> `x`
        let s = buf.to_string()
        buf.reset()
        buf.write_string(s.unsafe_substring(start=0, end=s.length() - 1))
      }
    } else {
      buf.write_char(c)
      i = i + 1
    }
  }
  buf.to_string()
}

///|
/// The generated code of the global function `name` (its definitions `f`
/// and `f_t`), without counters.
fn fn_code(src : String, name : String) -> String {
  @tt.check_program("t.mbtpp", src) catch {
    @tt.CheckError(msg) => return msg
  }
  let code = @codegen.generate([]) catch {
    @codegen.CodegenError(msg) => return msg
  }
  let out : Array[String] = []
  let mut inside = false
  for line in code.split("\n") {
    let l = strip_counters(line.to_owned())
    if l.has_prefix("fn f_" + name + "(") ||
      l.has_prefix("fn f_" + name + "_t(") {
      inside = true
    }
    if inside {
      out.push(l)
      if l == "}" {
        inside = false
      }
    }
  }
  out.join("\n")
}

///|
fn is_word(c : Char) -> Bool {
  (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z') || (c >= '0' && c <= '9')
}

///|
test "codegen: native functions over scalars" {
  inspect(
    signatures(
      (
        #|fn fib(n : Int) -> Int { if n < 2 { n } else { fib(n - 1) + fib(n - 2) } }
        #|fn main { println(fib(10)) }
      ),
    ),
    content=(
      #|fn f_main_init() -> Unit raise {
      #|fn f_fib_t(n : Int) -> Int {
      #|fn f_fib(a0 : Value) -> Value raise {
      #|fn main {
      #|fn[T0 : Show] f_println_t(x : T0) -> Unit raise {
      #|fn f_println(v_inst_t : Value, x : Value) -> Value raise {
      #|fn f_show_to_string(inst : Value) -> Value raise {
    ),
  )
}

///|
test "codegen: indexed datatypes become generic enums; indices are erased" {
  inspect(
    signatures(
      (
        #|enum Vector[T] : Nat -> Type {
        #|  Nil : Vector[T](0)
        #|  Cons[n : Nat](T, Vector[T](n)) : Vector[T](S(n))
        #|}
        #|fn[T, n : Nat, m : Nat] Vector::append(self : Vector[T](n), ys : Vector[T](m)) -> Vector[T](n + m) {
        #|  match self {
        #|    Nil => ys
        #|    Cons(x, xs) => Cons(x, xs.append(ys))
        #|  }
        #|}
        #|fn[T, U, n : Nat] Vector::map(self : Vector[T](n), f : (T) -> U) -> Vector[U](n) {
        #|  match self {
        #|    Nil => Nil
        #|    Cons(x, xs) => Cons(f(x), xs.map(f))
        #|  }
        #|}
        #|fn main {
        #|  let v : Vector[Int](1) = Cons(1, Nil)
        #|  let w = v.append(v).map(x => x + 1)
        #|}
      ),
    ),
    content=(
      #|enum E_Vector[T0] {
      #|fn f_main_init() -> Unit raise {
      #|fn[T0, T1] f_vector_map_t(self : E_Vector[T0], f : (T0) -> T1 raise) -> E_Vector[T1] raise {
      #|fn f_vector_map(a4 : Value, a5 : Value) -> Value raise {
      #|fn[T0] f_vector_append_t(self : E_Vector[T0], ys : E_Vector[T0]) -> E_Vector[T0] {
      #|fn f_vector_append(a3 : Value, a4 : Value) -> Value raise {
      #|fn main {
    ),
  )
}

///|
test "codegen: an implicit field used at runtime is kept" {
  inspect(
    signatures(
      (
        #|enum Vector[T] : Nat -> Type {
        #|  Nil : Vector[T](0)
        #|  Cons[n : Nat](T, Vector[T](n)) : Vector[T](S(n))
        #|}
        #|fn[T, n : Nat] len(v : Vector[T](n)) -> Nat {
        #|  match v {
        #|    Nil => Z
        #|    Cons[m](_, _) => S(m)
        #|  }
        #|}
        #|fn main { println(len(Vector::Cons(1, Nil))) }
      ),
    ),
    content=(
      #|enum E_Vector[T0] {
      #|fn f_main_init() -> Unit raise {
      #|fn[T0] f_len_t(v : E_Vector[T0]) -> BigInt {
      #|fn f_len(a2 : Value) -> Value raise {
      #|fn main {
      #|fn[T0 : Show] f_println_t(x : T0) -> Unit raise {
      #|fn f_println(v_inst_t : Value, x : Value) -> Value raise {
      #|fn f_show_to_string(inst : Value) -> Value raise {
    ),
  )
}

///|
test "codegen: dependent results stay uniform" {
  inspect(
    signatures(
      (
        #|fn NAry(n : Nat) -> Type {
        #|  match n {
        #|    Z => Int
        #|    S(k) => (Int) -> NAry(k)
        #|  }
        #|}
        #|fn sum_n(n : Nat, acc : Int) -> NAry(n) {
        #|  match n as m return NAry(m) {
        #|    Z => acc
        #|    S(k) => x => sum_n(k, acc + x)
        #|  }
        #|}
        #|fn main { println(sum_n(2, 0)(1)(2)) }
      ),
    ),
    content=(
      #|fn f_sum_n(n : Value, acc : Value) -> Value raise {
      #|fn main {
      #|fn[T0 : Show] f_println_t(x : T0) -> Unit raise {
      #|fn f_println(v_inst_t : Value, x : Value) -> Value raise {
      #|fn f_show_to_string(inst : Value) -> Value raise {
    ),
  )
}

///|
/// The MoonBit declarations generated for `#mbt` types and traits.
fn mbt_decls(src : String) -> String {
  @tt.check_program("t.mbtpp", src) catch {
    @tt.CheckError(msg) => return msg
  }
  let code = @codegen.generate([]) catch {
    @codegen.CodegenError(msg) => return msg
  }
  let out : Array[String] = []
  let mut inside = false
  for line in code.split("\n") {
    let l = line.to_owned()
    if l.has_prefix("enum Tree") ||
      l.has_prefix("struct ") ||
      l.has_prefix("trait ") ||
      l.has_prefix("impl") {
      inside = !l.has_prefix("impl")
      out.push(l)
    } else if inside {
      out.push(l)
      if l == "}" {
        inside = false
      }
    }
  }
  out.join("\n")
}

///|
test "codegen: #mbt types and traits" {
  inspect(
    mbt_decls(
      (
        #|#mbt
        #|enum Tree[T] { Leaf; Node(Tree[T], T, Tree[T]) }
        #|#mbt
        #|struct P { x : Int; y : Int }
        #|#mbt
        #|trait Size { size(Self) -> Int }
        #|impl Size for P with size(self) { self.x + self.y }
        #|impl[T : Size] Size for Tree[T] with size(self) {
        #|  match self {
        #|    Leaf => 0
        #|    Node(l, x, r) => l.size() + x.size() + r.size()
        #|  }
        #|}
        #|fn[T : Size] total(t : Tree[T]) -> Int { t.size() }
        #|fn sizes(t : Tree[P]) -> Int { total(t) }
        #|fn main { println(sizes(Node(Leaf, { x: 1, y: 2 }, Leaf))) }
      ),
    ),
    content=(
      #|impl Size for P with size(a0) {
      #|impl[T0 : Size] Size for Tree[T0] with size(a0) {
    ),
  )
}

///|
test "codegen: #mbt functions must be native" {
  inspect(
    signatures(
      (
        #|trait Sz { size(Self) -> Int }
        #|impl Sz for Int with size(self) { self }
        #|#mbt
        #|fn f(x : Int) -> Int { x.size() }
        #|fn main { println(f(1)) }
      ),
    ),
    content=(
      #|#mbt fn f cannot be compiled to MoonBit: its body is not in the native fragment: in `Sz::size(x)`, Sz::size is a method of the trait Sz, which is not #mbt
    ),
  )
  inspect(
    signatures(
      (
        #|#mbt
        #|fn twice(x : Int) -> Int { x + x }
        #|fn main { println(1) }
      ),
    ),
    content=(
      #|fn f_twice_t(x : Int) -> Int {
      #|fn f_twice(a0 : Value) -> Value raise {
      #|fn f_main_init() -> Unit raise {
      #|fn main {
      #|fn[T0 : Show] f_println_t(x : T0) -> Unit raise {
      #|fn f_println(v_inst_t : Value, x : Value) -> Value raise {
      #|fn f_show_to_string(inst : Value) -> Value raise {
    ),
  )
}

///|
/// The constructor variants of `Value` and the patterns matching them.
fn data_lines(src : String) -> String {
  @tt.check_program("t.mbtpp", src) catch {
    @tt.CheckError(msg) => return msg
  }
  let code = @codegen.generate([]) catch {
    @codegen.CodegenError(msg) => return msg
  }
  code
  .split("\n")
  .map(l => l.to_owned().trim(chars=" ").to_owned())
  .filter(l => l.has_prefix("K_Exp"))
  .map(l => {
    // drop the counters of local names: n_176 -> n
    let buf = StringBuilder()
    let cs : Array[Char] = l.iter().collect()
    let mut i = 0
    while i < cs.length() {
      if cs[i] == '_' &&
        i + 1 < cs.length() &&
        cs[i + 1] >= '0' &&
        cs[i + 1] <= '9' &&
        i > 0 &&
        cs[i - 1] >= 'a' &&
        cs[i - 1] <= 'z' {
        i = i + 1
        while i < cs.length() && cs[i] >= '0' && cs[i] <= '9' {
          i = i + 1
        }
      } else {
        buf.write_char(cs[i])
        i = i + 1
      }
    }
    buf.to_string()
  })
  .to_array()
  .join("\n")
}

///|
test "codegen: data are native variants of Value, without indices" {
  inspect(
    data_lines(
      (
        #|enum Exp : [T] -> Type {
        #|  IntLit(Int) : Exp[Int]
        #|  BoolLit(Bool) : Exp[Bool]
        #|  Add(Exp[Int], Exp[Int]) : Exp[Int]
        #|  If[T](Exp[Bool], Exp[T], Exp[T]) : Exp[T]
        #|}
        #|fn[T] Exp::eval(self : Exp[T]) -> T {
        #|  match self {
        #|    IntLit(n) => n
        #|    BoolLit(b) => b
        #|    Add(l, r) => l.eval() + r.eval()
        #|    If[_](c, t, f) => if c.eval() { t.eval() } else { f.eval() }
        #|  }
        #|}
        #|fn main { println(If(BoolLit(true), IntLit(1), IntLit(2)).eval()) }
      ),
    ),
    content=(
      #|K_Exp_IntLit(Value)
      #|K_Exp_BoolLit(Value)
      #|K_Exp_Add(Value, Value)
      #|K_Exp_If(Value, Value, Value)
      #|K_Exp_IntLit(a0) => Some(("Exp::IntLit", [a0]))
      #|K_Exp_BoolLit(a0) => Some(("Exp::BoolLit", [a0]))
      #|K_Exp_Add(a0, a1) => Some(("Exp::Add", [a0, a1]))
      #|K_Exp_If(a0, a1, a2) => Some(("Exp::If", [a0, a1, a2]))
      #|K_Exp_IntLit(a0) => E_Exp::IntLit(as_int(a0))
      #|K_Exp_BoolLit(a0) => E_Exp::BoolLit(as_bool(a0))
      #|K_Exp_Add(a0, a1) => E_Exp::Add(exp_of_value(a0), exp_of_value(a1))
      #|K_Exp_If(a1, a2, a3) => E_Exp::If(exp_of_value(a1), exp_of_value(a2), exp_of_value(a3))
    ),
  )
}

///|
test "codegen: proofs are erased" {
  inspect(
    signatures(
      (
        #|enum Le : (Nat, Nat) -> Prop {
        #|  LeZ[n : Nat] : Le(0, n)
        #|  LeS[m : Nat, n : Nat](Le(m, n)) : Le(S(m), S(n))
        #|}
        #|lemma le_refl[n : Nat] : Le(n, n) = match n {
        #|  Z => LeZ
        #|  S(k) => LeS(le_refl[k])
        #|}
        #|#mbt
        #|fn dec(n : Int, p : Le(1, 1)) -> Int { n - 1 }
        #|fn[T] cast(p : (1 : Nat) === 1, v : T) -> T { v }
        #|fn main {
        #|  let q : Le(2, 2) = le_refl
        #|  println(dec(cast(Id::Refl, 3), le_refl))
        #|}
      ),
    ),
    content=(
      #|fn f_dec_t(n : Int) -> Int {
      #|fn f_dec(a0 : Value) -> Value raise {
      #|fn f_main_init() -> Unit raise {
      #|fn[T0] f_cast_t(v : T0) -> T0 {
      #|fn f_cast(a2 : Value) -> Value raise {
      #|fn main {
      #|fn[T0 : Show] f_println_t(x : T0) -> Unit raise {
      #|fn f_println(v_inst_t : Value, x : Value) -> Value raise {
      #|fn f_show_to_string(inst : Value) -> Value raise {
    ),
  )
}

///|
test "codegen: async functions are native" {
  inspect(
    signatures(
      (
        #|async fn twice(f : async () -> Int) -> Int { f() + f() }
        #|async fn one() -> Int noraise { 1 }
        #|async fn main { println(twice(fn() { one() })) }
      ),
    ),
    content=(
      #|async fn f_twice_t(f : async () -> Int raise) -> Int raise {
      #|async fn f_one_t(v : Unit) -> Int raise {
      #|async fn main {
      #|fn[T0 : Show] f_println_t(x : T0) -> Unit raise {
      #|fn f_println(v_inst_t : Value, x : Value) -> Value raise {
      #|fn f_show_to_string(inst : Value) -> Value raise {
    ),
  )
  inspect(
    signatures(
      (
        #|fn NAry(n : Nat) -> Type { match n { Z => Int; S(k) => (Int) -> NAry(k) } }
        #|fn z(n : Nat) -> NAry(n) {
        #|  match n as m return NAry(m) { Z => 0; S(k) => _ => z(k) }
        #|}
        #|async fn g(n : Nat) -> NAry(n) { z(n) }
        #|async fn main { println(1) }
      ),
    ),
    content=(
      #|async fn g cannot be compiled to MoonBit: its type has no native MoonBit translation (like a type computed from a parameter, or a type parameter with a bound that occurs in no parameter and not in the result type)
    ),
  )
  // a top-level async function as a value
  inspect(
    signatures(
      (
        #|async fn inc(x : Int) -> Int { x + 1 }
        #|async fn twice(f : async (Int) -> Int, x : Int) -> Int { f(f(x)) }
        #|async fn main {
        #|  let g : async (Int) -> Int = inc
        #|  println(twice(g, 1) + twice(inc, 2))
        #|}
      ),
    ),
    content=(
      #|async fn f_twice_t(f : async (Int) -> Int raise, x : Int) -> Int raise {
      #|async fn f_inc_t(x : Int) -> Int raise {
      #|async fn main {
      #|fn[T0 : Show] f_println_t(x : T0) -> Unit raise {
      #|fn f_println(v_inst_t : Value, x : Value) -> Value raise {
      #|fn f_show_to_string(inst : Value) -> Value raise {
    ),
  )
}

///|
/// The MoonBit impls of a program: the lines starting with `impl`.
fn impl_lines(src : String) -> String {
  @tt.check_program("t.mbtpp", src) catch {
    @tt.CheckError(msg) => return msg
  }
  let code = @codegen.generate([]) catch {
    @codegen.CodegenError(msg) => return msg
  }
  code
  .split("\n")
  .filter(l => l.has_prefix("impl"))
  .map(l => l.to_owned())
  .to_array()
  .join("\n")
}

///|
test "codegen: instances of Prelude traits for MoonBit++ datatypes are MoonBit impls" {
  // an async function has only native code: printing, comparing, ... its
  // datatypes needs the impls (Option and Result use MoonBit's own)
  inspect(
    impl_lines(
      (
        #|enum Color {
        #|  Red
        #|  Green
        #|  Rgb(Int, Int, Int)
        #|} derive(Show, Eq, Compare, Hash)
        #|
        #|struct Point {
        #|  x : Int
        #|  y : Int
        #|} derive(Show, Eq, Compare)
        #|
        #|fn[T : Eq] same(a : T, b : T) -> Bool { a == b }
        #|fn[T : Compare] smaller(a : T, b : T) -> T { if a.compare(b) <= 0 { a } else { b } }
        #|fn[T : Show] show_all(xs : List[T]) -> String {
        #|  match xs { Nil => ""; Cons(x, r) => x.to_string() + ";" + show_all(r) }
        #|}
        #|
        #|async fn main {
        #|  println(Rgb(1, 2, 3))
        #|  println(Cons(Red, Cons(Green, Nil)))
        #|  println(same(Rgb(1, 2, 3), Rgb(1, 2, 3)))
        #|  println(smaller(Green, Red))
        #|  println({ x: 1, y: 2 })
        #|  println(same({ x: 1, y: 2 }, { x: 1, y: 3 }))
        #|  println(smaller({ x: 2, y: 0 }, { x: 1, y: 9 }))
        #|  println(show_all(Cons(Red, Cons(Rgb(0, 0, 0), Nil))))
        #|  let n : Nat = 2
        #|  println(n + 3)
        #|  println(Some(Red))
        #|  println(same(Some(1), Some(1)))
        #|  let r : Result[Int, String] = Ok(1)
        #|  println(r)
        #|}
      ),
    ),
    content=(
      #|impl Show for E_Color with to_string(a0) {
      #|impl Eq for E_Color with equal(a0, a1) {
      #|impl Compare for E_Color with compare(a0, a1) {
      #|impl Show for E_Point with to_string(a0) {
      #|impl Eq for E_Point with equal(a0, a1) {
      #|impl Compare for E_Point with compare(a0, a1) {
      #|impl[T0 : Show] Show for E_List[T0] with to_string(a0) {
    ),
  )
}

///|
test "codegen: arrays are MoonBit arrays in native code" {
  // never converted to `Value`: native and uniform code do not share them
  inspect(
    signatures(
      (
        #|struct Counter {
        #|  mut n : Int
        #|}
        #|
        #|fn bump(c : Counter) -> Unit { c.n = c.n + 1 }
        #|
        #|fn fill(xs : Array[Int], v : Int) -> Unit {
        #|  for i = 0; i < xs.length(); i = i + 1 { xs[i] = v }
        #|}
        #|
        #|// a dependent result: uniform code, sharing the array with native helpers
        #|fn[n : Nat] make_vec(len : Int) -> Array[Int] {
        #|  let a = Array::make(len, 0)
        #|  fill(a, 5)
        #|  a.push(n.to_int())
        #|  a
        #|}
        #|
        #|fn total(xs : Array[Int]) -> Int {
        #|  let mut s = 0
        #|  for x in xs { s = s + x }
        #|  s
        #|}
        #|
        #|async fn main {
        #|  let c : Counter = { n: 0 }
        #|  bump(c)
        #|  bump(c)
        #|  println(c.n)
        #|  let a = [1, 2, 3]
        #|  fill(a, 7)
        #|  println(a)
        #|  let m : Map[String, Int] = {}
        #|  m["x"] = 1
        #|  m["y"] = 2
        #|  m["x"] = 10
        #|  println(m)
        #|  let grid = [[1, 2], [3]]
        #|  grid[1].push(4)
        #|  println(grid)
        #|  println(a[5])
        #|}
      ),
    ),
    content=(
      #|struct E_Counter(Array[Int])
      #|fn f_fill_t(xs : Array[Int], v : Int) -> Unit {
      #|fn f_fill(xs : Value, v : Value) -> Value raise {
      #|fn f_counter_n_t(self : E_Counter) -> Array[Int] {
      #|fn f_counter_n(self : Value) -> Value raise {
      #|fn f_bump_t(c : E_Counter) -> Unit {
      #|fn f_bump(c : Value) -> Value raise {
      #|async fn main {
      #|enum E_Map[T0, T1] {
      #|fn[T0, T1] f_map_map_values_t(self : E_Map[T0, T1]) -> Array[Array[T1]] {
      #|fn f_map_map_values(self : Value) -> Value raise {
      #|fn[T0, T1] f_map_map_keys_t(self : E_Map[T0, T1]) -> Array[Array[T0]] {
      #|fn f_map_map_keys(self : Value) -> Value raise {
      #|fn[T0 : Eq, T1] f_map_op_set_t(self : E_Map[T0, T1], key : T0, value : T1) -> Unit raise {
      #|fn f_map_op_set(v_inst_k : Value, self : Value, key : Value, value : Value) -> Value raise {
      #|fn[T0 : Eq, T1] f_map_set_t(self : E_Map[T0, T1], key : T0, value : T1) -> Unit raise {
      #|fn f_map_set(v_inst_k : Value, self : Value, key : Value, value : Value) -> Value raise {
      #|fn[T0 : Eq, T1] f_map_index_of_t(self : E_Map[T0, T1], key : T0) -> Int raise {
      #|fn f_map_index_of(v_inst_k : Value, self : Value, key : Value) -> Value raise {
      #|fn f_eq_op_equal(inst : Value) -> Value raise {
      #|fn[T0, T1] f_map_new_t(v : Unit) -> E_Map[T0, T1] {
      #|fn f_map_new(v : Value) -> Value raise {
      #|fn[T0 : Show] f_println_t(x : T0) -> Unit raise {
      #|fn f_println(v_inst_t : Value, x : Value) -> Value raise {
      #|fn f_show_to_string(inst : Value) -> Value raise {
    ),
  )
}

///|
/// The warnings of the code generator, and the `pub fn` lines.
fn warnings_and_exports(src : String) -> String {
  @tt.check_program("t.mbtpp", src) catch {
    @tt.CheckError(msg) => return msg
  }
  let code = @codegen.generate([]) catch {
    @codegen.CodegenError(msg) => return msg
  }
  let out = @codegen.warnings.map(w => "warning: " + w)
  for line in code.split("\n") {
    if line.has_prefix("pub fn") {
      out.push(line.to_owned())
    }
  }
  out.join("\n")
}

///|
test "codegen: an implicit value used at run time is a parameter, with a warning for #mbt" {
  inspect(
    warnings_and_exports(
      (
        #|// `n` is used at run time: an ordinary parameter of the MoonBit function
        #|#mbt
        #|fn[n : Int] repeat_n(x : Int) -> Array[Int] {
        #|  Array::make(n, x)
        #|}
        #|
        #|// `n` is not used at run time: erased, no warning
        #|#mbt
        #|fn[n : Nat] konst(x : Int) -> Int { x }
        #|
        #|// not #mbt: no MoonBit signature to warn about
        #|fn[n : Nat] count_to(x : Int) -> Int { n.to_int() + x }
        #|
        #|fn main {
        #|  println(repeat_n[3](7))
        #|  println(konst[(4 : Nat)](5))
        #|  println(count_to[(2 : Nat)](1))
        #|}
      ),
    ),
    content=(
      #|warning: #mbt fn repeat_n: the implicit parameter(s) n are used at run time, so the MoonBit function repeat_n takes them as ordinary parameters: repeat_n(n : Int, x : Int)
      #|pub fn konst(x : Int) -> Int {
      #|pub fn repeat_n(n : Int, x : Int) -> Array[Int] {
    ),
  )
}

///|
test "codegen: a datatype that takes the name of a #mbt trait is not #mbt" {
  inspect(
    signatures(
      (
        #|enum Sub {
        #|  Minus(Int, Int)
        #|}
        #|
        #|fn[n : Nat] apply(s : Sub) -> Int {
        #|  match s {
        #|    Minus(a, b) => a - b + n.to_int()
        #|  }
        #|}
        #|
        #|fn main {
        #|  println(apply[(1 : Nat)](Minus(5, 2)))
        #|}
      ),
    ),
    content=(
      #|enum E_Sub {
      #|fn f_main_init() -> Unit raise {
      #|fn f_apply_t(n : BigInt, s : E_Sub) -> Int {
      #|fn f_apply(a0 : Value, a1 : Value) -> Value raise {
      #|fn main {
      #|fn[T0 : Show] f_println_t(x : T0) -> Unit raise {
      #|fn f_println(v_inst_t : Value, x : Value) -> Value raise {
      #|fn f_show_to_string(inst : Value) -> Value raise {
    ),
  )
}

///|
test "codegen: Nat is a BigInt" {
  let src =
    #|fn pred2(n : Nat) -> Nat {
    #|  match n {
    #|    S(S(k)) => k
    #|    S(Z) as one => one
    #|    _ => 0
    #|  }
    #|}
    #|
    #|fn NAry(n : Nat) -> Type {
    #|  match n {
    #|    Z => Int
    #|    S(k) => (Int) -> NAry(k)
    #|  }
    #|}
    #|
    #|fn sum_n(n : Nat, acc : Int) -> NAry(n) {
    #|  match n as m return NAry(m) {
    #|    Z => acc
    #|    S(k) => x => sum_n(k, acc + x)
    #|  }
    #|}
    #|
    #|fn main {
    #|  println(pred2(5) * 10 + int_to_nat(2))
    #|  println(sum_n(2, 0)(1)(2))
    #|}
  // native code: tests on the BigInt, whose slots are `n - j`
  inspect(
    fn_code(src, "pred2"),
    content=(
      #|fn f_pred2_t(n : BigInt) -> BigInt {
      #|match n {
      #|n if n >= 2N => (n - 2N)
      #|n if n == 1N => n
      #|_ => 0N
      #|_ => rt_stop("no match")
      #|}
      #|fn f_pred2(a0 : Value) -> Value raise {
      #|  VNat(f_pred2_t(as_nat(a0)))
      #|}
    ),
  )
  // uniform code
  inspect(
    fn_code(src, "sum_n"),
    content=(
      #|fn f_sum_n(n : Value, acc : Value) -> Value raise {
      #|match n {
      #|n if as_nat(n) == 0N => (acc)
      #|n if as_nat(n) >= 1N => (VFun(x => f_sum_n(VNat(as_nat(n) - 1N), VInt(as_int(acc) + as_int(x)))))
      #|_ => rt_fail("no match")
      #|}
    ),
  )
}

///|
test "codegen: Nat-like datatypes are BigInts" {
  let fin =
    #|enum Fin : (Nat) -> Type {
    #|  FZ[n : Nat] : Fin(S(n))
    #|  FS[n : Nat](Fin(n)) : Fin(S(n))
    #|}
    #|
    #|enum Vector[T] : Nat -> Type {
    #|  Nil : Vector[T](0)
    #|  Cons[n : Nat](T, Vector[T](n)) : Vector[T](S(n))
    #|}
    #|
    #|fn[T, n : Nat] Vector::get(self : Vector[T](n), i : Fin(n)) -> T {
    #|  match (self, i) {
    #|    (Cons(x, _), FZ) => x
    #|    (Cons(_, xs), FS(j)) => xs.get(j)
    #|  }
    #|}
    #|
  // `Fin`'s index fields are erased: it is `Nat` after erasure
  inspect(
    signatures(
      fin +
      (
        #|fn main {
        #|  let v : Vector[Int](2) = Cons(7, Cons(8, Nil))
        #|  println(v.get(FS(FZ)))
        #|}
      ),
    ),
    content=(
      #|enum E_Vector[T0] {
      #|fn f_main_init() -> Unit raise {
      #|fn[T0] f_vector_get_t(self : E_Vector[T0], i : BigInt) -> T0 {
      #|fn f_vector_get(a2 : Value, a3 : Value) -> Value raise {
      #|fn main {
      #|fn[T0 : Show] f_println_t(x : T0) -> Unit raise {
      #|fn f_println(v_inst_t : Value, x : Value) -> Value raise {
      #|fn f_show_to_string(inst : Value) -> Value raise {
    ),
  )
  // an index field used at run time is kept: `Fin` stays an enum
  inspect(
    signatures(
      fin +
      (
        #|fn[n : Nat] bound(i : Fin(n)) -> Int {
        #|  match i {
        #|    FZ[m] => m.to_int()
        #|    FS[m](_) => m.to_int()
        #|  }
        #|}
        #|
        #|fn main {
        #|  let i : Fin(3) = FS(FZ)
        #|  println(bound(i))
        #|}
      ),
    ),
    content=(
      #|enum E_Fin {
      #|fn f_main_init() -> Unit raise {
      #|fn f_bound_t(i : E_Fin) -> Int {
      #|fn f_bound(a1 : Value) -> Value raise {
      #|fn main {
      #|fn[T0 : Show] f_println_t(x : T0) -> Unit raise {
      #|fn f_println(v_inst_t : Value, x : Value) -> Value raise {
      #|fn f_show_to_string(inst : Value) -> Value raise {
    ),
  )
}

///|
test "codegen: newtypes and value parameters" {
  inspect(
    signatures(
      (
        #|type Ex Int
        #|
        #|enum Expr {
        #|  Var(Int)
        #|  Lam(Expr)
        #|}
        #|
        #|fn depth(e : Expr) -> Int {
        #|  match e {
        #|    Var(_) => 0
        #|    Lam(b) => depth(b) + 1
        #|  }
        #|}
        #|
        #|// `n` only occurs in a proof: it is dropped like an index
        #|struct Scoped(n : Int) {
        #|  e : Expr
        #|  ok : depth(e) === n
        #|}
        #|
        #|fn twice(x : Ex) -> Ex {
        #|  match x {
        #|    Ex(n) => Ex(n * 2)
        #|  }
        #|}
        #|
        #|fn[n : Int] body(s : Scoped(n)) -> Expr {
        #|  s.e
        #|}
        #|
        #|fn main {
        #|  let s : Scoped(1) = { e: Lam(Var(0)), ok: Refl }
        #|  println(depth(body(s)))
        #|  match twice(Ex(21)) {
        #|    Ex(n) => println(n)
        #|  }
        #|}
      ),
    ),
    content=(
      #|enum E_Expr {
      #|struct E_Scoped(E_Expr)
      #|struct E_Ex(Int)
      #|fn f_main_init() -> Unit raise {
      #|fn f_twice_t(x : E_Ex) -> E_Ex {
      #|fn f_twice(a0 : Value) -> Value raise {
      #|fn f_depth_t(e : E_Expr) -> Int {
      #|fn f_depth(a0 : Value) -> Value raise {
      #|fn f_body_t(s : E_Scoped) -> E_Expr {
      #|fn f_body(a1 : Value) -> Value raise {
      #|fn f_scoped_e_t(self : E_Scoped) -> E_Expr {
      #|fn f_scoped_e(a1 : Value) -> Value raise {
      #|fn main {
      #|fn[T0 : Show] f_println_t(x : T0) -> Unit raise {
      #|fn f_println(v_inst_t : Value, x : Value) -> Value raise {
      #|fn f_show_to_string(inst : Value) -> Value raise {
    ),
  )
}

///|
test "codegen: global lets in native code" {
  let arena =
    #|struct Arena {
    #|  kinds : Array[Int]
    #|}
    #|
    #|let glob : Arena = { kinds: [1, 2, 3] }
    #|
    #|fn kind_glob(e : Int) -> Int {
    #|  glob.kinds[e]
    #|}
    #|
  // native: the functions reading it are native too
  inspect(
    signatures(arena + "fn main {\n  println(kind_glob(1))\n}\n"),
    content=(
      #|fn f_main_init() -> Unit raise {
      #|fn f_kind_glob_t(e : Int) -> Int {
      #|fn f_kind_glob(a0 : Value) -> Value raise {
      #|struct E_Arena(Array[Int])
      #|fn f_arena_kinds_t(self : E_Arena) -> Array[Int] {
      #|fn f_arena_kinds(self : Value) -> Value raise {
      #|fn f_glob_init() -> E_Arena {
      #|fn f_glob_n() -> E_Arena {
      #|fn main {
      #|fn[T0 : Show] f_println_t(x : T0) -> Unit raise {
      #|fn f_println(v_inst_t : Value, x : Value) -> Value raise {
      #|fn f_show_to_string(inst : Value) -> Value raise {
    ),
  )
  // used by uniform code: arrays cannot be in both representations
  inspect(
    signatures(
      arena +
      (
        #|fn NAry(n : Nat) -> Type {
        #|  match n {
        #|    Z => Int
        #|    S(k) => (Int) -> NAry(k)
        #|  }
        #|}
        #|
        #|fn sum_n(n : Nat, acc : Int) -> NAry(n) {
        #|  match n as m return NAry(m) {
        #|    Z => acc + glob.kinds[0]
        #|    S(k) => x => sum_n(k, acc + x)
        #|  }
        #|}
        #|
        #|fn main {
        #|  println(kind_glob(1) + sum_n(1, 0)(2))
        #|}
      ),
    ),
    content=(
      #|fn f_sum_n(n : Value, acc : Value) -> Value raise {
      #|struct E_Arena(Array[Int])
      #|fn f_arena_kinds_t(self : E_Arena) -> Array[Int] {
      #|fn f_arena_kinds(self : Value) -> Value raise {
      #|fn f_kind_glob(e : Value) -> Value raise {
      #|fn main {
      #|fn[T0 : Show] f_println_t(x : T0) -> Unit raise {
      #|fn f_println(v_inst_t : Value, x : Value) -> Value raise {
      #|fn f_show_to_string(inst : Value) -> Value raise {
    ),
  )
}

///|
test "codegen: aliases in fields, if in match and while, string indexing" {
  let src =
    #|typealias Int as Expr
    #|
    #|struct Decl {
    #|  ty : Expr
    #|  name : String
    #|}
    #|
    #|fn first(d : Decl) -> Char {
    #|  d.name[0]
    #|}
    #|
    #|fn count(d : Decl, n : Int) -> Int {
    #|  let mut i = 0
    #|  while if d.ty > 0 { i < n } else { false } {
    #|    i = i + 1
    #|  }
    #|  match if i > 2 { 1 } else { 0 } {
    #|    1 => i
    #|    _ => d.ty
    #|  }
    #|}
    #|
    #|fn main {
    #|  let d : Decl = { ty: 7, name: "abc" }
    #|  println(first(d))
    #|  println(count(d, 5))
    #|}
  inspect(
    signatures(src),
    content=(
      #|enum E_Decl {
      #|fn f_main_init() -> Unit raise {
      #|fn f_count_t(d : E_Decl, n : Int) -> Int {
      #|fn f_count(a0 : Value, a1 : Value) -> Value raise {
      #|fn f_decl_ty_t(self : E_Decl) -> Int {
      #|fn f_decl_ty(a0 : Value) -> Value raise {
      #|fn f_first_t(d : E_Decl) -> Char {
      #|fn f_first(a0 : Value) -> Value raise {
      #|fn f_decl_name_t(self : E_Decl) -> String {
      #|fn f_decl_name(a0 : Value) -> Value raise {
      #|fn main {
      #|fn[T0 : Show] f_println_t(x : T0) -> Unit raise {
      #|fn f_println(v_inst_t : Value, x : Value) -> Value raise {
      #|fn f_show_to_string(inst : Value) -> Value raise {
    ),
  )
  inspect(
    @mbtpp.run_source("t.mbtpp", src),
    content=(
      #|a
      #|5
      #|
    ),
  )
}

///|
/// `main` with `return` is native: the functions it calls with arrays run
/// natively (they could not be called from uniform code).
test "codegen: main with return is native" {
  let src =
    #|fn total(xs : Array[Int]) -> Int {
    #|  let mut s = 0
    #|  for x in xs {
    #|    s = s + x
    #|  }
    #|  s
    #|}
    #|
    #|fn main {
    #|  let xs = [1, 2, 3]
    #|  if xs.length() == 0 {
    #|    println("empty")
    #|    return
    #|  }
    #|  println(total(xs))
    #|}
  inspect(
    fn_code(src, "main_init").length() > 0,
    content=(
      #|true
    ),
  )
  inspect(
    @mbtpp.run_source("t.mbtpp", src),
    content=(
      #|6
      #|
    ),
  )
}

///|
/// A lambda whose body is a variable: `moon fmt` may print a long `x => y`
/// as `x => { y }`, a record (bugs/005 of moonlit).
test "codegen: a variable alone is not a lambda body" {
  @tt.check_program(
    "t.mbtpp",
    (
      #|fn drop(m : HashMap[(Int, Int), Int], x : Int, y : Int) -> Unit {
      #|  if x > -1 {
      #|    m.remove((x, y))
      #|  }
      #|}
      #|
      #|fn main {
      #|  let m : HashMap[(Int, Int), Int] = HashMap::new()
      #|  drop(m, 1, 2)
      #|}
    ),
  ) catch {
    _ => abort("check failed")
  }
  let code = @codegen.generate([]) catch { _ => abort("codegen failed") }
  inspect(code.contains("=> value_id(self"), content="true")
}

///|
test "the driver of the splices has the imported functions" {
  @tt.check_program(
    "t.mbtpp",
    (
      #|fn twice(x : Int) -> Int = "@mbt:demo.twice"
      #|fn[T] first(xs : Array[T]) -> T? = "@mbt:demo.first"
      #|fn odd(f : (Int) -> Int) -> Int = "@mbt:demo.odd"
      #|fn main { println(twice(1)) }
    ),
  ) catch {
    @tt.CheckError(msg) => fail(msg)
  }
  let (files, skipped) = @codegen.generate_driver([("demo", "demo")], [
    "twice", "first", "odd", "main",
  ]) catch {
    @codegen.CodegenError(msg) => fail(msg)
  }
  let names = files.map(f => f.0)
  inspect(
    names,
    content=(
      #|[t.mbt, mbtpp_prelude.mbt, mbtpp_imports.mbt, mbtpp_driver.mbt]
    ),
  )
  let all = files.map(f => f.1).join("\n")
  let table = all
    .split("\n")
    .filter(l => l.contains("ffi_table.set") || l.contains("ffi_why.set"))
    .map(l => strip_counters(l.to_owned()))
  inspect(
    table,
    content=(
      #|[  ffi_table.set("twice", ffi),   ffi_table.set("first", ffi),   ffi_table.set("odd", ffi)]
    ),
  )
  inspect(
    skipped,
    content=(
      #|[(main, main is not an imported function)]
    ),
  )
  inspect(
    all.contains("pub fn call(name : String, args : String) -> String"),
    content="true",
  )
  inspect(all.contains("con_makers.push"), content="true")
}

///|
test "codegen: a primitive with a `$` in an argument is a dynamic call that the runtime handles" {
  inspect(
    fn_code(
      (
        #|fn T(b : Bool) -> Type { if b { Bool } else { Int } }
        #|fn f(b : Bool, x : BigInt) -> T(b) {
        #|  match b {
        #|    true => x < BigInt::from_int("$$".length())
        #|    false => 0
        #|  }
        #|}
        #|fn main { println(f(true, BigInt::from_int(1))) }
      ),
      "f",
    ),
    content=(
      #|fn f_f(b : Value, x : Value) -> Value raise {
      #|{
      #|let cond = b
      #|if truthy(cond) {
      #|prim("%bigint_lt", [x, prim("%bigint_of_int", [prim("%str_length", [VStr("$$")])])])
      #|} else {
      #|VInt(0)
      #|}
    ),
  )
}
