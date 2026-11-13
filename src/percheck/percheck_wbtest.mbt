///|
struct Box {
  n : Array[Int32]
}

///|
test "reset_all puts the registered values back" {
  let m : Map[String, Int32] = map()
  let a : Array[Int32] = array()
  let c : Ref[Int32] = cell(5)
  let s = state(Box::{ n: [1], }, s => s.n.clear())
  let before = count()
  m.set("x", 1)
  a.push(2)
  c.val = 9
  s.n.push(3)
  reset_all()
  assert_eq(m.length(), 0)
  assert_eq(a.length(), 0)
  assert_eq(c.val, 5)
  assert_eq(s.n.length(), 0)
  assert_true(before >= 4)
}
