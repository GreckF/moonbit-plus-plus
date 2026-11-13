///|
/// Pure primitives on literals, shared by the type checker and the
/// interpreter. Returns `None` for unknown or impure primitives and for
/// invalid arguments (e.g. division by zero).
pub fn prim_pure(name : String, args : Array[Lit]) -> Lit? {
  match (name, args) {
    ("%int_add", [LInt(a), LInt(b)]) => Some(LInt(a + b))
    ("%int_sub", [LInt(a), LInt(b)]) => Some(LInt(a - b))
    ("%int_mul", [LInt(a), LInt(b)]) => Some(LInt(a * b))
    ("%int_div", [LInt(a), LInt(b)]) =>
      if b == 0 {
        None
      } else {
        Some(LInt(a / b))
      }
    ("%int_mod", [LInt(a), LInt(b)]) =>
      if b == 0 {
        None
      } else {
        Some(LInt(a % b))
      }
    ("%int_neg", [LInt(a)]) => Some(LInt(-a))
    ("%int_land", [LInt(a), LInt(b)]) => Some(LInt(a & b))
    ("%int_lor", [LInt(a), LInt(b)]) => Some(LInt(a | b))
    ("%int_lxor", [LInt(a), LInt(b)]) => Some(LInt(a ^ b))
    ("%int_shl", [LInt(a), LInt(b)]) => Some(LInt(a << b))
    ("%int_shr", [LInt(a), LInt(b)]) => Some(LInt(a >> b))
    ("%int_eq", [LInt(a), LInt(b)]) => Some(LBool(a == b))
    ("%int_lt", [LInt(a), LInt(b)]) => Some(LBool(a < b))
    ("%int_le", [LInt(a), LInt(b)]) => Some(LBool(a <= b))
    ("%int_gt", [LInt(a), LInt(b)]) => Some(LBool(a > b))
    ("%int_ge", [LInt(a), LInt(b)]) => Some(LBool(a >= b))
    ("%int_compare", [LInt(a), LInt(b)]) => Some(LInt(a.compare(b)))
    ("%int_to_string", [LInt(a)]) => Some(LStr(a.to_string()))
    ("%int_to_char", [LInt(a)]) =>
      match a.to_char() {
        Some(c) => Some(LChar(c))
        None => None
      }
    ("%str_add", [LStr(a), LStr(b)]) => Some(LStr(a + b))
    ("%str_eq", [LStr(a), LStr(b)]) => Some(LBool(a == b))
    ("%str_compare", [LStr(a), LStr(b)]) => Some(LInt(a.compare(b)))
    ("%str_length", [LStr(a)]) => Some(LInt(a.length()))
    ("%str_get", [LStr(a), LInt(i)]) =>
      match a.get_char(i) {
        Some(c) => Some(LChar(c))
        None => None
      }
    ("%str_substring", [LStr(a), LInt(i), LInt(j)]) =>
      if i >= 0 && i <= j && j <= a.length() {
        Some(LStr(a.unsafe_substring(start=i, end=j)))
      } else {
        None
      }
    ("%bool_eq", [LBool(a), LBool(b)]) => Some(LBool(a == b))
    ("%bool_not", [LBool(a)]) => Some(LBool(!a))
    ("%bool_to_string", [LBool(a)]) => Some(LStr(a.to_string()))
    ("%char_eq", [LChar(a), LChar(b)]) => Some(LBool(a == b))
    ("%char_compare", [LChar(a), LChar(b)]) => Some(LInt(a.compare(b)))
    ("%char_to_int", [LChar(a)]) => Some(LInt(a.to_int()))
    ("%char_to_string", [LChar(a)]) => Some(LStr(a.to_string()))
    ("%unit_to_string", [LUnit]) => Some(LStr("()"))
    ("%double_add", [LDouble(a), LDouble(b)]) => Some(LDouble(a + b))
    ("%double_sub", [LDouble(a), LDouble(b)]) => Some(LDouble(a - b))
    ("%double_mul", [LDouble(a), LDouble(b)]) => Some(LDouble(a * b))
    ("%double_div", [LDouble(a), LDouble(b)]) => Some(LDouble(a / b))
    ("%double_neg", [LDouble(a)]) => Some(LDouble(-a))
    ("%double_eq", [LDouble(a), LDouble(b)]) => Some(LBool(a == b))
    ("%double_lt", [LDouble(a), LDouble(b)]) => Some(LBool(a < b))
    ("%double_le", [LDouble(a), LDouble(b)]) => Some(LBool(a <= b))
    ("%double_gt", [LDouble(a), LDouble(b)]) => Some(LBool(a > b))
    ("%double_ge", [LDouble(a), LDouble(b)]) => Some(LBool(a >= b))
    ("%double_compare", [LDouble(a), LDouble(b)]) => Some(LInt(a.compare(b)))
    ("%double_to_string", [LDouble(a)]) => Some(LStr(a.to_string()))
    ("%double_to_int", [LDouble(a)]) => Some(LInt(a.to_int()))
    ("%int_to_double", [LInt(a)]) => Some(LDouble(a.to_double()))
    ("%int64_add", [LInt64(a), LInt64(b)]) => Some(LInt64(a + b))
    ("%int64_sub", [LInt64(a), LInt64(b)]) => Some(LInt64(a - b))
    ("%int64_mul", [LInt64(a), LInt64(b)]) => Some(LInt64(a * b))
    ("%int64_div", [LInt64(a), LInt64(b)]) =>
      if b == 0L {
        None
      } else {
        Some(LInt64(a / b))
      }
    ("%int64_mod", [LInt64(a), LInt64(b)]) =>
      if b == 0L {
        None
      } else {
        Some(LInt64(a % b))
      }
    ("%int64_neg", [LInt64(a)]) => Some(LInt64(-a))
    ("%int64_land", [LInt64(a), LInt64(b)]) => Some(LInt64(a & b))
    ("%int64_lor", [LInt64(a), LInt64(b)]) => Some(LInt64(a | b))
    ("%int64_lxor", [LInt64(a), LInt64(b)]) => Some(LInt64(a ^ b))
    ("%int64_shl", [LInt64(a), LInt(b)]) => Some(LInt64(a << b))
    ("%int64_shr", [LInt64(a), LInt(b)]) => Some(LInt64(a >> b))
    ("%int64_eq", [LInt64(a), LInt64(b)]) => Some(LBool(a == b))
    ("%int64_lt", [LInt64(a), LInt64(b)]) => Some(LBool(a < b))
    ("%int64_le", [LInt64(a), LInt64(b)]) => Some(LBool(a <= b))
    ("%int64_gt", [LInt64(a), LInt64(b)]) => Some(LBool(a > b))
    ("%int64_ge", [LInt64(a), LInt64(b)]) => Some(LBool(a >= b))
    ("%int64_compare", [LInt64(a), LInt64(b)]) => Some(LInt(a.compare(b)))
    ("%int64_to_string", [LInt64(a)]) => Some(LStr(a.to_string()))
    ("%int64_hash", [LInt64(a)]) => Some(LInt(a.hash()))
    ("%uint_add", [LUInt(a), LUInt(b)]) => Some(LUInt(a + b))
    ("%uint_sub", [LUInt(a), LUInt(b)]) => Some(LUInt(a - b))
    ("%uint_mul", [LUInt(a), LUInt(b)]) => Some(LUInt(a * b))
    ("%uint_div", [LUInt(a), LUInt(b)]) =>
      if b == 0U {
        None
      } else {
        Some(LUInt(a / b))
      }
    ("%uint_mod", [LUInt(a), LUInt(b)]) =>
      if b == 0U {
        None
      } else {
        Some(LUInt(a % b))
      }
    ("%uint_land", [LUInt(a), LUInt(b)]) => Some(LUInt(a & b))
    ("%uint_lor", [LUInt(a), LUInt(b)]) => Some(LUInt(a | b))
    ("%uint_lxor", [LUInt(a), LUInt(b)]) => Some(LUInt(a ^ b))
    ("%uint_shl", [LUInt(a), LInt(b)]) => Some(LUInt(a << b))
    ("%uint_shr", [LUInt(a), LInt(b)]) => Some(LUInt(a >> b))
    ("%uint_eq", [LUInt(a), LUInt(b)]) => Some(LBool(a == b))
    ("%uint_lt", [LUInt(a), LUInt(b)]) => Some(LBool(a < b))
    ("%uint_le", [LUInt(a), LUInt(b)]) => Some(LBool(a <= b))
    ("%uint_gt", [LUInt(a), LUInt(b)]) => Some(LBool(a > b))
    ("%uint_ge", [LUInt(a), LUInt(b)]) => Some(LBool(a >= b))
    ("%uint_compare", [LUInt(a), LUInt(b)]) => Some(LInt(a.compare(b)))
    ("%uint_to_string", [LUInt(a)]) => Some(LStr(a.to_string()))
    ("%uint_hash", [LUInt(a)]) => Some(LInt(a.hash()))
    ("%uint64_add", [LUInt64(a), LUInt64(b)]) => Some(LUInt64(a + b))
    ("%uint64_sub", [LUInt64(a), LUInt64(b)]) => Some(LUInt64(a - b))
    ("%uint64_mul", [LUInt64(a), LUInt64(b)]) => Some(LUInt64(a * b))
    ("%uint64_div", [LUInt64(a), LUInt64(b)]) =>
      if b == 0UL {
        None
      } else {
        Some(LUInt64(a / b))
      }
    ("%uint64_mod", [LUInt64(a), LUInt64(b)]) =>
      if b == 0UL {
        None
      } else {
        Some(LUInt64(a % b))
      }
    ("%uint64_land", [LUInt64(a), LUInt64(b)]) => Some(LUInt64(a & b))
    ("%uint64_lor", [LUInt64(a), LUInt64(b)]) => Some(LUInt64(a | b))
    ("%uint64_lxor", [LUInt64(a), LUInt64(b)]) => Some(LUInt64(a ^ b))
    ("%uint64_shl", [LUInt64(a), LInt(b)]) => Some(LUInt64(a << b))
    ("%uint64_shr", [LUInt64(a), LInt(b)]) => Some(LUInt64(a >> b))
    ("%uint64_eq", [LUInt64(a), LUInt64(b)]) => Some(LBool(a == b))
    ("%uint64_lt", [LUInt64(a), LUInt64(b)]) => Some(LBool(a < b))
    ("%uint64_le", [LUInt64(a), LUInt64(b)]) => Some(LBool(a <= b))
    ("%uint64_gt", [LUInt64(a), LUInt64(b)]) => Some(LBool(a > b))
    ("%uint64_ge", [LUInt64(a), LUInt64(b)]) => Some(LBool(a >= b))
    ("%uint64_compare", [LUInt64(a), LUInt64(b)]) => Some(LInt(a.compare(b)))
    ("%uint64_to_string", [LUInt64(a)]) => Some(LStr(a.to_string()))
    ("%uint64_hash", [LUInt64(a)]) => Some(LInt(a.hash()))
    ("%byte_add", [LByte(a), LByte(b)]) => Some(LByte(a + b))
    ("%byte_sub", [LByte(a), LByte(b)]) => Some(LByte(a - b))
    ("%byte_mul", [LByte(a), LByte(b)]) => Some(LByte(a * b))
    ("%byte_div", [LByte(a), LByte(b)]) =>
      if b == b'\x00' {
        None
      } else {
        Some(LByte(a / b))
      }
    ("%byte_mod", [LByte(a), LByte(b)]) =>
      if b == b'\x00' {
        None
      } else {
        Some(LByte(a % b))
      }
    ("%byte_land", [LByte(a), LByte(b)]) => Some(LByte(a & b))
    ("%byte_lor", [LByte(a), LByte(b)]) => Some(LByte(a | b))
    ("%byte_lxor", [LByte(a), LByte(b)]) => Some(LByte(a ^ b))
    ("%byte_shl", [LByte(a), LInt(b)]) => Some(LByte(a << b))
    ("%byte_shr", [LByte(a), LInt(b)]) => Some(LByte(a >> b))
    ("%byte_eq", [LByte(a), LByte(b)]) => Some(LBool(a == b))
    ("%byte_lt", [LByte(a), LByte(b)]) => Some(LBool(a < b))
    ("%byte_le", [LByte(a), LByte(b)]) => Some(LBool(a <= b))
    ("%byte_gt", [LByte(a), LByte(b)]) => Some(LBool(a > b))
    ("%byte_ge", [LByte(a), LByte(b)]) => Some(LBool(a >= b))
    ("%byte_compare", [LByte(a), LByte(b)]) => Some(LInt(a.compare(b)))
    ("%byte_to_string", [LByte(a)]) => Some(LStr(a.to_string()))
    ("%byte_hash", [LByte(a)]) => Some(LInt(a.hash()))
    ("%float_add", [LFloat(a), LFloat(b)]) => Some(LFloat(a + b))
    ("%float_sub", [LFloat(a), LFloat(b)]) => Some(LFloat(a - b))
    ("%float_mul", [LFloat(a), LFloat(b)]) => Some(LFloat(a * b))
    ("%float_div", [LFloat(a), LFloat(b)]) => Some(LFloat(a / b))
    ("%float_neg", [LFloat(a)]) => Some(LFloat(-a))
    ("%float_eq", [LFloat(a), LFloat(b)]) => Some(LBool(a == b))
    ("%float_lt", [LFloat(a), LFloat(b)]) => Some(LBool(a < b))
    ("%float_le", [LFloat(a), LFloat(b)]) => Some(LBool(a <= b))
    ("%float_gt", [LFloat(a), LFloat(b)]) => Some(LBool(a > b))
    ("%float_ge", [LFloat(a), LFloat(b)]) => Some(LBool(a >= b))
    ("%float_compare", [LFloat(a), LFloat(b)]) => Some(LInt(a.compare(b)))
    ("%float_to_string", [LFloat(a)]) => Some(LStr(a.to_string()))
    ("%float_hash", [LFloat(a)]) => Some(LInt(a.hash()))
    ("%int64_to_int", [LInt64(a)]) => Some(LInt(a.to_int()))
    ("%int64_to_double", [LInt64(a)]) => Some(LDouble(a.to_double()))
    ("%int_to_int64", [LInt(a)]) => Some(LInt64(a.to_int64()))
    ("%uint_to_int", [LUInt(a)]) => Some(LInt(a.reinterpret_as_int()))
    ("%uint_to_double", [LUInt(a)]) => Some(LDouble(a.to_double()))
    ("%int_to_uint", [LInt(a)]) => Some(LUInt(a.reinterpret_as_uint()))
    ("%uint64_to_int", [LUInt64(a)]) => Some(LInt(a.to_int()))
    ("%uint64_to_double", [LUInt64(a)]) => Some(LDouble(a.to_double()))
    ("%int_to_uint64", [LInt(a)]) => Some(LUInt64(a.to_uint64()))
    ("%byte_to_int", [LByte(a)]) => Some(LInt(a.to_int()))
    ("%byte_to_double", [LByte(a)]) => Some(LDouble(a.to_double()))
    ("%int_to_byte", [LInt(a)]) => Some(LByte(a.to_byte()))
    ("%float_to_int", [LFloat(a)]) => Some(LInt(a.to_int()))
    ("%float_to_double", [LFloat(a)]) => Some(LDouble(a.to_double()))
    ("%int_to_float", [LInt(a)]) => Some(LFloat(Float::from_int(a)))
    ("%double_to_float", [LDouble(a)]) => Some(LFloat(Float::from_double(a)))
    ("%int64_to_uint64", [LInt64(a)]) =>
      Some(LUInt64(a.reinterpret_as_uint64()))
    ("%uint64_to_int64", [LUInt64(a)]) => Some(LInt64(a.reinterpret_as_int64()))
    ("%uint_to_uint64", [LUInt(a)]) => Some(LUInt64(a.to_uint64()))
    ("%uint64_to_uint", [LUInt64(a)]) => Some(LUInt(a.to_uint()))
    ("%uint_to_int64", [LUInt(a)]) => Some(LInt64(a.to_int64()))
    ("%byte_to_int64", [LByte(a)]) => Some(LInt64(a.to_int64()))
    ("%byte_to_uint", [LByte(a)]) => Some(LUInt(a.to_uint()))
    ("%byte_to_uint64", [LByte(a)]) => Some(LUInt64(a.to_uint64()))
    ("%int64_to_byte", [LInt64(a)]) => Some(LByte(a.to_byte()))
    _ => None
  }
}
