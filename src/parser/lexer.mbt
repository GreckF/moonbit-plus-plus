///|
pub(all) enum Tok {
  TIdent(String)
  TInt(Int32)
  TDouble(Double)
  /// A literal of another numeric type (`1L`, `1U`, `1UL`, `1.5F`, `b'a'`).
  TLit(Lit)
  TStr(Array[StrPart])
  TChar(Char)
  /// Keywords and symbols.
  TSym(String)
  TEOF
} derive(Debug, Eq)

///|
pub extend Tok with @moonbitlang/core/debug.Debug::{to_repr}

///|
pub extend Tok with Eq::{not_equal, equal}

///|
pub(all) enum StrPart {
  SPStr(String)
  /// Source of an interpolated expression and its position.
  SPExpr(String, Int32, Int32)
} derive(Debug, Eq)

///|
pub extend StrPart with @moonbitlang/core/debug.Debug::{to_repr}

///|
pub extend StrPart with Eq::{not_equal, equal}

///|
pub(all) struct Token {
  tok : Tok
  pos : Pos
  /// Whether a newline separates this token from the previous one.
  nl : Bool
} derive(Debug)

///|
pub extend Token with @moonbitlang/core/debug.Debug::{to_repr}

///|
pub suberror ParseError {
  ParseError(Pos, String)
}

///|
let keywords : Array[String] = [
  "fn", "let", "mut", "if", "else", "match", "enum", "struct", "trait", "impl", "for",
  "in", "with", "while", "return", "break", "continue", "raise", "try", "catch",
  "true", "false", "Type", "Prop", "forall", "lemma", "proof", "monad", "as", "suberror",
  "derive", "pub", "priv", "noraise", "loop", "is", "guard", "async", "defer",
]

///|
/// Symbols, longest first.
let symbols : Array[String] = [
  "===", "..<", "..=", "::", "->", "=>", "==", "!=", "<=", ">=", "&&", "||", "|>",
  "<<", ">>", "<-", "+=", "-=", "*=", "/=", "..", "#", "(", ")", "[", "]", "{", "}",
  ",", ";", ":", ".", "=", "<", ">", "+", "-", "*", "/", "%", "!", "|", "_", "~",
  "?", "@", "&", "^", "$",
]

///|
fn is_ident_start(c : Char) -> Bool {
  (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z') || c == '_'
}

///|
fn is_ident_char(c : Char) -> Bool {
  is_ident_start(c) || (c >= '0' && c <= '9')
}

///|
pub fn tokenize(
  src : String,
  line0~ : Int32 = 1,
  col0~ : Int32 = 1,
) -> Array[Token] raise ParseError {
  let cs : Array[Char] = src.iter().collect()
  let n = cs.length()
  let toks : Array[Token] = []
  let mut i = 0
  let mut line = line0
  let mut col = col0
  let mut nl = true
  fn peek(k : Int32) -> Char {
    if i + k < n {
      cs[i + k]
    } else {
      '\u{0}'
    }
  }

  fn adv() -> Unit {
    if cs[i] == '\n' {
      line = line + 1
      col = 1
    } else {
      col = col + 1
    }
    i = i + 1
  }

  while i < n {
    let c = cs[i]
    if c == '\n' {
      nl = true
      adv()
      continue
    }
    if c == ' ' || c == '\t' || c == '\r' {
      adv()
      continue
    }
    if c == '/' && peek(1) == '/' {
      while i < n && cs[i] != '\n' {
        adv()
      }
      continue
    }
    let pos = { line, col, }
    // `0x1F`, `0o17`, `0b1010`
    if c == '0' &&
      (
        peek(1) == 'x' ||
        peek(1) == 'X' ||
        peek(1) == 'o' ||
        peek(1) == 'O' ||
        peek(1) == 'b' ||
        peek(1) == 'B'
      ) {
      let base = match peek(1) {
        'x' | 'X' => 16
        'o' | 'O' => 8
        _ => 2
      }
      adv()
      adv()
      let mut v : UInt64 = 0
      let mut digits = 0
      while i < n {
        let d = cs[i]
        let dv = if d >= '0' && d <= '9' {
          d.to_int() - '0'.to_int()
        } else if d >= 'a' && d <= 'f' {
          d.to_int() - 'a'.to_int() + 10
        } else if d >= 'A' && d <= 'F' {
          d.to_int() - 'A'.to_int() + 10
        } else if d == '_' {
          adv()
          continue
        } else {
          break
        }
        if dv >= base {
          break
        }
        if v > (18446744073709551615UL - dv.to_uint64()) / base.to_uint64() {
          raise ParseError(pos, "the integer literal is out of range")
        }
        v = v * base.to_uint64() + dv.to_uint64()
        digits = digits + 1
        adv()
      }
      if digits == 0 {
        raise ParseError(pos, "expected digits after the base prefix")
      }
      // `0xFFU`, `0xFFUL`, `0xFFL`
      let tok = if peek(0) == 'U' && peek(1) == 'L' && !is_ident_char(peek(2)) {
        adv()
        adv()
        TLit(LUInt64(v))
      } else if peek(0) == 'U' && !is_ident_char(peek(1)) {
        adv()
        if v > 4294967295UL {
          raise ParseError(pos, "the integer literal is out of range for UInt")
        }
        TLit(LUInt(v.to_uint()))
      } else if peek(0) == 'L' && !is_ident_char(peek(1)) {
        adv()
        TLit(LInt64(v.reinterpret_as_int64()))
      } else {
        // a bit pattern of 32 bits
        if v > 4294967295UL {
          raise ParseError(pos, "the integer literal is out of range for Int")
        }
        TInt(v.to_int())
      }
      toks.push({ tok, pos, nl, })
      nl = false
      continue
    }
    // `#|raw` and `$|interpolated` lines: consecutive lines form one string
    if (c == '#' || c == '$') && peek(1) == '|' {
      let parts : Array[StrPart] = []
      let buf = StringBuilder()
      let mut first = true
      while i < n && (cs[i] == '#' || cs[i] == '$') && peek(1) == '|' {
        let interp = cs[i] == '$'
        adv()
        adv()
        if !first {
          buf.write_char('\n')
        }
        first = false
        while i < n && cs[i] != '\n' && cs[i] != '\r' {
          let d = cs[i]
          if interp && d == '\\' && peek(1) == '{' {
            adv()
            adv()
            if buf.to_string() != "" {
              parts.push(SPStr(buf.to_string()))
            }
            buf.reset()
            let eline = line
            let ecol = col
            let ebuf = StringBuilder()
            let mut depth = 0
            while i < n && cs[i] != '\n' && !(cs[i] == '}' && depth == 0) {
              // a string or a character in the expression
              if cs[i] == '"' || cs[i] == '\'' {
                let q = cs[i]
                ebuf.write_char(q)
                adv()
                while i < n && cs[i] != q && cs[i] != '\n' {
                  if cs[i] == '\\' && i + 1 < n {
                    ebuf.write_char(cs[i])
                    adv()
                  }
                  ebuf.write_char(cs[i])
                  adv()
                }
                if i < n && cs[i] == q {
                  ebuf.write_char(q)
                  adv()
                }
                continue
              }
              if cs[i] == '{' {
                depth = depth + 1
              } else if cs[i] == '}' {
                depth = depth - 1
              }
              ebuf.write_char(cs[i])
              adv()
            }
            if i >= n || cs[i] != '}' {
              raise ParseError(pos, "unterminated interpolation")
            }
            adv()
            parts.push(SPExpr(ebuf.to_string(), eline, ecol))
            continue
          }
          if interp && d == '\\' {
            adv()
            if i >= n {
              raise ParseError(pos, "unterminated string literal")
            }
            let e = cs[i]
            adv()
            buf.write_char(escape_char(pos, e))
            continue
          }
          buf.write_char(d)
          adv()
        }
        // the next line, if it continues the string
        let mut j = i
        while j < n && (cs[j] == '\r' || cs[j] == '\n') {
          j = j + 1
        }
        while j < n && (cs[j] == ' ' || cs[j] == '\t') {
          j = j + 1
        }
        if j + 1 < n && (cs[j] == '#' || cs[j] == '$') && cs[j + 1] == '|' {
          while i < j {
            adv()
          }
        } else {
          break
        }
      }
      if buf.to_string() != "" || parts.length() == 0 {
        parts.push(SPStr(buf.to_string()))
      }
      toks.push({ tok: TStr(parts), pos, nl, })
      nl = false
      continue
    }
    // `b'a'`: a Byte
    if c == 'b' && peek(1) == '\'' {
      adv()
      adv()
      let ch = if i < n && cs[i] == '\\' {
        adv()
        if i >= n {
          raise ParseError(pos, "unterminated byte literal")
        }
        let e = cs[i]
        adv()
        if e == 'x' {
          let mut b = 0
          for _ in 0..<2 {
            let d = if i < n { cs[i] } else { ' ' }
            b = b * 16 +
              (if d >= '0' && d <= '9' {
                d.to_int() - '0'.to_int()
              } else if d >= 'a' && d <= 'f' {
                d.to_int() - 'a'.to_int() + 10
              } else if d >= 'A' && d <= 'F' {
                d.to_int() - 'A'.to_int() + 10
              } else {
                raise ParseError(
                  pos, "expected two hexadecimal digits after \\x",
                )
              })
            adv()
          }
          b.unsafe_to_char()
        } else {
          escape_char(pos, e)
        }
      } else if i < n {
        let ch = cs[i]
        adv()
        if ch.to_int() > 127 {
          raise ParseError(
            pos, "a byte literal is an ASCII character or an escape",
          )
        }
        ch
      } else {
        raise ParseError(pos, "unterminated byte literal")
      }
      if i >= n || cs[i] != '\'' {
        raise ParseError(pos, "unterminated byte literal")
      }
      adv()
      toks.push({ tok: TLit(LByte(ch.to_int().to_byte())), pos, nl, })
      nl = false
      continue
    }
    if c >= '0' && c <= '9' {
      let text = StringBuilder()
      let mut v : UInt64 = 0
      let mut too_big = false
      let digits = () => {
        while i < n && ((cs[i] >= '0' && cs[i] <= '9') || cs[i] == '_') {
          if cs[i] != '_' {
            text.write_char(cs[i])
          }
          adv()
        }
      }
      while i < n && ((cs[i] >= '0' && cs[i] <= '9') || cs[i] == '_') {
        if cs[i] != '_' {
          let d = (cs[i].to_int() - '0'.to_int()).to_uint64()
          if v > (18446744073709551615UL - d) / 10UL {
            too_big = true
          }
          v = v * 10 + d
          text.write_char(cs[i])
        }
        adv()
      }
      // `1.5` and `1e3` are Doubles, but not `0..n` or the field access
      // `t.0.1`
      let after_dot = toks.length() > 0 &&
        toks[toks.length() - 1].tok == TSym(".")
      let frac = !after_dot &&
        i + 1 < n &&
        cs[i] == '.' &&
        cs[i + 1] >= '0' &&
        cs[i + 1] <= '9'
      if frac {
        text.write_char('.')
        adv()
        digits()
      }
      let exp = !after_dot &&
        (peek(0) == 'e' || peek(0) == 'E') &&
        (
          (peek(1) >= '0' && peek(1) <= '9') ||
          (
            (peek(1) == '+' || peek(1) == '-') &&
            peek(2) >= '0' &&
            peek(2) <= '9'
          )
        )
      if exp {
        text.write_char('e')
        adv()
        if peek(0) == '+' || peek(0) == '-' {
          text.write_char(peek(0))
          adv()
        }
        digits()
      }
      if frac || exp {
        let d = @string.parse_double(text.to_string()) catch {
          _ => raise ParseError(pos, "invalid floating-point literal")
        }
        // `1.5F`: a Float
        if peek(0) == 'F' && !is_ident_char(peek(1)) {
          adv()
          toks.push({ tok: TLit(LFloat(Float::from_double(d))), pos, nl, })
        } else {
          toks.push({ tok: TDouble(d), pos, nl, })
        }
        nl = false
        continue
      }
      // `-2147483648`: the literal after a minus may be one more
      let neg = toks.length() > 0 && toks[toks.length() - 1].tok == TSym("-")
      let range = (max : UInt64, ty : String) => {
        if too_big || v > max + (if neg { 1UL } else { 0UL }) {
          raise ParseError(
            pos,
            "the integer literal " +
            text.to_string() +
            " is out of range for " +
            ty,
          )
        }
      }
      // `1L` Int64, `1U` UInt, `1UL` UInt64, `1F` Float
      let tok = if peek(0) == 'U' && peek(1) == 'L' && !is_ident_char(peek(2)) {
        adv()
        adv()
        range(18446744073709551615UL, "UInt64")
        TLit(LUInt64(v))
      } else if peek(0) == 'U' && !is_ident_char(peek(1)) {
        adv()
        range(4294967295UL, "UInt")
        TLit(LUInt(v.to_uint()))
      } else if peek(0) == 'L' && !is_ident_char(peek(1)) {
        adv()
        range(9223372036854775807UL, "Int64")
        TLit(LInt64(v.reinterpret_as_int64()))
      } else if peek(0) == 'F' && !is_ident_char(peek(1)) {
        adv()
        TLit(LFloat(Float::from_double(v.to_double())))
      } else {
        range(2147483647UL, "Int")
        TInt(v.to_int())
      }
      toks.push({ tok, pos, nl, })
      nl = false
      continue
    }
    if is_ident_start(c) && !(c == '_' && !is_ident_char(peek(1))) {
      let buf = StringBuilder()
      while i < n && is_ident_char(cs[i]) {
        buf.write_char(cs[i])
        adv()
      }
      let s = buf.to_string()
      let tok = if keywords.contains(s) { TSym(s) } else { TIdent(s) }
      toks.push({ tok, pos, nl, })
      nl = false
      continue
    }
    if c == '\'' {
      adv()
      let ch = if i < n && cs[i] == '\\' {
        adv()
        if i >= n {
          raise ParseError(pos, "unterminated character literal")
        }
        let e = cs[i]
        adv()
        escape_char(pos, e)
      } else if i < n {
        let ch = cs[i]
        adv()
        ch
      } else {
        raise ParseError(pos, "unterminated character literal")
      }
      if i >= n || cs[i] != '\'' {
        raise ParseError(pos, "unterminated character literal")
      }
      adv()
      toks.push({ tok: TChar(ch), pos, nl, })
      nl = false
      continue
    }
    if c == '"' {
      adv()
      let parts : Array[StrPart] = []
      let buf = StringBuilder()
      while true {
        if i >= n || cs[i] == '\n' {
          raise ParseError(pos, "unterminated string literal")
        }
        let d = cs[i]
        if d == '"' {
          adv()
          break
        }
        if d == '\\' && peek(1) == '{' {
          adv()
          adv()
          if buf.to_string() != "" {
            parts.push(SPStr(buf.to_string()))
          }
          buf.reset()
          let eline = line
          let ecol = col
          let ebuf = StringBuilder()
          let mut depth = 0
          while i < n && !(cs[i] == '}' && depth == 0) {
            // a string or a character in the expression
            if cs[i] == '"' || cs[i] == '\'' {
              let q = cs[i]
              ebuf.write_char(q)
              adv()
              while i < n && cs[i] != q && cs[i] != '\n' {
                if cs[i] == '\\' && i + 1 < n {
                  ebuf.write_char(cs[i])
                  adv()
                }
                ebuf.write_char(cs[i])
                adv()
              }
              if i < n && cs[i] == q {
                ebuf.write_char(q)
                adv()
              }
              continue
            }
            if cs[i] == '{' {
              depth = depth + 1
            } else if cs[i] == '}' {
              depth = depth - 1
            }
            ebuf.write_char(cs[i])
            adv()
          }
          if i >= n {
            raise ParseError(pos, "unterminated interpolation")
          }
          adv()
          parts.push(SPExpr(ebuf.to_string(), eline, ecol))
          continue
        }
        if d == '\\' {
          adv()
          if i >= n {
            raise ParseError(pos, "unterminated string literal")
          }
          let e = cs[i]
          adv()
          buf.write_char(escape_char(pos, e))
          continue
        }
        buf.write_char(d)
        adv()
      }
      if buf.to_string() != "" || parts.length() == 0 {
        parts.push(SPStr(buf.to_string()))
      }
      toks.push({ tok: TStr(parts), pos, nl, })
      nl = false
      continue
    }
    let mut matched = false
    for s in symbols {
      let len = s.length()
      if i + len <= n {
        let mut ok = true
        for k = 0; k < len; k = k + 1 {
          if cs[i + k] != s.get_char(k).unwrap() {
            ok = false
            break
          }
        }
        if ok {
          for k = 0; k < len; k = k + 1 {
            adv()
          }
          toks.push({ tok: TSym(s), pos, nl, })
          nl = false
          matched = true
          break
        }
      }
    }
    if !matched {
      raise ParseError(pos, "unexpected character '" + c.to_string() + "'")
    }
  }
  toks.push({ tok: TEOF, pos: { line, col, }, nl: true, })
  toks
}

///|
fn escape_char(pos : Pos, e : Char) -> Char raise ParseError {
  match e {
    'n' => '\n'
    't' => '\t'
    'r' => '\r'
    '\\' => '\\'
    '"' => '"'
    '\'' => '\''
    '0' => '\u{0}'
    _ => raise ParseError(pos, "unknown escape \\" + e.to_string())
  }
}
