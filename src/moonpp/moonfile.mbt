///|
/// The configuration files of newer MoonBit toolchains: `moon.mod` (a
/// module), `moon.pkg` (a package) and `moon.work` (a workspace) share one
/// syntax of items:
///
/// ```
/// name = "user/module"
/// import {
///   "moonbitlang/x@0.5.6",
///   "moonbitlang/core/strconv" @conv,
/// }
/// import { "moonbitlang/x/fs" } for "test"
/// options("is-main": true, targets: { "a.mbt": [ "js" ] })
/// members = [ ".", "../lib" ]
/// ```
///
/// Older toolchains use `moon.mod.json` and `moon.pkg.json`; moonpp reads
/// both and writes the new files.
priv enum MValue {
  MStr(String)
  /// Identifiers, numbers, `true`, `false`.
  MAtom(String)
  MList(Array[MValue])
  MMap(Array[(String, MValue)])
} derive(Show)

///|
/// An entry of an `import { ... }` block: path and alias.
priv struct MImport {
  path : String
  pkg_alias : String?
  /// `for "test"` etc.
  kind : String?
}

///|
priv struct MoonFile {
  fields : Map[String, MValue]
  imports : Array[MImport]
  /// `options(k: v, ...)`, `pkgtype(kind: "executable")` and other calls:
  /// their named arguments, by call name.
  calls : Map[String, Array[(String, MValue)]]
}

///|
priv enum MTok {
  TStr(String)
  TWord(String)
  TPunct(Char)
} derive(Eq)

///|
fn moon_tokens(src : String) -> Array[MTok] raise Failure {
  let cs : Array[Char] = src.iter().collect()
  let out : Array[MTok] = []
  let mut i = 0
  while i < cs.length() {
    let c = cs[i]
    if c == ' ' || c == '\t' || c == '\r' || c == '\n' {
      i = i + 1
    } else if c == '/' && i + 1 < cs.length() && cs[i + 1] == '/' {
      while i < cs.length() && cs[i] != '\n' {
        i = i + 1
      }
    } else if c == '"' {
      let buf = StringBuilder()
      i = i + 1
      while i < cs.length() && cs[i] != '"' {
        if cs[i] == '\\' && i + 1 < cs.length() {
          i = i + 1
          buf.write_char(
            match cs[i] {
              'n' => '\n'
              't' => '\t'
              x => x
            },
          )
        } else {
          buf.write_char(cs[i])
        }
        i = i + 1
      }
      if i >= cs.length() {
        die("unterminated string")
      }
      i = i + 1
      out.push(TStr(buf.to_string()))
    } else if "{}()[],:=@".contains_char(c) {
      out.push(TPunct(c))
      i = i + 1
    } else {
      let buf = StringBuilder()
      while i < cs.length() && !" \t\r\n{}()[],:=@\"".contains_char(cs[i]) {
        buf.write_char(cs[i])
        i = i + 1
      }
      out.push(TWord(buf.to_string()))
    }
  }
  out
}

///|
fn parse_moon_file(src : String) -> MoonFile raise Failure {
  let toks = moon_tokens(src)
  let mut i = 0
  let peek = () => if i < toks.length() { Some(toks[i]) } else { None }
  fn expect(c : Char) -> Unit raise Failure {
    if peek() == Some(TPunct(c)) {
      i = i + 1
    } else {
      die("expected '" + c.to_string() + "'")
    }
  }

  fn key() -> String raise Failure {
    match peek() {
      Some(TStr(s)) | Some(TWord(s)) => {
        i = i + 1
        s
      }
      _ => die("expected a key")
    }
  }

  fn value() -> MValue raise Failure {
    match peek() {
      Some(TStr(s)) => {
        i = i + 1
        MStr(s)
      }
      Some(TWord(w)) => {
        i = i + 1
        MAtom(w)
      }
      Some(TPunct('[')) => {
        i = i + 1
        let xs : Array[MValue] = []
        while peek() != Some(TPunct(']')) {
          xs.push(value())
          if peek() == Some(TPunct(',')) {
            i = i + 1
          }
        }
        expect(']')
        MList(xs)
      }
      Some(TPunct('{')) => {
        i = i + 1
        let kvs : Array[(String, MValue)] = []
        while peek() != Some(TPunct('}')) {
          let k = key()
          expect(':')
          kvs.push((k, value()))
          if peek() == Some(TPunct(',')) {
            i = i + 1
          }
        }
        expect('}')
        MMap(kvs)
      }
      _ => die("expected a value")
    }
  }

  let fields : Map[String, MValue] = Map([])
  let imports : Array[MImport] = []
  let calls : Map[String, Array[(String, MValue)]] = Map([])
  while i < toks.length() {
    match peek() {
      Some(TWord("import")) if i + 1 < toks.length() &&
        toks[i + 1] == TPunct('{') => {
        i = i + 2
        let block : Array[(String, String?)] = []
        while peek() != Some(TPunct('}')) {
          let path = match peek() {
            Some(TStr(s)) => {
              i = i + 1
              s
            }
            _ => die("expected an import path")
          }
          let pkg_alias = if peek() == Some(TPunct('@')) {
            i = i + 1
            match peek() {
              Some(TWord(a)) => {
                i = i + 1
                Some(a)
              }
              _ => die("expected an alias after '@'")
            }
          } else {
            None
          }
          block.push((path, pkg_alias))
          if peek() == Some(TPunct(',')) {
            i = i + 1
          }
        }
        expect('}')
        let kind = if peek() == Some(TWord("for")) {
          i = i + 1
          match peek() {
            Some(TStr(s)) => {
              i = i + 1
              Some(s)
            }
            _ => die("expected a string after 'for'")
          }
        } else {
          None
        }
        for b in block {
          imports.push({ path: b.0, pkg_alias: b.1, kind, })
        }
      }
      Some(TWord(name)) if i + 1 < toks.length() && toks[i + 1] == TPunct('(') => {
        i = i + 2
        let args : Array[(String, MValue)] = calls.get(name).unwrap_or([])
        while peek() != Some(TPunct(')')) {
          let k = key()
          expect(':')
          args.push((k, value()))
          if peek() == Some(TPunct(',')) {
            i = i + 1
          }
        }
        expect(')')
        calls.set(name, args)
      }
      _ => {
        let k = key()
        expect('=')
        fields.set(k, value())
      }
    }
  }
  { fields, imports, calls, }
}

///|
/// Read a configuration file in the new syntax, if it exists.
fn read_moon_file(path : String) -> MoonFile? raise Failure {
  if !@fs.path_exists(path) {
    return None
  }
  let src = @fs.read_file_to_string(path) catch {
    @fs.IOError(msg) => die("cannot read " + path + ": " + msg)
  }
  Some(parse_moon_file(src)) catch {
    Failure(msg) => die(path + ": " + msg)
  }
}

///|
fn MoonFile::string_field(self : MoonFile, k : String) -> String? {
  match self.fields.get(k) {
    Some(MStr(s)) => Some(s)
    _ => None
  }
}

///|
/// The named argument `k` of the call `name(...)`: `options("is-main": true)`
/// gives `call_arg("options", "is-main")`.
fn MoonFile::call_arg(self : MoonFile, name : String, k : String) -> MValue? {
  for kv in self.calls.get(name).unwrap_or([]) {
    if kv.0 == k {
      return Some(kv.1)
    }
  }
  None
}

///|
/// The value of an option, `"is-main": true` etc.
fn MoonFile::option(self : MoonFile, k : String) -> MValue? {
  self.call_arg("options", k)
}

///|
/// A string literal of the new syntax.
fn mstr(s : String) -> String {
  s.escape()
}
