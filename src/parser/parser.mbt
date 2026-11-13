///|
struct Parser {
  toks : Array[Token]
  mut i : Int32
}

///|
fn Parser::peek(self : Parser) -> Token {
  self.toks[self.i]
}

///|
fn Parser::peek_at(self : Parser, k : Int32) -> Token {
  let j = self.i + k
  if j < self.toks.length() {
    self.toks[j]
  } else {
    self.toks[self.toks.length() - 1]
  }
}

///|
fn Parser::pos(self : Parser) -> Pos {
  self.peek().pos
}

///|
fn Parser::advance(self : Parser) -> Token {
  let t = self.toks[self.i]
  if self.i < self.toks.length() - 1 {
    self.i = self.i + 1
  }
  t
}

///|
fn Parser::at(self : Parser, s : String) -> Bool {
  self.peek().tok == TSym(s)
}

///|
fn Parser::at_k(self : Parser, k : Int32, s : String) -> Bool {
  self.peek_at(k).tok == TSym(s)
}

///|
/// The current token is `s` and on the same line as the previous one.
fn Parser::is_same_line(self : Parser, s : String) -> Bool {
  self.at(s) && !self.peek().nl
}

///|
fn Parser::accept(self : Parser, s : String) -> Bool {
  if self.at(s) {
    ignore(self.advance())
    true
  } else {
    false
  }
}

///|
fn tok_desc(t : Tok) -> String {
  match t {
    TIdent(s) => "identifier '" + s + "'"
    TInt(n) => "number " + n.to_string()
    TDouble(d) => "number " + d.to_string()
    TLit(_) => "literal"
    TStr(_) => "string literal"
    TChar(_) => "character literal"
    TSym(s) => "'" + s + "'"
    TEOF => "end of file"
  }
}

///|
fn[T] Parser::fail(self : Parser, msg : String) -> T raise ParseError {
  raise ParseError(self.pos(), msg + ", found " + tok_desc(self.peek().tok))
}

///|
fn Parser::expect(self : Parser, s : String) -> Unit raise ParseError {
  if !self.accept(s) {
    self.fail("expected '" + s + "'")
  }
}

///|
fn Parser::ident(self : Parser) -> String raise ParseError {
  match self.peek().tok {
    TIdent(s) => {
      ignore(self.advance())
      s
    }
    _ => self.fail("expected an identifier")
  }
}

///|
/// A name, or `@pkg.Name` from an imported package.
fn Parser::qual_ident(self : Parser) -> String raise ParseError {
  if self.accept("@") {
    let pkg = self.pkg_name()
    self.expect(".")
    "@" + pkg + "." + self.ident()
  } else {
    self.ident()
  }
}

///|
fn Parser::is_ident(self : Parser) -> Bool {
  self.peek().tok is TIdent(_)
}

///|
/// A statement or item ends here: `;`, `}`, end of file or a newline.
fn Parser::at_stmt_end(self : Parser) -> Bool {
  self.at(";") || self.at("}") || self.peek().tok == TEOF || self.peek().nl
}

///|
fn Parser::end_stmt(self : Parser) -> Unit raise ParseError {
  if self.accept(";") {
    return
  }
  if self.at_stmt_end() {
    return
  }
  self.fail("expected a newline or ';'")
}

///|
/// Skip `pub`, `priv`, `pub(all)` etc.
fn Parser::skip_visibility(self : Parser) -> Unit {
  if self.at("pub") || self.at("priv") {
    ignore(self.advance())
    if self.is_same_line("(") {
      ignore(self.advance())
      while !self.at(")") && self.peek().tok != TEOF {
        ignore(self.advance())
      }
      ignore(self.advance())
    }
  }
}

///|
fn Parser::skip_derive(self : Parser) -> Unit raise ParseError {
  if self.is_same_line("derive") {
    ignore(self.advance())
    self.expect("(")
    while !self.at(")") && self.peek().tok != TEOF {
      ignore(self.advance())
    }
    self.expect(")")
  }
}

// ---------------------------------------------------------------------------
// Binders

///|
/// `[x, y : A, M : Monad]`
fn Parser::impl_binders(self : Parser) -> Array[Binder] raise ParseError {
  let bs : Array[Binder] = []
  if !self.accept("[") {
    return bs
  }
  while !self.at("]") {
    let pos = self.pos()
    let name = if self.accept("_") { "_" } else { self.ident() }
    let ty = if self.accept(":") { Some(self.expr()) } else { None }
    bs.push({ pos, name, ty, kind: Positional, })
    if !self.accept(",") {
      break
    }
  }
  self.expect("]")
  bs
}

///|
/// Parameters `(x : A, y, B)`: an item is `name : type`, a bare name (whose
/// type is inferred) when `names_only`, and otherwise an anonymous type.
fn Parser::params(
  self : Parser,
  names_only : Bool,
) -> Array[Binder] raise ParseError {
  self.expect("(")
  let bs : Array[Binder] = []
  while !self.at(")") {
    let pos = self.pos()
    if self.is_ident() && (self.at_k(1, "~") || self.at_k(1, "?")) {
      // tagged parameters: `x~ : T`, `x~ : T = default`, `x? : T`
      let name = self.ident()
      let labelled = self.accept("~")
      if !labelled {
        self.expect("?")
      }
      self.expect(":")
      let ty = self.expr()
      let kind : ParamKind = if !labelled {
        Optional
      } else if self.accept("=") {
        Labelled(Some(self.expr()))
      } else {
        Labelled(None)
      }
      bs.push({ pos, name, ty: Some(ty), kind, })
    } else if (self.is_ident() || self.at("_")) && self.at_k(1, ":") {
      let name = if self.accept("_") { "_" } else { self.ident() }
      ignore(self.advance())
      bs.push({ pos, name, ty: Some(self.expr()), kind: Positional, })
    } else if names_only {
      let name = if self.accept("_") { "_" } else { self.ident() }
      bs.push({ pos, name, ty: None, kind: Positional, })
    } else {
      bs.push({ pos, name: "_", ty: Some(self.expr()), kind: Positional, })
    }
    if !self.accept(",") {
      break
    }
  }
  self.expect(")")
  bs
}

///|
/// Turn the elements of a parenthesised list into Pi binders.
fn exprs_to_binders(es : Array[Expr]) -> Array[Binder] {
  es.map(e => {
    match e {
      EAnn(p, EVar(_, x), t) =>
        { pos: p, name: x, ty: Some(t), kind: Positional, }
      EAnn(p, EHole(_), t) =>
        { pos: p, name: "_", ty: Some(t), kind: Positional, }
      _ => { pos: e.pos(), name: "_", ty: Some(e), kind: Positional, }
    }
  })
}

///|
/// Turn the elements of a parenthesised list into lambda parameters.
fn exprs_to_params(es : Array[Expr]) -> Array[Binder] raise ParseError {
  es.map(e => {
    match e {
      EVar(p, x) => { pos: p, name: x, ty: None, kind: Positional, }
      EHole(p) => { pos: p, name: "_", ty: None, kind: Positional, }
      EAnn(p, EVar(_, x), t) =>
        { pos: p, name: x, ty: Some(t), kind: Positional, }
      EAnn(p, EHole(_), t) =>
        { pos: p, name: "_", ty: Some(t), kind: Positional, }
      _ => raise ParseError(e.pos(), "invalid lambda parameter")
    }
  })
}

///|
/// Turn the elements of a `[...]` list into implicit binders.
fn exprs_to_impl_binders(es : Array[Expr]) -> Array[Binder] raise ParseError {
  es.map(e => {
    match e {
      EVar(p, x) => { pos: p, name: x, ty: None, kind: Positional, }
      EHole(p) => { pos: p, name: "_", ty: None, kind: Positional, }
      EAnn(p, EVar(_, x), t) =>
        { pos: p, name: x, ty: Some(t), kind: Positional, }
      EAnn(p, EHole(_), t) =>
        { pos: p, name: "_", ty: Some(t), kind: Positional, }
      _ => raise ParseError(e.pos(), "invalid implicit binder")
    }
  })
}

// ---------------------------------------------------------------------------
// Expressions

///|
pub fn Parser::expr(self : Parser) -> Expr raise ParseError {
  let e = self.arrow()
  // `e catch { arms }`: a `try` without the keyword
  if self.is_same_line("catch") {
    let pos = self.pos()
    ignore(self.advance())
    let arms = self.arms()
    return ETry(pos, e, arms, self.noraise_opt())
  }
  e
}

///|
fn Parser::raises_opt(self : Parser) -> Expr? raise ParseError {
  if self.is_same_line("raise") {
    ignore(self.advance())
    // `raise?` (error polymorphism) is treated as not raising
    if self.accept("?") {
      return None
    }
    if self.at("{") ||
      self.at("=") ||
      self.at_stmt_end() ||
      self.at(",") ||
      self.at(")") ||
      self.at("]") {
      Some(EVar(self.pos(), "Error"))
    } else {
      Some(self.pipe())
    }
  } else {
    None
  }
}

///|
/// The effect after a result type: `raise E`, `noraise` or nothing, and for
/// an `async` function the async effect `%Async[E]` (`E` is `Error` by
/// default, as async functions raise by default, and `%NoRaise` for
/// `noraise`).
fn Parser::effect_opt(self : Parser, is_async : Bool) -> Expr? raise ParseError {
  let pos = self.pos()
  let row0 = self.row_opt()
  let no_raise = self.is_same_line("noraise")
  if no_raise {
    ignore(self.advance())
  }
  let mut r = if no_raise { None } else { self.raises_opt() }
  // `nocancel` (an async function that cannot be cancelled) does not change
  // how it is called
  if is_async && self.peek().tok is TIdent("nocancel") && !self.peek().nl {
    ignore(self.advance())
  }
  let mut is_async = is_async
  // `!Raise[E]` is `raise E`, `!Async` is `async`
  let row = match row0 {
    Some(rw) => {
      let (rest, err, a) = split_builtin_effects(rw)
      if err is Some(_) {
        r = err
      }
      is_async = is_async || a
      // `!pure` stays an (empty) annotation: no inferred effect variable
      if rest is EVar(_, "%RowNil") && (err is Some(_) || a) {
        None
      } else {
        Some(rest)
      }
    }
    None => None
  }
  match row {
    Some(row) => {
      if is_async {
        raise ParseError(pos, "an async function cannot have other effects yet")
      }
      return Some(
        EApp(
          pos,
          EVar(pos, "%Effs"),
          Some([row, r.unwrap_or(EVar(pos, "%NoRaise"))]),
          None,
        ),
      )
    }
    None => ()
  }
  if !is_async {
    return r
  }
  let err : Expr = if no_raise {
    EVar(pos, "%NoRaise")
  } else {
    r.unwrap_or(EVar(pos, "Error"))
  }
  Some(EApp(pos, EVar(pos, "%Async"), Some([err]), None))
}

///|
/// The effects after a result type: `!E1 + E2 + e`, as the row
/// `%Row[E1, %Row[E2, e]]` (`%RowNil` at the end when there is no effect
/// variable). A lowercase name is an effect variable, except `pure`, the
/// effect without operations, which is left out.
fn Parser::row_opt(self : Parser) -> Expr? raise ParseError {
  if !self.is_same_line("!") {
    return None
  }
  let pos = self.pos()
  ignore(self.advance())
  let items : Array[Expr] = []
  let mut tail : Expr? = None
  while true {
    let ipos = self.pos()
    let item = self.unary()
    match item {
      EVar(_, "pure") => ()
      EVar(_, x) if x.length() > 0 && x[0] >= 'a' && x[0] <= 'z' => {
        if tail is Some(_) {
          raise ParseError(
            ipos, "an effect row has at most one effect variable",
          )
        }
        tail = Some(item)
      }
      _ => items.push(item)
    }
    if !self.accept("+") {
      break
    }
  }
  let mut row = tail.unwrap_or(EVar(pos, "%RowNil"))
  for i = items.length() - 1; i >= 0; i = i - 1 {
    row = EApp(pos, EVar(pos, "%Row"), Some([items[i], row]), None)
  }
  Some(row)
}

///|
/// `Raise[E]` (`Raise`: `Raise[Error]`) and `Async` in a row: the errors and
/// the async effect, kept apart from the row (see `effect_opt`). Returns the
/// other items, the error type and whether `Async` is there.
fn split_builtin_effects(row : Expr) -> (Expr, Expr?, Bool) raise ParseError {
  let items : Array[Expr] = []
  let mut err : Expr? = None
  let mut is_async = false
  let mut r = row
  while r is EApp(_, EVar(_, "%Row"), Some([item, rest]), _) {
    match item {
      EApp(_, EVar(_, "Raise"), Some([e]), _) => err = Some(e)
      EVar(p, "Raise") => err = Some(EVar(p, "Error"))
      EVar(_, "Async") => is_async = true
      _ => items.push(item)
    }
    r = rest
  }
  let mut out = r
  for i = items.length() - 1; i >= 0; i = i - 1 {
    out = EApp(r.pos(), EVar(r.pos(), "%Row"), Some([items[i], out]), None)
  }
  (out, err, is_async)
}

///|
/// The result type of a lambda with its effect.
fn lam_ret(pos : Pos, ret : Expr?, eff : Expr?) -> Expr? {
  match eff {
    Some(e) => Some(EEff(pos, ret.unwrap_or(EHole(pos)), e))
    None => ret
  }
}

///|
fn Parser::arrow(self : Parser) -> Expr raise ParseError {
  let pos = self.pos()
  let is_async = self.at("async") && self.at_k(1, "(")
  if is_async {
    ignore(self.advance())
  }
  let parenthesised = self.at("(")
  let lhs = self.pipe()
  if !self.at("->") {
    if is_async {
      self.fail("expected `->` in an async function type")
    }
    return lhs
  }
  ignore(self.advance())
  let cod = self.arrow()
  let raises = self.effect_opt(is_async)
  let binders = match lhs {
    ETuple(_, es) if parenthesised => exprs_to_binders(es)
    // `(T[X]) -> Y`: the parentheses wrap the call-like `T[X]` in a block
    EBlock(_, [SExpr(_, e)]) if parenthesised => exprs_to_binders([e])
    ELit(_, LUnit) if parenthesised => []
    _ => exprs_to_binders([lhs])
  }
  EPi(pos, [], Some(binders), cod, raises)
}

///|
fn Parser::pipe(self : Parser) -> Expr raise ParseError {
  let mut lhs = self.binary(0)
  while self.at("|>") {
    let pos = self.pos()
    ignore(self.advance())
    let rhs = self.binary(0)
    lhs = match rhs {
      EApp(p, f, impl_args, Some(args)) =>
        EApp(p, f, impl_args, Some([lhs, ..args]))
      EMethod(p, e, m, impl_args, args) =>
        EMethod(p, e, m, impl_args, [lhs, ..args])
      _ => EApp(pos, rhs, None, Some([lhs]))
    }
  }
  lhs
}

///|
fn bin_prec(op : String) -> Int32 {
  match op {
    // as in MoonBit: bitwise operators bind looser than comparisons
    "||" => 1
    "&&" => 2
    "|" => 3
    "^" => 4
    "&" => 5
    "==" | "!=" | "===" | "<" | ">" | "<=" | ">=" | "is" => 6
    "..<" | "..=" => 7
    "<<" | ">>" => 8
    "+" | "-" => 9
    "*" | "/" | "%" => 10
    _ => -1
  }
}

///|
fn Parser::binary(self : Parser, min_prec : Int32) -> Expr raise ParseError {
  let mut lhs = self.unary()
  while true {
    let t = self.peek()
    let op = match t.tok {
      TSym(s) => s
      _ => break
    }
    let prec = bin_prec(op)
    if prec < 0 || prec < min_prec {
      break
    }
    // A line starting with `-` begins a new statement.
    if t.nl && op == "-" {
      break
    }
    ignore(self.advance())
    if op == "is" {
      lhs = EIs(t.pos, lhs, self.pattern())
      continue
    }
    let rhs = self.binary(prec + 1)
    lhs = if op == "..<" || op == "..=" {
      ERange(t.pos, lhs, rhs, op == "..=")
    } else {
      EBin(t.pos, op, lhs, rhs)
    }
  }
  lhs
}

///|
fn Parser::unary(self : Parser) -> Expr raise ParseError {
  let pos = self.pos()
  if self.accept("-") {
    match self.peek().tok {
      TInt(n) => {
        ignore(self.advance())
        return self.postfix(ELit(pos, LInt(-n)))
      }
      TDouble(d) => {
        ignore(self.advance())
        return self.postfix(ELit(pos, LDouble(-d)))
      }
      TLit(LInt64(n)) => {
        ignore(self.advance())
        return self.postfix(ELit(pos, LInt64(-n)))
      }
      TLit(LFloat(f)) => {
        ignore(self.advance())
        return self.postfix(ELit(pos, LFloat(-f)))
      }
      _ => ()
    }
    return EUn(pos, "-", self.unary())
  }
  if self.accept("!") {
    return EUn(pos, "!", self.unary())
  }
  // `&Show`: a trait object type
  if self.accept("&") {
    return EUn(pos, "&", self.unary())
  }
  if self.accept("<-") {
    return EBind(pos, self.unary())
  }
  self.postfix(self.primary())
}

///|
fn Parser::args(self : Parser, close : String) -> Array[Expr] raise ParseError {
  let es : Array[Expr] = []
  while !self.at(close) {
    // tagged arguments are for calls; in `[...]`, `T?` is a type, and
    // `T raise E`, `T!Eff` are types of code (`Code[T raise E]`)
    es.push(
      if close == ")" {
        self.arg()
      } else {
        let pos = self.pos()
        let e = self.expr()
        match self.effect_opt(false) {
          Some(eff) => EEff(pos, e, eff)
          None => e
        }
      },
    )
    if !self.accept(",") {
      break
    }
  }
  self.expect(close)
  es
}

///|
/// A call argument: an expression or a tagged argument `label=e`, `label~`,
/// `label?=e`, `label?`.
fn Parser::arg(self : Parser) -> Expr raise ParseError {
  let pos = self.pos()
  match self.peek().tok {
    TIdent(x) if self.at_k(1, "=") => {
      ignore(self.advance())
      ignore(self.advance())
      ETagged(pos, x, self.expr(), false)
    }
    TIdent(x) if self.at_k(1, "~") => {
      ignore(self.advance())
      ignore(self.advance())
      ETagged(pos, x, EVar(pos, x), false)
    }
    TIdent(x) if self.at_k(1, "?") && self.at_k(2, "=") => {
      ignore(self.advance())
      ignore(self.advance())
      ignore(self.advance())
      ETagged(pos, x, self.expr(), true)
    }
    TIdent(x) if self.at_k(1, "?") && (self.at_k(2, ",") || self.at_k(2, ")")) => {
      ignore(self.advance())
      ignore(self.advance())
      ETagged(pos, x, EVar(pos, x), true)
    }
    _ => self.expr()
  }
}

///|
fn Parser::postfix(self : Parser, e0 : Expr) -> Expr raise ParseError {
  let mut e = e0
  while true {
    let pos = self.pos()
    if self.is_same_line("(") {
      ignore(self.advance())
      let args = self.args(")")
      e = match e {
        EApp(p, f, Some(impl_args), None) =>
          EApp(p, f, Some(impl_args), Some(args))
        _ => EApp(pos, e, None, Some(args))
      }
    } else if self.is_same_line("[") {
      ignore(self.advance())
      let args = self.args("]")
      e = EApp(pos, e, Some(args), None)
    } else if self.is_same_line("?") {
      // `T?` is `Option[T]` (tagged arguments `x?=e` are parsed by `arg`)
      ignore(self.advance())
      e = EApp(pos, EVar(pos, "Option"), Some([e]), None)
    } else if self.at(".") && !self.at_k(1, ".") {
      ignore(self.advance())
      match self.peek().tok {
        TInt(n) => {
          ignore(self.advance())
          e = EField(pos, e, n.to_string())
        }
        _ => {
          // field and method calls are at the position of their name
          let npos = self.pos()
          let name = self.ident()
          if self.is_same_line("[") || self.is_same_line("(") {
            let impl_args = if self.is_same_line("[") {
              ignore(self.advance())
              Some(self.args("]"))
            } else {
              None
            }
            if impl_args is Some(idx) && !self.is_same_line("(") {
              // `e.f[i]`: index into a field
              e = EApp(pos, EField(npos, e, name), Some(idx), None)
            } else {
              self.expect("(")
              let args = self.args(")")
              e = EMethod(npos, e, name, impl_args, args)
            }
          } else {
            e = EField(npos, e, name)
          }
        }
      }
    } else if self.at("..") && self.peek_at(1).tok is TIdent(_) {
      // `x..f(a)..g()`: method calls on `x`, whose value is `x`
      let tmp = "__cascade_" + pos.line.to_string() + "_" + pos.col.to_string()
      let stmts : Array[Stmt] = [SLet(pos, PVar(pos, tmp), None, e)]
      while self.at("..") && self.peek_at(1).tok is TIdent(_) {
        ignore(self.advance())
        let npos = self.pos()
        let name = self.ident()
        self.expect("(")
        let args = self.args(")")
        stmts.push(
          SExpr(npos, EMethod(npos, EVar(npos, tmp), name, None, args)),
        )
      }
      stmts.push(SExpr(pos, EVar(pos, tmp)))
      e = EBlock(pos, stmts)
    } else {
      break
    }
  }
  e
}

///|
/// An element of a parenthesised or bracketed list: `e` or `e : T`.
fn Parser::ann_elem(self : Parser) -> Expr raise ParseError {
  let e = self.expr()
  if self.at(":") {
    let pos = self.pos()
    ignore(self.advance())
    EAnn(pos, e, self.expr())
  } else {
    e
  }
}

///|
fn Parser::block(self : Parser) -> Expr raise ParseError {
  // inside a block, `unfold(f) { e }` is an unfolding again
  let saved = in_condition.val
  in_condition.val = false
  errdefer { in_condition.val = saved }
  let r = self.block_in()
  in_condition.val = saved
  r
}

///|
fn Parser::block_in(self : Parser) -> Expr raise ParseError {
  let pos = self.pos()
  self.expect("{")
  let stmts : Array[Stmt] = []
  while !self.at("}") {
    if self.accept(";") {
      continue
    }
    stmts.push(self.stmt())
    if !self.at("}") {
      self.end_stmt()
    }
  }
  self.expect("}")
  EBlock(pos, stmts)
}

///|
fn Parser::is_struct_literal(self : Parser) -> Bool {
  // `{ x: ...`, `{ x, ...` or `{ x }` with a following field list
  if !self.at("{") {
    return false
  }
  match self.peek_at(1).tok {
    TIdent(_) => self.at_k(2, ":") || self.at_k(2, ",")
    TSym("..") => true
    _ => false
  }
}

///|
fn Parser::struct_literal(self : Parser) -> Expr raise ParseError {
  let pos = self.pos()
  self.expect("{")
  let fields : Array[(String, Expr)] = []
  // `{ ..base, x: e }`: the base is the field `..`
  if self.accept("..") {
    fields.push(("..", self.expr()))
    ignore(self.accept(","))
  }
  while !self.at("}") {
    let fpos = self.pos()
    let name = self.ident()
    let e = if self.accept(":") { self.expr() } else { EVar(fpos, name) }
    fields.push((name, e))
    if !self.accept(",") {
      break
    }
  }
  self.expect("}")
  EStruct(pos, fields)
}

///|
fn Parser::lambda_body(self : Parser) -> Expr raise ParseError {
  if self.at("{") && !self.is_struct_literal() {
    self.block()
  } else {
    self.expr()
  }
}

///|
fn Parser::primary(self : Parser) -> Expr raise ParseError {
  let t = self.peek()
  let pos = t.pos
  match t.tok {
    TInt(n) => {
      ignore(self.advance())
      ELit(pos, LInt(n))
    }
    TChar(c) => {
      ignore(self.advance())
      ELit(pos, LChar(c))
    }
    TDouble(d) => {
      ignore(self.advance())
      ELit(pos, LDouble(d))
    }
    TLit(l) => {
      ignore(self.advance())
      ELit(pos, l)
    }
    TSym("@") => {
      // `@pkg.name`: a name from an imported package
      ignore(self.advance())
      let pkg = self.pkg_name()
      self.expect(".")
      let mut name = "@" + pkg + "." + self.ident()
      while self.at("::") {
        ignore(self.advance())
        name = name + "::" + self.ident()
      }
      EVar(pos, name)
    }
    TStr(parts) => {
      ignore(self.advance())
      match parts {
        [SPStr(s)] => ELit(pos, LStr(s))
        _ => {
          let out : Array[InterpPart] = []
          for p in parts {
            match p {
              SPStr(s) => out.push(IStr(s))
              SPExpr(src, line, col) => {
                let sub = { toks: tokenize(src, line0=line, col0=col), i: 0, }
                let e = sub.expr()
                if sub.peek().tok != TEOF {
                  sub.fail("unexpected token in interpolation")
                }
                out.push(IExpr(e))
              }
            }
          }
          EInterp(pos, out)
        }
      }
    }
    // `perform Op(args)` (`perform` is not a keyword)
    TIdent("perform") if self.peek_at(1).tok is TIdent(_) => {
      ignore(self.advance())
      let op = self.qual_ident()
      let args = if self.is_same_line("(") {
        ignore(self.advance())
        self.args(")")
      } else {
        []
      }
      EPerform(pos, op, args)
    }
    // `unfold(f, g) { e }` (`unfold` is not a keyword)
    TIdent("unfold") if self.at_unfold_block() => {
      ignore(self.advance())
      self.expect("(")
      let names = self.unfold_names()
      self.expect(")")
      EUnfold(pos, names, self.block())
    }
    // `code { e }`: the code of `e` (`code` is not a keyword; see
    // doc/mbtpp/staging.md). It is `%quote(() => e)`: code is a thunk.
    TIdent("code") if !in_condition.val &&
      self.at_k(1, "{") &&
      !self.peek_at(1).nl => {
      ignore(self.advance())
      let body = self.block()
      EApp(
        pos,
        EVar(pos, "%quote"),
        None,
        Some([ELam(pos, [], [], None, body)]),
      )
    }
    // `${ e }`, `$x`: the splice of the code `e`, `%splice(e)`
    TSym("$") => {
      ignore(self.advance())
      let e = if self.at("{") {
        self.block()
      } else {
        let p = self.pos()
        let mut name = self.ident()
        while self.at("::") {
          ignore(self.advance())
          name = name + "::" + self.ident()
        }
        EVar(p, name)
      }
      EApp(pos, EVar(pos, "%splice"), None, Some([e]))
    }
    TIdent(x) => {
      ignore(self.advance())
      if self.at("=>") {
        ignore(self.advance())
        return ELam(
          pos,
          [],
          [{ pos, name: x, ty: None, kind: Positional, }],
          None,
          self.lambda_body(),
        )
      }
      let mut name = x
      while self.at("::") {
        ignore(self.advance())
        name = name + "::" + self.ident()
      }
      EVar(pos, name)
    }
    TSym("_") => {
      ignore(self.advance())
      if self.accept("=>") {
        return ELam(
          pos,
          [],
          [{ pos, name: "_", ty: None, kind: Positional, }],
          None,
          self.lambda_body(),
        )
      }
      EHole(pos)
    }
    TSym("true") => {
      ignore(self.advance())
      ELit(pos, LBool(true))
    }
    TSym("false") => {
      ignore(self.advance())
      ELit(pos, LBool(false))
    }
    TSym("Type") => {
      ignore(self.advance())
      EType(pos)
    }
    TSym("Prop") => {
      ignore(self.advance())
      EProp(pos)
    }
    TSym("(") => {
      ignore(self.advance())
      let es : Array[Expr] = []
      let mut trailing = false
      while !self.at(")") {
        es.push(self.ann_elem())
        trailing = false
        if !self.accept(",") {
          break
        }
        trailing = true
      }
      self.expect(")")
      if self.at("=>") {
        ignore(self.advance())
        return ELam(pos, [], exprs_to_params(es), None, self.lambda_body())
      }
      if es.length() == 0 {
        ELit(pos, LUnit)
      } else if es.length() == 1 && !trailing {
        // `(xs[i])(x)` calls the element: not `f[T](x)`
        match es[0] {
          EApp(_, _, Some(_), None) as e => EBlock(pos, [SExpr(pos, e)])
          e => e
        }
      } else {
        ETuple(pos, es)
      }
    }
    TSym("[") => {
      ignore(self.advance())
      let es : Array[Expr] = []
      while !self.at("]") {
        es.push(self.ann_elem())
        if !self.accept(",") {
          break
        }
      }
      self.expect("]")
      if self.is_same_line("(") || self.at("->") {
        let impl_bs = exprs_to_impl_binders(es)
        let expl = if self.at("(") {
          let ps = self.pipe()
          match ps {
            ETuple(_, xs) => Some(exprs_to_binders(xs))
            ELit(_, LUnit) => Some([])
            _ => Some(exprs_to_binders([ps]))
          }
        } else {
          None
        }
        self.expect("->")
        let cod = self.arrow()
        let raises = self.effect_opt(false)
        return EPi(pos, impl_bs, expl, cod, raises)
      }
      for e in es {
        if e is EAnn(p, _, _) {
          raise ParseError(p, "unexpected ':' in array literal")
        }
      }
      EArray(pos, es)
    }
    TSym("{") =>
      if self.is_struct_literal() {
        self.struct_literal()
      } else if self.is_map_literal() {
        self.map_literal()
      } else {
        self.block()
      }
    TSym("fn") | TSym("async") => {
      let is_async = self.accept("async")
      self.expect("fn")
      let impl_bs = self.impl_binders()
      let ps = self.params(true)
      let ret = if self.accept("->") { Some(self.expr()) } else { None }
      let eff = self.effect_opt(is_async)
      ELam(pos, impl_bs, ps, lam_ret(pos, ret, eff), self.block())
    }
    TSym("if") => self.if_expr()
    TSym("match") => self.match_expr()
    TSym("try") => {
      ignore(self.advance())
      if self.accept("?") {
        return ETryQ(pos, self.expr())
      }
      let body = if self.at("{") { self.block() } else { self.arrow() }
      self.expect("catch")
      let arms = self.arms()
      ETry(pos, body, arms, self.noraise_opt())
    }
    TSym("raise") => {
      ignore(self.advance())
      ERaise(pos, self.expr())
    }
    TSym("return") => {
      ignore(self.advance())
      if self.at_stmt_end() {
        EReturn(pos, None)
      } else {
        EReturn(pos, Some(self.expr()))
      }
    }
    TSym("break") => {
      ignore(self.advance())
      let label = self.label_ref()
      if self.at_stmt_end() || self.at(",") || self.at(")") {
        EBreak(pos, label, None)
      } else {
        EBreak(pos, label, Some(self.expr()))
      }
    }
    TSym("continue") => {
      ignore(self.advance())
      let label = self.label_ref()
      let args : Array[Expr] = []
      if !(self.at_stmt_end() || self.at(")")) {
        args.push(self.expr())
        while self.accept(",") {
          args.push(self.expr())
        }
      }
      EContinue(pos, label, args)
    }
    // loops are expressions too (`let x = for ... { break v } nobreak { d }`)
    TSym("while" | "for") => EBlock(pos, [self.loop_stmt(pos, None)])
    TSym("loop") => self.loop_expr(pos, None)
    TIdent(_) if self.at_k(1, "~") && self.at_k(2, ":") => {
      let label = self.ident()
      ignore(self.advance())
      ignore(self.advance())
      if self.at("loop") {
        self.loop_expr(pos, Some(label))
      } else {
        EBlock(pos, [self.loop_stmt(pos, Some(label))])
      }
    }
    TSym("monad") => {
      ignore(self.advance())
      EMonad(pos, self.block())
    }
    TSym("proof") => {
      ignore(self.advance())
      EProof(pos, self.tactics())
    }
    TSym("forall") => {
      ignore(self.advance())
      let names : Array[(Pos, String)] = []
      while !self.at(":") && !self.at(",") {
        let p = self.pos()
        let name = if self.accept("_") { "_" } else { self.ident() }
        names.push((p, name))
      }
      let ty = if self.accept(":") { Some(self.expr()) } else { None }
      self.expect(",")
      let body = self.expr()
      let bs = names.map(pn => { pos: pn.0, name: pn.1, ty, kind: Positional, })
      EPi(pos, [], Some(bs), body, None)
    }
    _ => self.fail("expected an expression")
  }
}

///|
/// `noraise { arms }` after the handlers of a `try`.
fn Parser::noraise_opt(self : Parser) -> Array[Arm]? raise ParseError {
  if self.accept("noraise") {
    Some(self.arms())
  } else {
    None
  }
}

///|
fn Parser::if_expr(self : Parser) -> Expr raise ParseError {
  let pos = self.pos()
  self.expect("if")
  let c = self.cond_expr()
  let t = self.block()
  if self.accept("else") {
    let e = if self.at("if") { self.if_expr() } else { self.block() }
    EIf(pos, c, t, Some(e))
  } else {
    EIf(pos, c, t, None)
  }
}

///|
fn Parser::match_expr(self : Parser) -> Expr raise ParseError {
  let pos = self.pos()
  self.expect("match")
  let scrut = self.cond_expr()
  let as_name = if self.accept("as") { Some(self.ident()) } else { None }
  let in_ty = if self.accept("in") { Some(self.expr()) } else { None }
  let ret = if self.accept("return") { Some(self.expr()) } else { None }
  let mr = if as_name is None && in_ty is None && ret is None {
    None
  } else {
    Some({ as_name, in_ty, ret, })
  }
  EMatch(pos, scrut, mr, self.arms())
}

///|
fn Parser::arms(self : Parser) -> Array[Arm] raise ParseError {
  self.expect("{")
  let arms : Array[Arm] = []
  while !self.at("}") {
    if self.accept(";") {
      continue
    }
    let pos = self.pos()
    let pat = self.pattern()
    let cond = if self.accept("if") { Some(self.guard_expr()) } else { None }
    let rhs = if self.accept("=>") {
      Some(
        if self.at("{") && !self.is_struct_literal() && !self.is_map_literal() {
          self.block()
        } else {
          self.expr_or_assign()
        },
      )
    } else {
      None
    }
    arms.push({ pos, pat, cond, rhs, })
    if !self.at("}") {
      self.end_stmt()
    }
  }
  self.expect("}")
  arms
}

// ---------------------------------------------------------------------------
// Patterns

///|
fn is_upper(s : String) -> Bool {
  match s.get_char(0) {
    Some(c) => c >= 'A' && c <= 'Z'
    None => false
  }
}

///|
/// The arguments of a constructor pattern `C[impl](expl)`.
fn Parser::con_pattern_args(
  self : Parser,
  pos : Pos,
  name : String,
) -> Pat raise ParseError {
  let impl_ps = if self.is_same_line("[") {
    ignore(self.advance())
    let ps : Array[Pat] = []
    while !self.at("]") {
      ps.push(self.pattern())
      if !self.accept(",") {
        break
      }
    }
    self.expect("]")
    Some(ps)
  } else {
    None
  }
  let ps : Array[Pat] = []
  if self.is_same_line("(") {
    ignore(self.advance())
    while !self.at(")") {
      // `..`: the other arguments match anything
      if self.at("..") {
        let lpos = self.pos()
        ignore(self.advance())
        ps.push(PLabel(lpos, "..", PWild(lpos)))
      } else if self.is_ident() && self.at_k(1, "~") {
        // `x~` and `x=p`: a labelled field
        let lpos = self.pos()
        let l = self.ident()
        ignore(self.advance())
        ps.push(PLabel(lpos, l, PVar(lpos, l)))
      } else if self.is_ident() && self.at_k(1, "=") {
        let lpos = self.pos()
        let l = self.ident()
        ignore(self.advance())
        ps.push(PLabel(lpos, l, self.pattern()))
      } else {
        ps.push(self.pattern())
      }
      if !self.accept(",") {
        break
      }
    }
    self.expect(")")
  }
  PCon(pos, name, impl_ps, ps)
}

///|
/// `p | q`, `p as x` (`as` binds loosest).
fn Parser::pattern(self : Parser) -> Pat raise ParseError {
  let mut p = self.pattern_atom()
  while self.at("|") {
    let pos = self.pos()
    ignore(self.advance())
    p = POr(pos, p, self.pattern_atom())
  }
  while self.at("as") {
    let pos = self.pos()
    ignore(self.advance())
    p = PAs(pos, p, self.ident())
  }
  p
}

///|
fn Parser::pattern_atom(self : Parser) -> Pat raise ParseError {
  let pos = self.pos()
  let p = self.pattern_atom1()
  // `lo..=hi`, `lo..<hi`
  if self.at("..=") || self.at("..<") {
    let incl = self.at("..=")
    ignore(self.advance())
    let bound = (q : Pat) => {
      match q {
        PLit(_, l) => Some(Some(l))
        PWild(_) => Some(None)
        _ => None
      }
    }
    let lo = match bound(p) {
      Some(l) => l
      None => raise ParseError(p.pos(), "a range pattern is between literals")
    }
    let q = self.pattern_atom1()
    let hi = match bound(q) {
      Some(l) => l
      None => raise ParseError(q.pos(), "a range pattern is between literals")
    }
    return PRange(pos, lo, hi, incl)
  }
  p
}

///|
fn Parser::pattern_atom1(self : Parser) -> Pat raise ParseError {
  let t = self.peek()
  let pos = t.pos
  match t.tok {
    // `{ x, y: p, .. }`
    TSym("{") => {
      ignore(self.advance())
      let fields : Array[(String, Pat)] = []
      let mut open = false
      while !self.at("}") {
        if self.accept("..") {
          open = true
          ignore(self.accept(","))
          break
        }
        let fpos = self.pos()
        let f = self.ident()
        let p = if self.accept(":") { self.pattern() } else { PVar(fpos, f) }
        fields.push((f, p))
        if !self.accept(",") {
          break
        }
      }
      self.expect("}")
      PStruct(pos, fields, open)
    }
    // `[p, q, ..rest, r]`
    TSym("[") => {
      ignore(self.advance())
      let before : Array[Pat] = []
      let after : Array[Pat] = []
      let mut rest : String?? = None
      while !self.at("]") {
        let dpos = self.pos()
        if self.accept("..") {
          if rest is Some(_) {
            raise ParseError(dpos, "an array pattern has at most one `..`")
          }
          rest = if self.is_ident() {
            Some(Some(self.ident()))
          } else {
            Some(None)
          }
        } else if rest is Some(_) {
          after.push(self.pattern())
        } else {
          before.push(self.pattern())
        }
        if !self.accept(",") {
          break
        }
      }
      self.expect("]")
      PArray(pos, before, rest, after)
    }
    TSym("_") => {
      ignore(self.advance())
      PWild(pos)
    }
    TInt(n) => {
      ignore(self.advance())
      PLit(pos, LInt(n))
    }
    TLit(l) => {
      ignore(self.advance())
      PLit(pos, l)
    }
    TSym("-") => {
      ignore(self.advance())
      match self.peek().tok {
        TInt(n) => {
          ignore(self.advance())
          PLit(pos, LInt(-n))
        }
        TLit(LInt64(n)) => {
          ignore(self.advance())
          PLit(pos, LInt64(-n))
        }
        _ => self.fail("expected a number")
      }
    }
    TStr([SPStr(s)]) => {
      ignore(self.advance())
      PLit(pos, LStr(s))
    }
    TChar(c) => {
      ignore(self.advance())
      PLit(pos, LChar(c))
    }
    TSym("true") => {
      ignore(self.advance())
      PLit(pos, LBool(true))
    }
    TSym("false") => {
      ignore(self.advance())
      PLit(pos, LBool(false))
    }
    TSym("@") => {
      // `@pkg.Type::Ctor(..)`: a constructor of an imported type
      ignore(self.advance())
      let pkg = self.pkg_name()
      self.expect(".")
      let mut name = "@" + pkg + "." + self.ident()
      while self.at("::") {
        ignore(self.advance())
        name = name + "::" + self.ident()
      }
      self.con_pattern_args(pos, name)
    }
    TSym("(") => {
      ignore(self.advance())
      let ps : Array[Pat] = []
      let mut trailing = false
      while !self.at(")") {
        ps.push(self.pattern())
        trailing = false
        if !self.accept(",") {
          break
        }
        trailing = true
      }
      self.expect(")")
      if ps.length() == 0 {
        PLit(pos, LUnit)
      } else if ps.length() == 1 && !trailing {
        ps[0]
      } else {
        PTuple(pos, ps)
      }
    }
    TIdent(x) => {
      ignore(self.advance())
      let mut name = x
      while self.at("::") {
        ignore(self.advance())
        name = name + "::" + self.ident()
      }
      if !is_upper(x) && !name.contains("::") {
        return PVar(pos, name)
      }
      self.con_pattern_args(pos, name)
    }
    _ => self.fail("expected a pattern")
  }
}

// ---------------------------------------------------------------------------
// Statements

///|
fn Parser::stmt(self : Parser) -> Stmt raise ParseError {
  let pos = self.pos()
  if self.accept("let") {
    if self.accept("mut") {
      let name = self.ident()
      let ty = if self.accept(":") { Some(self.expr()) } else { None }
      self.expect("=")
      return SLetMut(pos, name, ty, self.expr())
    }
    let pat = self.pattern()
    if self.accept("<-") {
      return SLetBind(pos, pat, self.expr())
    }
    let ty = if self.accept(":") { Some(self.expr()) } else { None }
    self.expect("=")
    return SLet(pos, pat, ty, self.expr())
  }
  if self.at("fn") && (self.peek_at(1).tok is TIdent(_) || self.at_k(1, "[")) {
    ignore(self.advance())
    return SFn(pos, self.fn_rest(pos, false))
  }
  if self.at("async") &&
    self.at_k(1, "fn") &&
    (self.peek_at(2).tok is TIdent(_) || self.at_k(2, "[")) {
    ignore(self.advance())
    ignore(self.advance())
    return SFn(pos, self.fn_rest(pos, false, is_async=true))
  }
  if self.accept("defer") {
    return SDefer(pos, self.expr())
  }
  if self.accept("guard") {
    let c = self.cond_expr()
    let e = if self.accept("else") { Some(self.block()) } else { None }
    return SGuard(pos, c, e)
  }
  if self.at("while") || self.at("for") {
    return self.loop_stmt(pos, None)
  }
  if self.is_ident() && self.at_k(1, "~") && self.at_k(2, ":") {
    let label = self.ident()
    ignore(self.advance())
    ignore(self.advance())
    if self.at("loop") {
      return SExpr(pos, self.loop_expr(pos, Some(label)))
    }
    return self.loop_stmt(pos, Some(label))
  }
  let e = self.expr()
  for op in ["=", "+=", "-=", "*=", "/="] {
    if self.at(op) {
      ignore(self.advance())
      return SAssign(pos, e, op, self.expr())
    }
  }
  SExpr(pos, e)
}

///|
/// `label~` after `break` or `continue`.
fn Parser::label_ref(self : Parser) -> String? raise ParseError {
  if self.is_ident() && self.at_k(1, "~") && !self.peek().nl {
    let l = self.ident()
    ignore(self.advance())
    Some(l)
  } else {
    None
  }
}

///|
/// `loop a, b { p, q => ... }`
fn Parser::loop_expr(
  self : Parser,
  pos : Pos,
  label : String?,
) -> Expr raise ParseError {
  self.expect("loop")
  let args = [self.expr()]
  while self.accept(",") {
    args.push(self.expr())
  }
  self.expect("{")
  let arms : Array[Arm] = []
  while !self.at("}") {
    if self.accept(";") {
      continue
    }
    let apos = self.pos()
    let ps = [self.pattern()]
    while self.accept(",") {
      ps.push(self.pattern())
    }
    let pat = if ps.length() == 1 { ps[0] } else { PTuple(apos, ps) }
    let cond = if self.accept("if") { Some(self.guard_expr()) } else { None }
    self.expect("=>")
    let rhs = if self.at("{") && !self.is_struct_literal() {
      self.block()
    } else {
      self.expr()
    }
    arms.push({ pos: apos, pat, cond, rhs: Some(rhs), })
    if !self.at("}") {
      self.end_stmt()
    }
  }
  self.expect("}")
  ELoop(pos, label, args, arms)
}

///|
/// A `while` or `for` loop, with its label and `nobreak` block.
fn Parser::loop_stmt(
  self : Parser,
  pos : Pos,
  label : String?,
) -> Stmt raise ParseError {
  let s = self.plain_loop(pos)
  // `nobreak { e }` (older MoonBit: `else { e }`)
  let no_break = if self.at("else") ||
    (self.peek().tok == TIdent("nobreak") && self.at_k(1, "{")) {
    ignore(self.advance())
    Some(self.block())
  } else {
    None
  }
  match (label, no_break) {
    (None, None) => s
    _ => SLoopX(pos, label, s, no_break)
  }
}

///|
fn Parser::plain_loop(self : Parser, pos : Pos) -> Stmt raise ParseError {
  if self.accept("while") {
    let c = self.cond_expr()
    return SWhile(pos, c, self.block())
  }
  self.expect("for")
  // `for x in e`, `for i, x in e`
  if self.is_ident() && (self.at_k(1, "in") || self.at_k(1, ",")) {
    let xs = [self.ident()]
    if self.accept(",") {
      xs.push(self.ident())
    }
    self.expect("in")
    let e = self.cond_expr()
    return SForIn(pos, xs, e, self.block())
  }
  let inits : Array[(String, Expr)] = []
  while !self.at(";") {
    let x = self.ident()
    self.expect("=")
    inits.push((x, self.expr()))
    if !self.accept(",") {
      break
    }
  }
  self.expect(";")
  let cond = if self.at(";") { None } else { Some(self.expr()) }
  self.expect(";")
  let updates : Array[(String, Expr)] = []
  while !self.at("{") {
    let x = self.ident()
    self.expect("=")
    updates.push((x, self.expr()))
    if !self.accept(",") {
      break
    }
  }
  SFor(pos, inits, cond, updates, self.block())
}

// ---------------------------------------------------------------------------
// Tactics

///|
fn Parser::tactics(self : Parser) -> Array[Tactic] raise ParseError {
  self.expect("{")
  let ts : Array[Tactic] = []
  while !self.at("}") {
    if self.accept(";") {
      continue
    }
    let pos = self.pos()
    let name = self.ident()
    let t = match name {
      "intros" | "intro" => {
        let xs : Array[String] = []
        while !self.at_stmt_end() {
          xs.push(if self.accept("_") { "_" } else { self.ident() })
        }
        TIntros(pos, xs)
      }
      "exact" => TExact(pos, self.expr())
      "rfl" => TRfl(pos)
      "destruct" | "cases" => TDestruct(pos, self.ident())
      "rewrite" | "rw" => {
        let rev = self.accept("<-")
        TRewrite(pos, self.expr(), rev)
      }
      "apply" => TApply(pos, self.expr())
      "unfold" => TUnfold(pos, self.unfold_names())
      "assume" | "have" => {
        let x = self.ident()
        self.expect(":")
        TAssume(pos, x, self.expr())
      }
      _ => raise ParseError(pos, "unknown tactic '" + name + "'")
    }
    ts.push(t)
    if !self.at("}") {
      self.end_stmt()
    }
  }
  self.expect("}")
  ts
}

// ---------------------------------------------------------------------------
// Declarations

///|
/// After `fn`: `[impl] name(params) -> ret raise E { body }`.
fn Parser::fn_rest(
  self : Parser,
  pos : Pos,
  is_lemma : Bool,
  is_async~ : Bool = false,
) -> FnDecl raise ParseError {
  let mut impl_bs = self.impl_binders()
  let mut name = self.ident()
  while self.accept("::") {
    name = name + "::" + self.ident()
  }
  if is_lemma && self.at("[") {
    impl_bs = impl_bs + self.impl_binders()
  }
  let params = if self.at("(") { Some(self.params(false)) } else { None }
  let ret = if self.accept("->") { Some(self.expr()) } else { None }
  let raises = self.effect_opt(is_async)
  let body = if self.accept("=") {
    match self.peek().tok {
      TStr([SPStr(s)]) => {
        ignore(self.advance())
        BodyExtern(s)
      }
      _ => BodyExpr(self.expr())
    }
  } else {
    BodyExpr(self.block())
  }
  { pos, name, impl_params: impl_bs, params, ret, raises, body, is_lemma, }
}

///|
fn Parser::con_decls(self : Parser) -> Array[ConDecl] raise ParseError {
  self.expect("{")
  let cs : Array[ConDecl] = []
  while !self.at("}") {
    if self.accept(";") {
      continue
    }
    let pos = self.pos()
    let name = self.ident()
    let impl_bs = self.impl_binders()
    let params = if self.is_same_line("(") { self.params(false) } else { [] }
    let ret = if self.accept(":") { Some(self.expr()) } else { None }
    cs.push({ pos, name, impl_params: impl_bs, params, ret, })
    if !self.at("}") {
      self.end_stmt()
    }
  }
  self.expect("}")
  cs
}

///|
fn Decl::without_pub(self : Decl) -> Decl {
  match self {
    DPub(d) | DDerive(_, d) | DLimit(_, _, d) | DUnfoldAttr(_, _, d) =>
      d.without_pub()
    d => d
  }
}

///|
/// `derive(A, B)` after a type declaration.
fn Parser::derives(self : Parser) -> Array[(Pos, String)] raise ParseError {
  let out : Array[(Pos, String)] = []
  if self.is_same_line("derive") {
    ignore(self.advance())
    self.expect("(")
    while !self.at(")") && self.peek().tok != TEOF {
      let p = self.pos()
      out.push((p, self.ident()))
      if !self.accept(",") {
        break
      }
    }
    self.expect(")")
  }
  out
}

///|
fn with_derives(d : Decl, ds : Array[(Pos, String)]) -> Decl {
  if ds.length() == 0 {
    d
  } else {
    DDerive(ds, d)
  }
}

///|
fn Parser::decl(self : Parser) -> Decl raise ParseError {
  let pos = self.pos()
  if self.accept("#") {
    let attr = self.ident()
    // `#timelimit(60)` or `#timelimit(none)`
    if attr == "timelimit" {
      self.expect("(")
      let lpos = self.pos()
      let limit = match self.advance().tok {
        TInt(n) if n > 0 => Some(n)
        TIdent("none") => None
        _ =>
          raise ParseError(
            lpos, "a time limit is a positive number of seconds or `none`",
          )
      }
      self.expect(")")
      return DLimit(pos, limit, self.decl())
    }
    // `#opaque`, `#opaque(sealed)`, `#unfold(f, g)`
    if attr == "opaque" || attr == "unfold" {
      let a : UnfoldAttr = if attr == "opaque" {
        if self.is_same_line("(") {
          ignore(self.advance())
          if self.ident() != "sealed" {
            raise ParseError(pos, "expected #opaque or #opaque(sealed)")
          }
          self.expect(")")
          Sealed
        } else {
          Opaque
        }
      } else {
        self.expect("(")
        let names = self.unfold_names()
        self.expect(")")
        Unfolds(names)
      }
      let d = self.decl()
      if !(d.inner() is (DFn(_) | DDef(_, _, _, _, _))) {
        raise ParseError(pos, "#" + attr + " applies to functions and lemmas")
      }
      return DUnfoldAttr(pos, a, d)
    }
    // `#mbt` or `#mbt("name")`
    if attr != "mbt" {
      self.fail(
        "unknown attribute (only #mbt, #timelimit, #opaque and #unfold are supported)",
      )
    }
    let name = if self.is_same_line("(") {
      ignore(self.advance())
      let n = match self.advance().tok {
        TStr([SPStr(s)]) => s
        _ => self.fail("expected the MoonBit name as a string")
      }
      self.expect(")")
      Some(n)
    } else {
      None
    }
    let d = self.decl()
    match d.without_pub() {
      DEnum({ is_error: false, .. })
      | DStruct(_)
      | DTrait(_)
      | DFn({ is_lemma: false, .. }) => ()
      _ =>
        raise ParseError(
          pos, "#mbt applies to enums, structs, traits and functions",
        )
    }
    return DMbt(pos, name, false, d)
  }
  if self.at("pub") {
    self.skip_visibility()
    return DPub(self.decl_body())
  }
  self.skip_visibility()
  self.decl_body()
}

///|
/// A declaration after its attributes and visibility.
fn Parser::decl_body(self : Parser) -> Decl raise ParseError {
  let pos = self.pos()
  if self.accept("fn") {
    return DFn(self.fn_rest(pos, false))
  }
  // `effect Name[T] { … }` (`effect` is not a keyword)
  if self.peek().tok == TIdent("effect") && self.peek_at(1).tok is TIdent(_) {
    ignore(self.advance())
    return DEffect(self.effect_rest(pos))
  }
  if self.at("async") && self.at_k(1, "fn") {
    ignore(self.advance())
    ignore(self.advance())
    return DFn(self.fn_rest(pos, false, is_async=true))
  }
  if self.accept("lemma") {
    // `lemma name[T](x : A) -> P { ... }` or `lemma name[T] : P = e`
    let impl_bs = self.impl_binders()
    let name = self.ident()
    let impl_bs = impl_bs + self.impl_binders()
    if self.accept(":") {
      let ty = self.expr()
      self.expect("=")
      return DDef(pos, name, impl_bs, Some(ty), self.expr())
    }
    let params = if self.at("(") { Some(self.params(false)) } else { None }
    let ret = if self.accept("->") { Some(self.expr()) } else { None }
    let body = if self.accept("=") { self.expr() } else { self.block() }
    return DFn({
      pos,
      name,
      impl_params: impl_bs,
      params,
      ret,
      raises: None,
      body: BodyExpr(body),
      is_lemma: true,
    })
  }
  if self.accept("let") || self.accept_ident("const") {
    let name = self.ident()
    let ty = if self.accept(":") { Some(self.expr()) } else { None }
    self.expect("=")
    return DDef(pos, name, [], ty, self.expr())
  }
  // `typealias T = U`, `typealias U as T`
  if self.accept_ident("typealias") {
    let first = self.expr()
    if self.accept("as") {
      let name = self.ident()
      return DDef(pos, name, [], Some(EType(pos)), first)
    }
    let (name, bs) = match first {
      EVar(_, n) => (n, [])
      EApp(_, EVar(_, n), Some(ps), None) => (n, exprs_to_impl_binders(ps))
      _ => self.fail("expected the name of the alias")
    }
    self.expect("=")
    return DDef(pos, name, bs, Some(EType(pos)), self.expr())
  }
  // `type T U`: a tuple struct with one field
  if self.peek().tok == TIdent("type") && self.peek_at(1).tok is TIdent(_) {
    ignore(self.advance())
    let name = self.ident()
    let impl_bs = self.impl_binders()
    let ty = self.expr()
    let ds = self.derives()
    return with_derives(
      DStruct({
        pos,
        name,
        impl_params: impl_bs,
        params: None,
        fields: [(pos, "0", ty)],
      }),
      ds,
    )
  }
  // `test "name" { .. }`: a function run by `moonpp test`
  if self.peek().tok == TIdent("test") {
    ignore(self.advance())
    let display = match self.peek().tok {
      TStr([SPStr(s)]) => {
        ignore(self.advance())
        s
      }
      _ => ""
    }
    test_counter.val = test_counter.val + 1
    let name = "__test_" + test_counter.val.to_string()
    test_names.set(name, display)
    return DFn({
      pos,
      name,
      impl_params: [],
      params: None,
      ret: Some(EVar(pos, "Unit")),
      raises: Some(EVar(pos, "Error")),
      body: BodyExpr(self.block()),
      is_lemma: false,
    })
  }
  if self.accept("enum") {
    let name = self.ident()
    let impl_bs = self.impl_binders()
    let params = if self.at("(") { Some(self.params(false)) } else { None }
    let sig = if self.accept(":") { Some(self.expr()) } else { None }
    let cons = self.con_decls()
    let ds = self.derives()
    return with_derives(
      DEnum({
        pos,
        name,
        impl_params: impl_bs,
        params,
        sig,
        cons,
        is_error: false,
      }),
      ds,
    )
  }
  if self.accept("suberror") {
    let name = self.ident()
    let cons = if self.at("{") {
      self.con_decls()
    } else if self.at_stmt_end() || self.is_same_line("derive") {
      [{ pos, name, impl_params: [], params: [], ret: None, }]
    } else {
      let ty = self.expr()
      [
        {
          pos,
          name,
          impl_params: [],
          params: [{ pos, name: "_", ty: Some(ty), kind: Positional, }],
          ret: None,
        },
      ]
    }
    self.skip_derive()
    return DEnum({
      pos,
      name,
      impl_params: [],
      params: None,
      sig: None,
      cons,
      is_error: true,
    })
  }
  if self.accept("struct") {
    let name = self.ident()
    let impl_bs = self.impl_binders()
    let params = if self.at("(") { Some(self.params(false)) } else { None }
    // `struct P(Int, Int)`: a tuple struct, with the fields `0`, `1`, ...
    if !self.at("{") {
      let fields : Array[(Pos, String, Expr)] = []
      let ps = params.unwrap_or([])
      for k = 0; k < ps.length(); k = k + 1 {
        let ty = match ps[k].ty {
          Some(t) => t
          None => EVar(ps[k].pos, ps[k].name)
        }
        fields.push((ps[k].pos, k.to_string(), ty))
      }
      let ds = self.derives()
      return with_derives(
        DStruct({ pos, name, impl_params: impl_bs, params: None, fields, }),
        ds,
      )
    }
    self.expect("{")
    let fields : Array[(Pos, String, Expr)] = []
    while !self.at("}") {
      if self.accept(";") {
        continue
      }
      // `mut x : T`: the type is marked `%Mut[T]`
      let is_mut = self.accept("mut")
      let fpos = self.pos()
      let f = self.ident()
      self.expect(":")
      let ty = self.expr()
      fields.push(
        (
          fpos,
          f,
          if is_mut {
            EApp(fpos, EVar(fpos, "%Mut"), Some([ty]), None)
          } else {
            ty
          },
        ),
      )
      if !self.at("}") {
        self.end_stmt()
      }
    }
    self.expect("}")
    let ds = self.derives()
    return with_derives(
      DStruct({ pos, name, impl_params: impl_bs, params, fields, }),
      ds,
    )
  }
  if self.accept("trait") {
    let name = self.ident()
    let self_kind = if self.accept("(") {
      let s = self.ident()
      if s != "Self" {
        self.fail("expected 'Self'")
      }
      self.expect(":")
      let k = self.expr()
      self.expect(")")
      Some(k)
    } else {
      None
    }
    let supers : Array[String] = []
    if self.accept(":") {
      supers.push(self.qual_ident())
      while self.accept("+") {
        supers.push(self.qual_ident())
      }
    }
    self.expect("{")
    let methods : Array[TraitMethod] = []
    while !self.at("}") {
      if self.accept(";") {
        continue
      }
      let mpos = self.pos()
      ignore(self.accept("fn"))
      let impl_bs = self.impl_binders()
      let m = self.ident()
      let ps = self.params(false)
      self.expect("->")
      let ret = self.pipe()
      let raises = self.effect_opt(false)
      if self.accept("=") {
        self.expect("_")
      }
      methods.push({
        pos: mpos,
        name: m,
        impl_params: impl_bs,
        params: ps,
        ret,
        raises,
      })
      if !self.at("}") {
        self.end_stmt()
      }
    }
    self.expect("}")
    return DTrait({ pos, name, self_kind, supers, methods, })
  }
  if self.accept("impl") {
    let impl_bs = self.impl_binders()
    let tr = self.qual_ident()
    // `impl Tr with m(..) { }`: the default of a method (for `%Default`)
    let ty = if self.at("with") {
      EVar(pos, "%Default")
    } else {
      self.expect("for")
      self.expr()
    }
    // `impl Tr for T`: all methods are the defaults
    if !self.at("with") {
      return DImpl({
        pos,
        impl_params: impl_bs,
        trait_name: tr,
        for_ty: ty,
        meth: "",
        params: [],
        body: EVar(pos, "_"),
      })
    }
    self.expect("with")
    let m = self.ident()
    let ps = self.params(true)
    if self.accept("->") {
      ignore(self.pipe())
    }
    ignore(self.raises_opt())
    let body = self.block()
    return DImpl({
      pos,
      impl_params: impl_bs,
      trait_name: tr,
      for_ty: ty,
      meth: m,
      params: ps,
      body,
    })
  }
  self.fail("expected a declaration")
}

///|
pub fn parse_program(
  src : String,
  line0~ : Int32 = 1,
) -> Array[Decl] raise ParseError {
  let p = { toks: tokenize(src, line0~), i: 0, }
  let ds : Array[Decl] = []
  while p.peek().tok != TEOF {
    if p.accept(";") {
      continue
    }
    ds.push(p.decl())
  }
  ds
}

///|
pub fn parse_expr(src : String) -> Expr raise ParseError {
  let p = { toks: tokenize(src), i: 0, }
  let e = p.expr()
  if p.peek().tok != TEOF {
    p.fail("unexpected token")
  }
  e
}

///|
/// The package alias after `@`: a keyword is a valid alias (`@async`).
fn Parser::pkg_name(self : Parser) -> String raise ParseError {
  match self.peek().tok {
    TSym(s) if s.length() > 0 && s.get_char(0).unwrap().is_ascii_alphabetic() => {
      ignore(self.advance())
      s
    }
    _ => self.ident()
  }
}

///|
/// The guard of a match arm, up to the arm's `=>` (so that `x if a == b =>`
/// is not read as the lambda `b => ...`).
fn Parser::guard_expr(self : Parser) -> Expr raise ParseError {
  let mut k = self.i
  let mut depth = 0
  while k < self.toks.length() {
    match self.toks[k].tok {
      TSym("(" | "[" | "{") => depth = depth + 1
      TSym(")" | "]" | "}") => depth = depth - 1
      TSym("=>") if depth == 0 => break
      TEOF => break
      _ => ()
    }
    k = k + 1
  }
  let sub : Parser = {
    toks: [
      ..self.toks[self.i:k].to_owned(),
      { tok: TEOF, pos: self.toks[k].pos, nl: true, },
    ],
    i: 0,
  }
  let e = sub.expr()
  if sub.peek().tok != TEOF {
    sub.fail("unexpected token in a guard")
  }
  self.i = k
  e
}

///|
/// The names of the `test` blocks: the function -> the test's name.
pub let test_names : Map[String, String] = Map([])

///|
let test_counter : Ref[Int32] = Ref(0)

///|
/// Accept an identifier that is not a keyword of MoonBit++ (`const`).
fn Parser::accept_ident(self : Parser, s : String) -> Bool {
  if self.peek().tok == TIdent(s) {
    ignore(self.advance())
    true
  } else {
    false
  }
}

///|
/// `{ "a": 1, ... }`: a literal key and `:`.
fn Parser::is_map_literal(self : Parser) -> Bool {
  self.at("{") &&
  (match self.peek_at(1).tok {
    TStr(_) | TInt(_) | TChar(_) | TLit(_) | TDouble(_) => true
    TSym("true" | "false" | "-") => true
    _ => false
  }) &&
  (self.at_k(2, ":") || self.at_k(3, ":"))
}

///|
/// `{ k: v, ... }`: `Map::from_array([(k, v), ...])`.
fn Parser::map_literal(self : Parser) -> Expr raise ParseError {
  let pos = self.pos()
  self.expect("{")
  let pairs : Array[Expr] = []
  while !self.at("}") {
    let kpos = self.pos()
    let k = self.unary()
    self.expect(":")
    let v = self.expr()
    pairs.push(ETuple(kpos, [k, v]))
    if !self.accept(",") {
      break
    }
  }
  self.expect("}")
  EApp(pos, EVar(pos, "Map::from_array"), None, Some([EArray(pos, pairs)]))
}

///|
/// An expression, or an assignment (`x = e`, `a[i] += e`) as the body of an
/// arm.
fn Parser::expr_or_assign(self : Parser) -> Expr raise ParseError {
  let pos = self.pos()
  let e = self.expr()
  for op in ["=", "+=", "-=", "*=", "/="] {
    if self.at(op) {
      ignore(self.advance())
      return EBlock(pos, [SAssign(pos, e, op, self.expr())])
    }
  }
  e
}

///|
/// `effect Name[params] { Op(params) -> ret; ctl Op(params) -> ret }`, after
/// `effect`.
fn Parser::effect_rest(self : Parser, pos : Pos) -> EffectDecl raise ParseError {
  let name = self.ident()
  let params = self.impl_binders()
  self.expect("{")
  let ops : Array[EffOpDecl] = []
  while !self.at("}") {
    if self.accept(";") {
      continue
    }
    let opos = self.pos()
    let ctl = self.peek().tok == TIdent("ctl") &&
      self.peek_at(1).tok is TIdent(_)
    if ctl {
      ignore(self.advance())
    }
    let op = self.ident()
    let ps = if self.at("(") { self.params(false) } else { [] }
    let ret = if self.accept("->") { self.pipe() } else { EVar(opos, "Unit") }
    ops.push({ pos: opos, name: op, params: ps, ret, ctl, })
    if !self.at("}") {
      self.end_stmt()
    }
  }
  self.expect("}")
  { pos, name, params, ops, }
}

///|
/// The names of `#unfold(…)`, `unfold(…) { e }` and the `unfold` tactic:
/// `f, g, T::m`.
fn Parser::unfold_names(self : Parser) -> Array[(Pos, String)] raise ParseError {
  let names : Array[(Pos, String)] = []
  while true {
    let p = self.pos()
    let mut name = self.ident()
    while self.accept("::") {
      name = name + "::" + self.ident()
    }
    names.push((p, name))
    if !self.accept(",") {
      break
    }
  }
  names
}

///|
/// At `unfold(f, g) {`?
fn Parser::at_unfold_block(self : Parser) -> Bool {
  if in_condition.val || !self.at_k(1, "(") {
    return false
  }
  let mut k = 2
  while true {
    match self.peek_at(k).tok {
      TIdent(_) | TSym("::") | TSym(",") => k = k + 1
      TSym(")") => return self.at_k(k + 1, "{") && !self.peek_at(k + 1).nl
      _ => return false
    }
  }
  false
}

///|
/// Parsing a condition (`if c {`, `match e {`, ...), where `unfold(f) {` is
/// a call followed by the block of the `if`.
let in_condition : Ref[Bool] = Ref(false)

///|
fn Parser::cond_expr(self : Parser) -> Expr raise ParseError {
  let saved = in_condition.val
  in_condition.val = true
  errdefer { in_condition.val = saved }
  let r = self.expr()
  in_condition.val = saved
  r
}
