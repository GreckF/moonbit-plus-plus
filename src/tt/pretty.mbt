///|
/// Pretty printing of core terms in MoonBit++ syntax.
fn short_name(n : String) -> String {
  match con_info(n) {
    Some(_) =>
      match n.rev_find("::") {
        Some(i) => n.unsafe_substring(start=i + 2, end=n.length())
        None => n
      }
    None => n
  }
}

///|
fn fresh_name(names : Array[String], x : String) -> String {
  if x == "_" || !names.contains(x) {
    x
  } else {
    let mut k = 1
    while names.contains(x + k.to_string()) {
      k = k + 1
    }
    x + k.to_string()
  }
}

///|
fn flatten_app(t : Tm) -> (Tm, Array[(Tm, Icit)]) {
  let args : Array[(Tm, Icit)] = []
  let mut h = t
  while h is App(f, a, i) {
    args.push((a, i))
    h = f
  }
  args.rev_in_place()
  (h, args)
}

///|
/// The number `S(…S(Z))` denotes.
pub fn nat_lit(t : Tm) -> Int32? {
  let mut n = 0
  let mut cur = t
  while true {
    match cur {
      Global("Nat::Z") => return Some(n)
      // a large literal (see `nat_tm`)
      App(Global("int_to_nat"), Lit(LInt(k)), Expl) if k >= 0 =>
        return Some(n + k)
      App(Global("Nat::S"), a, Expl) => {
        n = n + 1
        cur = a
      }
      _ => return None
    }
  }
  None
}

///|
fn show_lit(l : Lit) -> String {
  match l {
    LInt(n) => n.to_string()
    LStr(s) => s.escape()
    LChar(c) => c.to_string().escape()
    LBool(b) => b.to_string()
    LDouble(d) => d.to_string()
    LInt64(n) => n.to_string() + "L"
    LUInt(n) => n.to_string() + "U"
    LUInt64(n) => n.to_string() + "UL"
    LByte(b) => b.to_string()
    LFloat(f) => f.to_string() + "F"
    LUnit => "()"
  }
}

///|
fn show_pat(names : Array[String], p : CPat) -> (String, Array[String]) {
  // Returns the printed pattern and the names it binds (in slot order).
  match p {
    CPVar(x) => {
      let y = fresh_name(names, x)
      (y, [y])
    }
    CPWild => ("_", ["_"])
    CPLit(l) => (show_lit(l), ["_"])
    CPCon(c, ps) => {
      let bound = ["_"]
      let shown : Array[String] = []
      let mut ns = names
      for q in ps {
        let (s, bs) = show_pat(ns, q)
        shown.push(s)
        for b in bs {
          bound.push(b)
        }
        ns = concat(ns, bs)
      }
      let s = if ps.length() == 0 {
        short_name(c)
      } else {
        short_name(c) + "(" + shown.join(", ") + ")"
      }
      (s, bound)
    }
  }
}

///|
fn op_symbol(n : String) -> String? {
  let m = match n.rev_find("::") {
    Some(i) => n.unsafe_substring(start=i + 2, end=n.length())
    None => return None
  }
  match m {
    "op_add" => Some("+")
    "op_sub" => Some("-")
    "op_mul" => Some("*")
    "op_div" => Some("/")
    "op_mod" => Some("%")
    "op_equal" => Some("==")
    "op_lt" => Some("<")
    "op_le" => Some("<=")
    "op_gt" => Some(">")
    "op_ge" => Some(">=")
    _ => None
  }
}

///|
pub fn show_tm(names : Array[String], t : Tm) -> String {
  show_prec(names, t, 0)
}

///|
fn paren(b : Bool, s : String) -> String {
  if b {
    "(" + s + ")"
  } else {
    s
  }
}

///|
fn show_prec(names : Array[String], t : Tm, prec : Int32) -> String {
  match t {
    Var(ix) => {
      let i = names.length() - 1 - ix
      if i >= 0 && i < names.length() {
        names[i]
      } else {
        "#" + ix.to_string()
      }
    }
    Global("Nat::Z") => "0"
    Global(n) => short_name(n)
    Meta(m) => "?" + m.to_string()
    InsertedMeta(m, _) => "?" + m.to_string()
    U => "Type"
    PropU => "Prop"
    Lit(l) => show_lit(l)
    App(_, _, _) => {
      match nat_lit(t) {
        Some(n) => return n.to_string()
        None => ()
      }
      let (h, args) = flatten_app(t)
      match (h, args) {
        (Global("%raise"), [(e, _)]) =>
          return paren(prec > 1, "raise " + show_prec(names, e, 2))
        // a delayed application (see raise.mbt)
        (Global("%app"), [(f, _), (a, i), .. rest]) =>
          return show_prec(
            names,
            rest.fold(init=App(f, a, i), (g, x) => App(g, x.0, x.1)),
            prec,
          )
        (Global("Id"), [_, (a, Expl), (b, Expl)]) =>
          return paren(
            prec > 1,
            show_prec(names, a, 2) + " === " + show_prec(names, b, 2),
          )
        // `code { e }` and `${ c }` (see staging.mbt)
        (Global("%quote"), [_, (s, _), (Lam(x, _, _, _) as f, _)]) =>
          return "code " + show_block(push1(names, x), quoted_body(s, f))
        (Global("%splice"), [_, (c, _), _, _, .. rest]) => {
          let code = match c {
            Var(_) => "$" + show_prec(names, c, 3)
            _ => "${ " + show_prec(names, c, 0) + " }"
          }
          if rest.length() == 0 {
            return code
          }
          return code +
            "(" +
            rest.map(a => show_prec(names, a.0, 0)).join(", ") +
            ")"
        }
        _ => ()
      }
      let hide_impl = match h {
        Global(n) => !(data_info(n) is Some(_))
        _ => false
      }
      let impls : Array[String] = []
      let expls : Array[String] = []
      for a in args {
        match a.1 {
          Expl => expls.push(show_prec(names, a.0, 0))
          _ => if !hide_impl { impls.push(show_prec(names, a.0, 0)) }
        }
      }
      // tuples and tuple types: `(a, b)`, `(Int, String)`
      match h {
        Global(n) if n.has_prefix("Tuple") && n.has_suffix("::mk") =>
          return "(" + expls.join(", ") + ")"
        Global(n) if n.has_prefix("Tuple") &&
          data_info(n) is Some(_) &&
          expls.length() == 0 => return "(" + impls.join(", ") + ")"
        _ => ()
      }
      // `T::op_add(a, b)` is shown as `a + b`
      match (h, expls.length()) {
        (Global(n), 2) =>
          match op_symbol(n) {
            Some(op) => {
              let ex = args.filter(a => a.1 == Expl)
              return paren(
                prec > 1,
                show_prec(names, ex[0].0, 2) +
                " " +
                op +
                " " +
                show_prec(names, ex[1].0, 2),
              )
            }
            None => ()
          }
        _ => ()
      }
      let mut s = show_prec(names, h, 3)
      if impls.length() > 0 {
        s = s + "[" + impls.join(", ") + "]"
      }
      if expls.length() > 0 {
        s = s + "(" + expls.join(", ") + ")"
      }
      s
    }
    Pi(_, _, _, _, _) => {
      let mut ns = names
      let mut cur = t
      let impls : Array[String] = []
      let expls : Array[String] = []
      // implicit binders followed by one explicit group
      while cur is Pi(x, i, g, a, b) {
        if i != Expl && expls.length() > 0 {
          break
        }
        if i == Expl && g && expls.length() > 0 {
          break
        }
        let y = fresh_name(ns, x)
        let ann = if y == "_" {
          show_prec(ns, a, 0)
        } else {
          y + " : " + show_prec(ns, a, 0)
        }
        match i {
          Expl => expls.push(ann)
          // the capability of an effect is in the codomain's row
          _ if x.has_prefix("%cap:") => ()
          _ => impls.push(ann)
        }
        ns = push1(ns, y)
        cur = b
      }
      let mut s = ""
      if impls.length() > 0 {
        s = "[" + impls.join(", ") + "]"
      }
      if expls.length() > 0 {
        s = s + "(" + expls.join(", ") + ")"
      }
      // `async (A) -> B raise E` (the effect is in the codomain)
      let (pre, cod) = match cur {
        Raises(r, App(Global("%Async"), Global("%NoRaise"), _)) =>
          ("async ", show_prec(ns, r, 1) + " noraise")
        Raises(r, App(Global("%Async"), Global("Error"), _)) =>
          ("async ", show_prec(ns, r, 1))
        Raises(r, App(Global("%Async"), e, _)) =>
          ("async ", show_prec(ns, r, 1) + " raise " + show_prec(ns, e, 1))
        Raises(_, App(App(Global("%Effs"), _, _), _, _)) =>
          ("", show_prec(ns, cur, 1))
        _ => ("", show_prec(ns, cur, 0))
      }
      paren(prec > 0, pre + s + " -> " + cod)
    }
    Lam(_, _, _, _) => {
      let mut ns = names
      let mut cur = t
      let xs : Array[String] = []
      while cur is Lam(x, i, _, b) {
        let y = fresh_name(ns, x)
        xs.push(if i == Expl { y } else { "[" + y + "]" })
        ns = push1(ns, y)
        cur = b
      }
      paren(prec > 0, "(" + xs.join(", ") + ") => " + show_prec(ns, cur, 0))
    }
    Let(_, _, _, _) | LetMut(_, _, _, _) | Seq(_, _) | Defer(_, _) =>
      show_block(names, t)
    Match(scr, cls) => {
      let arms = cls.map(cl => {
        let mut ns = names
        let ps : Array[String] = []
        for p in cl.pats {
          let (s, bs) = show_pat(ns, p)
          ps.push(s)
          ns = concat(ns, bs)
        }
        let lhs = if ps.length() == 1 {
          ps[0]
        } else {
          "(" + ps.join(", ") + ")"
        }
        lhs + " => " + show_prec(ns, cl.body, 0)
      })
      let s = if scr.length() == 1 {
        show_prec(names, scr[0], 3)
      } else {
        "(" + scr.map(x => show_prec(names, x, 0)).join(", ") + ")"
      }
      "match " + s + " { " + arms.join("; ") + " }"
    }
    // `T!E1 + e raise Err` (see effects.mbt)
    Raises(a, App(App(Global("%Effs"), row, _), err, _)) => {
      let items : Array[String] = []
      let mut r = row
      while r is App(App(Global("%Row"), item, _), rest, _) {
        items.push(show_prec(names, item, 2))
        r = rest
      }
      // an effect variable; an unknown row (a meta) is not shown
      match flatten_app(r).0 {
        Global("%RowNil") | Meta(_) | InsertedMeta(_, _) => ()
        _ => items.push(show_prec(names, r, 2))
      }
      let effs = if items.length() == 0 { "" } else { "!" + items.join(" + ") }
      let errs = if err is Global("%NoRaise") {
        ""
      } else {
        " raise " + show_prec(names, err, 1)
      }
      show_prec(names, a, 2) + effs + errs
    }
    Raises(a, e) => show_prec(names, a, 1) + " raise " + show_prec(names, e, 1)
    ArrayLit(es) => "[" + es.map(x => show_prec(names, x, 0)).join(", ") + "]"
    Assign(ix, v) =>
      show_prec(names, Var(ix), 3) + " = " + show_prec(names, v, 0)
    While(c, b, s) => {
      let items : Array[String] = []
      block_items(names, b, items)
      if !(s is Lit(LUnit)) {
        block_items(names, s, items)
      }
      "while " + show_prec(names, c, 0) + " { " + items.join("; ") + " }"
    }
    Break => "break"
    Continue => "continue"
    Return(v) => paren(prec > 1, "return " + show_prec(names, v, 0))
    Raise(v) => paren(prec > 1, "raise " + show_prec(names, v, 2))
    Try(b, cls) => {
      let arms = cls.map(cl => {
        let mut ns = names
        let ps : Array[String] = []
        for p in cl.pats {
          let (s, bs) = show_pat(ns, p)
          ps.push(s)
          ns = concat(ns, bs)
        }
        ps.join(", ") + " => " + show_prec(ns, cl.body, 0)
      })
      paren(
        prec > 0,
        "try " + show_block(names, b) + " catch { " + arms.join("; ") + " }",
      )
    }
  }
}

///|
/// `t` as a block `{ a; b; c }`.
fn show_block(names : Array[String], t : Tm) -> String {
  let items : Array[String] = []
  block_items(names, t, items)
  "{ " + items.join("; ") + " }"
}

///|
/// The statements of `t` (`let`s and sequences), then its value.
fn block_items(names : Array[String], t : Tm, out : Array[String]) -> Unit {
  match t {
    Let(x, _, v, b) => {
      let y = fresh_name(names, x)
      out.push("let " + y + " = " + show_prec(names, v, 0))
      block_items(push1(names, y), b, out)
    }
    LetMut(x, _, v, b) => {
      let y = fresh_name(names, x)
      out.push("let mut " + y + " = " + show_prec(names, v, 0))
      block_items(push1(names, y), b, out)
    }
    Seq(a, b) => {
      block_items(names, a, out)
      block_items(names, b, out)
    }
    Defer(d, b) => {
      out.push("defer " + show_prec(names, d, 0))
      block_items(names, b, out)
    }
    _ => out.push(show_prec(names, t, 0))
  }
}
