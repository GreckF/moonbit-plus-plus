///|
/// Time limits: the checking of each declaration (its signature, and its
/// body) may take `default_time_limit` seconds, or what `#timelimit(n)` says
/// (`#timelimit(none)`: no limit). The time spent checking other
/// declarations on the way does not count. When the limit is exceeded,
/// evaluation stops (`eval` returns stuck values from then on, so that the
/// checker gets out of a loop quickly) and the declaration fails.

///|
/// The default limit, in seconds.
pub let default_time_limit : Ref[Int32] = Ref(30)

///|
/// `#timelimit` of declarations, by global name (`None`: no limit).
let time_limits : Map[String, Int32?] = Map([])

///|
priv struct TimeFrame {
  name : String
  limit : Int32?
  /// When the declaration fails, in ms since the epoch (moved forward by the
  /// time spent on nested declarations).
  mut deadline : UInt64
}

///|
let time_frames : Array[TimeFrame] = []

///|
/// The declaration whose time ran out, and the function being evaluated
/// then.
let timed_out : Ref[(String, String?)?] = Ref(None)

///|
let ticks : Ref[Int32] = Ref(0)

///|
/// The global function last unfolded or executed (for the message).
let last_unfolded : Ref[String?] = Ref(None)

///|
fn reset_time_limits() -> Unit {
  time_limits.clear()
  time_frames.clear()
  timed_out.val = None
  ticks.val = 0
  last_unfolded.val = None
}

///|
/// Called often by evaluation: has the time of the current declaration run
/// out?
fn time_up() -> Bool {
  if timed_out.val is Some(_) {
    return true
  }
  ticks.val = ticks.val + 1
  if ticks.val % 4096 != 0 {
    return false
  }
  match time_frames.last() {
    Some({ limit: Some(_), deadline, name, }) if @env.now() > deadline => {
      timed_out.val = Some((name, last_unfolded.val))
      true
    }
    _ => false
  }
}

///|
/// Check a declaration (`th`) within its time limit.
fn with_time_limit(
  name : String,
  th : () -> Unit raise ElabError,
) -> Unit raise ElabError {
  // the signature and the body are checked separately; nested checks of
  // the same declaration share its frame
  if time_frames.last() is Some(f) && f.name == name {
    return th()
  }
  (checking_hook.val)(name)
  let limit = match time_limits.get(name) {
    Some(l) => l
    None => Some(default_time_limit.val)
  }
  let start = @env.now()
  let deadline = match limit {
    Some(s) => start + s.to_uint64() * 1000
    None => 0
  }
  time_frames.push({ name, limit, deadline, })
  let res : Result[Unit, ElabError] = try {
    th()
    Ok(())
  } catch {
    ElabError(p, m) => Err(ElabError(p, m))
  }
  ignore(time_frames.pop())
  // the outer declarations do not pay for this one
  let spent = @env.now() - start
  for f in time_frames {
    f.deadline = f.deadline + spent
  }
  match timed_out.val {
    Some((n, during)) if n == name => {
      timed_out.val = None
      let secs = limit.unwrap_or(0).to_string()
      raise ElabError(
        decl_pos.get(name).unwrap_or({ line: 0, col: 0, }),
        "checking " +
        name +
        " took more than " +
        secs +
        " s" +
        (match during {
          Some(f) => " (while evaluating " + f + ")"
          None => ""
        }) +
        "; a definition that does not terminate? Raise the limit with #timelimit(seconds) or #timelimit(none)",
      )
    }
    _ => ()
  }
  match res {
    Ok(_) => ()
    Err(e) => raise e
  }
}

///|
/// Record and remove the `#timelimit` attributes of a declaration.
fn strip_limits(d : @parser.Decl) -> @parser.Decl {
  match d {
    DLimit(_, limit, inner) => {
      for n in limit_names(inner.inner()) {
        time_limits.set(n, limit)
      }
      strip_limits(inner)
    }
    DMbt(p, n, ro, x) => DMbt(p, n, ro, strip_limits(x))
    DPub(x) => DPub(strip_limits(x))
    DDerive(ds, x) => DDerive(ds, strip_limits(x))
    DUnfoldAttr(p, a, x) => DUnfoldAttr(p, a, strip_limits(x))
    _ => d
  }
}

///|
/// The names under which a declaration is checked.
fn limit_names(d : @parser.Decl) -> Array[String] {
  match d {
    DFn(fd) => [fd.name]
    DDef(_, n, _, _, _) | DOpaque(_, n, _) => [n]
    DEnum(ed) => [ed.name, ..ed.cons.map(c => ed.name + "::" + c.name)]
    DStruct(sd) => [sd.name, sd.name + "::mk"]
    DTrait(td) => [td.name, td.name + "::mk"]
    DImpl(id) => ["impl$" + id.trait_name + "$" + impl_head(id.for_ty)]
    _ => []
  }
}

///|
/// Called with the name of each definition when its checking starts (the
/// JS build of moonpp names it when the checker runs out of stack).
pub let checking_hook : Ref[(String) -> Unit] = Ref(_ => ())
