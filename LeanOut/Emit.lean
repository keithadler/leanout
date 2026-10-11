/-
Copyright 2026 Keith Adler
Licensed under the Apache License, Version 2.0 (see LICENSE).

Clean-room exporter: written from the published NDJSON format description (3.1.0) only.
-/
import Lean
open Lean

namespace LeanOut

structure St where
  names   : Std.HashMap Name Nat := {}
  levels  : Std.HashMap Level Nat := {}
  exprs   : Std.HashMap Expr Nat := {}
  done    : Std.HashSet Name := {}
  skipped : Std.HashSet Name := {}
  allowUnsafe : Bool := false
  counts  : Std.HashMap String Nat := {}
  axioms  : Array Name := #[]
  nName   : Nat := 1   -- id 0 is the anonymous name
  nLevel  : Nat := 1   -- id 0 is level zero
  nExpr   : Nat := 0

abbrev M := StateRefT St (ReaderT (Environment × IO.FS.Stream) IO)

def out (j : Json) : M Unit := do
  let (_, h) ← read
  h.putStr (j.compress ++ "\n")

def binfo : BinderInfo → String
  | .default => "default" | .implicit => "implicit"
  | .strictImplicit => "strictImplicit" | .instImplicit => "instImplicit"

/-- Metadata payload as a JSON object. Syntax values are exported as their printed form. -/
def dataJson (d : MData) : Json :=
  Json.mkObj <| d.entries.filterMap fun (k, v) =>
    match v with
    | .ofString s => some (k.toString, Json.str s)
    | .ofBool b => some (k.toString, Json.bool b)
    | .ofName n => some (k.toString, Json.str n.toString)
    | .ofNat n => some (k.toString, (n : Json))
    | .ofInt i => some (k.toString, (i : Json))
    | .ofSyntax stx => some (k.toString, Json.str (toString stx))

partial def nameId (n : Name) : M Nat := do
  if n.isAnonymous then return 0
  if let some i := (← get).names[n]? then return i
  match n with
  | .anonymous => return 0
  | .str p s =>
    let pi ← nameId p
    let i := (← get).nName
    modify fun st => { st with names := st.names.insert n i, nName := i + 1 }
    out <| Json.mkObj [("str", Json.mkObj [("pre", pi), ("str", s)]), ("in", i)]
    return i
  | .num p k =>
    let pi ← nameId p
    let i := (← get).nName
    modify fun st => { st with names := st.names.insert n i, nName := i + 1 }
    out <| Json.mkObj [("num", Json.mkObj [("pre", pi), ("i", k)]), ("in", i)]
    return i

partial def levelId (l : Level) : M Nat := do
  if let .zero := l then return 0
  if let some i := (← get).levels[l]? then return i
  let body : String × Json ← match l with
    | .zero => pure ("zero", Json.null)
    | .succ a => pure ("succ", (← levelId a : Nat))
    | .max a b => pure ("max", Json.arr #[(← levelId a : Nat), (← levelId b : Nat)])
    | .imax a b => pure ("imax", Json.arr #[(← levelId a : Nat), (← levelId b : Nat)])
    | .param n => pure ("param", (← nameId n : Nat))
    | .mvar _ => throw <| IO.userError "level metavariable in environment"
  let i := (← get).nLevel
  modify fun st => { st with levels := st.levels.insert l i, nLevel := i + 1 }
  out <| Json.mkObj [(body.1, body.2), ("il", i)]
  return i

def idxs (xs : List Nat) : Json := Json.arr (xs.toArray.map fun (n : Nat) => (n : Json))

partial def exprId (e : Expr) : M Nat := do
  if let some i := (← get).exprs[e]? then return i
  let body : String × Json ← match e with
    | .bvar k => pure ("bvar", k)
    | .sort l => pure ("sort", (← levelId l : Nat))
    | .const n us =>
      let ni ← nameId n
      let ui ← us.mapM levelId
      pure ("const", Json.mkObj [("name", ni), ("us", idxs ui)])
    | .app f a =>
      let fi ← exprId f
      let ai ← exprId a
      pure ("app", Json.mkObj [("fn", fi), ("arg", ai)])
    | .lam n t b bi =>
      let ni ← nameId n
      let ti ← exprId t
      let bo ← exprId b
      pure ("lam", Json.mkObj [("name", ni), ("type", ti), ("body", bo), ("binderInfo", binfo bi)])
    | .forallE n t b bi =>
      let ni ← nameId n
      let ti ← exprId t
      let bo ← exprId b
      pure ("forallE", Json.mkObj [("name", ni), ("type", ti), ("body", bo), ("binderInfo", binfo bi)])
    | .letE n t v b nd =>
      let ni ← nameId n
      let ti ← exprId t
      let vi ← exprId v
      let bo ← exprId b
      pure ("letE", Json.mkObj [("name", ni), ("type", ti), ("value", vi), ("body", bo), ("nondep", nd)])
    | .proj s k x =>
      let si ← nameId s
      let xi ← exprId x
      pure ("proj", Json.mkObj [("typeName", si), ("idx", k), ("struct", xi)])
    | .lit (.natVal v) => pure ("natVal", toString v)
    | .lit (.strVal s) => pure ("strVal", s)
    | .mdata d x =>
      let xi ← exprId x
      pure ("mdata", Json.mkObj [("expr", xi), ("data", dataJson d)])
    | .fvar _ | .mvar _ => throw <| IO.userError "free variable or metavariable in environment"
  let i := (← get).nExpr
  modify fun st => { st with exprs := st.exprs.insert e i, nExpr := i + 1 }
  out <| Json.mkObj [(body.1, body.2), ("ie", i)]
  return i

def nameIds (ns : List Name) : M Json := do
  return idxs (← ns.mapM nameId)

def hintsJson : ReducibilityHints → M Json
  | .opaque => pure "opaque"
  | .abbrev => pure "abbrev"
  | .regular h => pure <| Json.mkObj [("regular", h.toNat)]

def safetyStr : DefinitionSafety → String
  | .unsafe => "unsafe" | .safe => "safe" | .partial => "partial"

/-- Literals implicitly mean constants: a checker expanding a numeric or string literal needs
these already declared, although they never appear in the term. -/
def literalRefs (e : Expr) : Array Name :=
  let nat := (e.find? fun x => match x with | .lit (.natVal _) => true | _ => false).isSome
  let str := (e.find? fun x => match x with | .lit (.strVal _) => true | _ => false).isSome
  (if nat || str then #[``Nat, ``Nat.zero, ``Nat.succ] else #[]) ++
  (if str then #[``String, ``String.ofList, ``Char, ``Char.ofNat, ``List, ``List.nil, ``List.cons] else #[])

/-- Constants a constant refers to (in its type and, where present, its value). -/
def refsOf (ci : ConstantInfo) : Array Name :=
  let es := match ci.value? (allowOpaque := true) with | some v => #[ci.type, v] | none => #[ci.type]
  es.foldl (fun acc e => acc ++ e.getUsedConstants ++ literalRefs e) #[]

/-- Constants a kernel checker cannot take on trust-free terms: unsafe/partial code and the
`_unsafe_rec` compilation helpers. They are skipped (with everything that refers to them)
unless `allowUnsafe` is set. -/
def isUnsafeLike (ci : ConstantInfo) : Bool :=
  (match ci.name with | .str _ "_unsafe_rec" => true | _ => false) ||
  match ci with
  | .defnInfo v => v.safety != .safe
  | .axiomInfo v => v.isUnsafe
  | .opaqueInfo v => v.isUnsafe
  | .inductInfo v => v.isUnsafe
  | .ctorInfo v => v.isUnsafe
  | .recInfo v => v.isUnsafe
  | _ => false

def kindOf : ConstantInfo → String
  | .axiomInfo _ => "axiom" | .defnInfo _ => "def" | .thmInfo _ => "thm" | .opaqueInfo _ => "opaque"
  | .quotInfo _ => "quot" | _ => "inductive-block-member"

/-- Emit a constant (and its inductive/quotient group) after everything it depends on. -/
partial def emit (n : Name) : M Bool := do
  if (← get).done.contains n then return !(← get).skipped.contains n
  let (env, _) ← read
  let some ci := env.find? n | return false
  -- the unit emitted together: for inductive-ish things, the whole mutual group
  let group : List Name := match ci with
    | .inductInfo v => v.all
    | .ctorInfo v => (match env.find? v.induct with | some (.inductInfo i) => i.all | _ => [n])
    | .recInfo v => (match v.all with | a :: _ => (match env.find? a with | some (.inductInfo i) => i.all | _ => [n]) | [] => [n])
    | _ => [n]
  let members : List Name := match ci with
    | .quotInfo _ => [``Quot, ``Quot.mk, ``Quot.lift, ``Quot.ind]
    | .inductInfo _ | .ctorInfo _ | .recInfo _ =>
      group.flatMap fun t =>
        match env.find? t with
        | some (.inductInfo v) =>
          [t] ++ v.ctors ++ [mkRecName t] ++
            (if t == group.head! then (List.range v.numNested).map fun i => t ++ Name.mkSimple s!"rec_{i+1}" else [])
        | _ => [t]
    | _ => [n]
  modify fun st => { st with done := members.foldl (·.insert ·) st.done }
  let ext := members.filterMap env.find?
  -- dependencies first; if any is unavailable, this whole unit is unavailable
  let mut ok := (← get).allowUnsafe || !ext.any isUnsafeLike
  for c in ext do
    for r in refsOf c do
      if !members.contains r then
        if !(← emit r) then ok := false
  if !ok then
    modify fun st => { st with skipped := members.foldl (·.insert ·) st.skipped }
    return false
  modify fun st => { st with counts := st.counts.insert (kindOf ci) (st.counts.getD (kindOf ci) 0 + ext.length) }
  match ci with
  | .axiomInfo v =>
    modify fun st => { st with axioms := st.axioms.push v.name }
    out <| Json.mkObj [("axiom", Json.mkObj [("name", (← nameId v.name)), ("levelParams", (← nameIds v.levelParams)),
      ("type", (← exprId v.type)), ("isUnsafe", v.isUnsafe)])]
  | .defnInfo v =>
    out <| Json.mkObj [("def", Json.mkObj [("name", (← nameId v.name)), ("levelParams", (← nameIds v.levelParams)),
      ("type", (← exprId v.type)), ("value", (← exprId v.value)), ("hints", (← hintsJson v.hints)),
      ("safety", safetyStr v.safety), ("all", (← nameIds v.all))])]
  | .thmInfo v =>
    out <| Json.mkObj [("thm", Json.mkObj [("name", (← nameId v.name)), ("levelParams", (← nameIds v.levelParams)),
      ("type", (← exprId v.type)), ("value", (← exprId v.value)), ("all", (← nameIds v.all))])]
  | .opaqueInfo v =>
    out <| Json.mkObj [("opaque", Json.mkObj [("name", (← nameId v.name)), ("levelParams", (← nameIds v.levelParams)),
      ("type", (← exprId v.type)), ("value", (← exprId v.value)), ("isUnsafe", v.isUnsafe), ("all", (← nameIds v.all))])]
  | .quotInfo _ =>
    for q in ext do
      match q with
      | .quotInfo v =>
        let kind := match v.kind with | .type => "type" | .ctor => "ctor" | .lift => "lift" | .ind => "ind"
        out <| Json.mkObj [("quot", Json.mkObj [("name", (← nameId v.name)), ("levelParams", (← nameIds v.levelParams)),
          ("type", (← exprId v.type)), ("kind", kind)])]
      | _ => pure ()
  | _ =>
    let mut types : Array Json := #[]
    let mut ctors : Array Json := #[]
    let mut recs : Array Json := #[]
    for c in ext do
      match c with
      | .inductInfo v =>
        types := types.push <| Json.mkObj [("name", (← nameId v.name)), ("levelParams", (← nameIds v.levelParams)),
          ("type", (← exprId v.type)), ("numParams", v.numParams), ("numIndices", v.numIndices),
          ("all", (← nameIds v.all)), ("ctors", (← nameIds v.ctors)), ("numNested", v.numNested),
          ("isRec", v.isRec), ("isUnsafe", v.isUnsafe), ("isReflexive", v.isReflexive)]
      | .ctorInfo v =>
        ctors := ctors.push <| Json.mkObj [("name", (← nameId v.name)), ("levelParams", (← nameIds v.levelParams)),
          ("type", (← exprId v.type)), ("induct", (← nameId v.induct)), ("cidx", v.cidx),
          ("numParams", v.numParams), ("numFields", v.numFields), ("isUnsafe", v.isUnsafe)]
      | .recInfo v =>
        let mut rules : Array Json := #[]
        for r in v.rules do
          rules := rules.push <| Json.mkObj [("ctor", (← nameId r.ctor)), ("nfields", r.nfields), ("rhs", (← exprId r.rhs))]
        recs := recs.push <| Json.mkObj [("name", (← nameId v.name)), ("levelParams", (← nameIds v.levelParams)),
          ("type", (← exprId v.type)), ("all", (← nameIds v.all)), ("numParams", v.numParams),
          ("numIndices", v.numIndices), ("numMotives", v.numMotives), ("numMinors", v.numMinors),
          ("rules", Json.arr rules), ("k", v.k), ("isUnsafe", v.isUnsafe)]
      | _ => pure ()
    out <| Json.mkObj [("inductive", Json.mkObj [("types", Json.arr types), ("ctors", Json.arr ctors), ("recs", Json.arr recs)])]
  return true

def metaLine : Json :=
  Json.mkObj [("meta", Json.mkObj [
    ("exporter", Json.mkObj [("name", "leanout"), ("version", "0.1.0")]),
    ("lean", Json.mkObj [("githash", Lean.githash), ("version", Lean.versionString)]),
    ("format", Json.mkObj [("version", "3.1.0")])])]

def run (env : Environment) (roots : List Name) (h : IO.FS.Stream) (allowUnsafe := false) : IO St := do
  let ((), st) ← (do
    out metaLine
    for r in roots do discard <| emit r : M Unit).run { allowUnsafe } |>.run (env, h)
  return st

end LeanOut
