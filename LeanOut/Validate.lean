/-
Copyright 2026 Keith Adler
Licensed under the Apache License, Version 2.0 (see LICENSE).
-/
import Lean
open Lean

namespace LeanOut

/-- Structural validation of an NDJSON export, independent of any kernel: every id is defined
exactly once and before use, every declaration name is unique, and recursor/constructor/inductive
cross-references resolve. Returns the number of problems found (the first few are printed). -/
def validateFile (path : String) : IO Nat := do
  let h ← IO.FS.Handle.mk path .read
  let mut names : Std.HashSet Nat := (({} : Std.HashSet Nat).insert 0)
  let mut levels : Std.HashSet Nat := (({} : Std.HashSet Nat).insert 0)
  let mut exprs : Std.HashSet Nat := {}
  let mut declared : Std.HashSet Nat := {}
  let mut problems := 0
  let mut lineNo := 0
  let mut sawMeta := false
  let bad (n : Nat) (ln : Nat) (msg : String) : IO Nat := do
    if n < 20 then IO.eprintln s!"line {ln}: {msg}"
    return n + 1
  repeat
    let line ← h.getLine
    if line.isEmpty then break
    lineNo := lineNo + 1
    let j ← match Json.parse line with
      | .ok j => pure j
      | .error e => do problems ← bad problems lineNo s!"not JSON: {e}"; continue
    let nat (k : String) (o : Json) : Option Nat := (o.getObjVal? k).toOption >>= fun v => v.getNat?.toOption
    let isNum (v : Json) : Option Nat := v.getNat?.toOption
    if (j.getObjVal? "meta").isOk then sawMeta := true; continue
    if let some i := nat "in" j then
      let ok ← match (j.getObjVal? "str").toOption, (j.getObjVal? "num").toOption with
        | some o, _ => pure ((nat "pre" o).any names.contains)
        | _, some o => pure ((nat "pre" o).any names.contains)
        | _, _ => pure false
      if !ok || names.contains i then problems ← bad problems lineNo s!"bad name {i}"
      names := names.insert i
    else if let some i := nat "il" j then
      let refs : List Nat :=
        match (j.getObjVal? "succ").toOption >>= isNum with
        | some a => [a]
        | none =>
          match (j.getObjVal? "max" |>.toOption) <|> (j.getObjVal? "imax" |>.toOption) with
          | some (.arr a) => a.toList.filterMap isNum
          | _ => []
      let pn := (j.getObjVal? "param").toOption >>= isNum
      if !refs.all levels.contains || (pn.any fun n => !names.contains n) || levels.contains i then
        problems ← bad problems lineNo s!"bad level {i}"
      levels := levels.insert i
    else if let some i := nat "ie" j then
      let mut ok := !exprs.contains i
      for k in ["sort"] do
        if let some v := (j.getObjVal? k).toOption >>= isNum then ok := ok && levels.contains v
      for k in ["app", "lam", "forallE", "letE", "proj", "mdata", "const"] do
        if let some o := (j.getObjVal? k).toOption then
          for f in ["fn", "arg", "type", "body", "value", "struct", "expr"] do
            if let some v := nat f o then ok := ok && exprs.contains v
          for f in ["name", "typeName"] do
            if let some v := nat f o then ok := ok && names.contains v
          if let some (.arr us) := (o.getObjVal? "us").toOption then
            ok := ok && us.all fun u => (isNum u).any levels.contains
      if !ok then problems ← bad problems lineNo s!"bad expr {i}"
      exprs := exprs.insert i
    else
      -- declaration: check the declared name(s) are fresh and the type/value ids exist
      let some (k, o) := j.getObj?.toOption.bind fun m => m.toArray.toList.head?.map fun (k, v) => (k, v)
        | problems ← bad problems lineNo "unrecognised line"; continue
      let units : List Json := if k == "inductive" then
          ["types", "ctors", "recs"].flatMap fun f => match (o.getObjVal? f).toOption with
            | some (.arr a) => a.toList | _ => []
        else [o]
      for u in units do
        if let some n := nat "name" u then
          if declared.contains n || !names.contains n then problems ← bad problems lineNo s!"bad/duplicate declaration {n}"
          declared := declared.insert n
        for f in ["type", "value"] do
          if let some e := nat f u then
            if !exprs.contains e then problems ← bad problems lineNo s!"{f} {e} undefined"
  if !sawMeta then problems ← bad problems 0 "missing meta line"
  return problems

end LeanOut
