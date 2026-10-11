/-
Copyright 2026 Keith Adler
Licensed under the Apache License, Version 2.0 (see LICENSE).
-/
import LeanOut.Emit
import LeanOut.Validate
open Lean

def usage : String :=
"usage: leanout [options] <Module>... [-- <ConstName>...]
       leanout --validate <file.ndjson>

options:
  -o FILE         write to FILE instead of stdout (FILE ending in .gz is compressed with gzip)
  --prefix P      only export constants whose name starts with P (plus their dependencies)
  --exclude P     drop roots whose name starts with P (dependencies are still exported if needed)
  --module M      only export constants declared in module M (plus their dependencies)
  --unsafe        include unsafe/partial declarations (default: skipped, see README)
  --stats         print declaration counts to stderr
  --axioms        print every axiom in the export to stderr
  --validate F    structurally validate an existing export (ids defined before use, no duplicates)"

structure Opts where
  out : Option String := none
  prefixes : List String := []
  excludes : List String := []
  modules : List String := []
  unsafe_ : Bool := false
  stats : Bool := false
  axioms : Bool := false
  rest : List String := []

partial def parseArgs (as : List String) (o : Opts) : Except String Opts :=
  match as with
  | [] => .ok { o with rest := o.rest.reverse }
  | "-o" :: f :: t => parseArgs t { o with out := some f }
  | "--prefix" :: p :: t => parseArgs t { o with prefixes := p :: o.prefixes }
  | "--exclude" :: p :: t => parseArgs t { o with excludes := p :: o.excludes }
  | "--module" :: m :: t => parseArgs t { o with modules := m :: o.modules }
  | "--unsafe" :: t => parseArgs t { o with unsafe_ := true }
  | "--stats" :: t => parseArgs t { o with stats := true }
  | "--axioms" :: t => parseArgs t { o with axioms := true }
  | a :: t =>
    if a.startsWith "-" && a != "--" then .error s!"unknown option {a}"
    else parseArgs t { o with rest := a :: o.rest }

/-- An output stream, plus the action that finishes it (flushing, or closing a gzip pipe). -/
def openOut (f : Option String) : IO (IO.FS.Stream × IO Unit) := do
  match f with
  | none => return (← IO.getStdout, pure ())
  | some f =>
    if f.endsWith ".gz" then
      -- write plain text next to the target, then compress it (a pipe would need the stream closed to signal EOF)
      let tmp := f ++ ".tmp"
      let h ← IO.FS.Handle.mk tmp .write
      return (IO.FS.Stream.ofHandle h, do
        h.flush
        let r ← IO.Process.output { cmd := "sh", args := #["-c", "gzip -c < \"$1\" > \"$2\" && rm -f \"$1\"", "sh", tmp, f] }
        if r.exitCode != 0 then throw <| IO.userError s!"gzip failed: {r.stderr}")
    else
      let h ← IO.FS.Handle.mk f .write
      return (IO.FS.Stream.ofHandle h, h.flush)

def main (args : List String) : IO UInt32 := do
  if let ["--validate", f] := args then
    let n ← LeanOut.validateFile f
    IO.eprintln (if n == 0 then "valid" else s!"{n} problem(s)")
    return if n == 0 then 0 else 1
  match parseArgs args {} with
  | .error e => IO.eprintln s!"{e}\n{usage}"; return 2
  | .ok o =>
  let (mods, names) := match o.rest.span (· != "--") with
    | (m, _ :: n) => (m, n) | (m, []) => (m, [])
  if mods.isEmpty then
    IO.eprintln usage
    return 2
  initSearchPath (← findSysroot)
  let env ← importModules (mods.map fun m => { module := m.toName : Import }).toArray {}
  let mut roots := ((env.constants.toList.map (·.1)).toArray.qsort Name.lt).toList
  if !names.isEmpty then roots := names.map String.toName
  let startsWith (ps : List String) (n : Name) := ps.any fun p => p.isPrefixOf n.toString
  if !o.prefixes.isEmpty then roots := roots.filter (startsWith o.prefixes)
  if !o.excludes.isEmpty then roots := roots.filter (!startsWith o.excludes ·)
  if !o.modules.isEmpty then
    let idxs := o.modules.filterMap fun m => env.header.moduleNames.findIdx? (· == m.toName)
    if idxs.length != o.modules.length then
      IO.eprintln "--module: module not found among the imports"
      return 2
    roots := roots.filter fun n => (env.getModuleIdxFor? n).any fun i => idxs.contains i.toNat
  let (stream, close) ← openOut o.out
  let st ← LeanOut.run env roots stream o.unsafe_
  close
  if o.stats then
    IO.eprintln s!"names {st.nName - 1}, levels {st.nLevel - 1}, exprs {st.nExpr}"
    for (k, n) in st.counts.toList.toArray.qsort (·.1 < ·.1) do IO.eprintln s!"  {k}: {n}"
  if o.axioms then
    for a in st.axioms.qsort Name.lt do IO.eprintln s!"axiom {a}"
  return 0
