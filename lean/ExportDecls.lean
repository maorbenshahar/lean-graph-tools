/-
  Export all project declarations with their dependencies as JSON.

  Usage:
    lake build  -- must build first
    lake env lean --run <path>/ExportDecls.lean <RootModule>

  Output: JSON with declaration name, kind, module, sorry status,
  privacy, and actual declaration-level dependencies (not file-level imports).

  Auto-generated sub-declarations (_proof_N, eq_N, match_N, etc.) are merged
  into their parent: their sorry status and deps are absorbed by the parent.
  This means consumers never see internal artifacts.

  Key optimisation: only follows project-local dependencies (skips Mathlib/Init/
  Std/etc via the projectNames set). Since external libraries are sorry-free,
  any sorry must flow through project code. This keeps the export fast.

  Sorry detection is TRANSITIVE: if a public theorem calls a private
  helper that uses sorry, the public theorem is marked has_sorry=true.
  This matches the behavior of `#print axioms`.
-/
import Lean

open Lean

def getKind (ci : ConstantInfo) : Option String := match ci with
  | .ctorInfo _  => none
  | .recInfo _   => none
  | .quotInfo _  => none
  | .defnInfo _  => some "def"
  | .thmInfo _   => some "theorem"
  | .axiomInfo _  => some "axiom"
  | .inductInfo _ => some "inductive"
  | .opaqueInfo _ => some "opaque"

def getValueConstants (ci : ConstantInfo) : Array Name := match ci with
  | .defnInfo v  => v.value.getUsedConstants
  | .thmInfo v   => v.value.getUsedConstants
  | .opaqueInfo v => v.value.getUsedConstants
  | _ => #[]

/-- Get all constants referenced by a declaration (type + value). -/
def getAllConstants (ci : ConstantInfo) : Array Name :=
  ci.type.getUsedConstants ++ getValueConstants ci

/-- Check if a declaration contains a literal sorryAx in its type or value. -/
def containsSorryAx (ci : ConstantInfo) : Bool :=
  (getAllConstants ci).contains ``sorryAx

/-- Find the parent name for a sub-declaration by stripping the last component.
    Returns `none` if stripping doesn't yield a valid project name. -/
def findParent (name : Name) (projectNames : NameHashSet) : Option Name :=
  match name with
  | .str parent _ =>
    if projectNames.contains parent then some parent else none
  | _ => none

/-- Compute transitive sorry status for all project declarations.

    A declaration "has sorry" if `sorryAx` is reachable through any chain
    of project-internal references. This matches `#print axioms` behavior.

    Algorithm: DFS with memoization. Only recurses into project constants
    (external library constants are assumed sorry-free). -/
partial def hasSorryTransitive (env : Environment) (projectNames : NameHashSet)
    (memo : IO.Ref (NameMap Bool)) (name : Name) : IO Bool := do
  -- sorryAx itself is the base case
  if name == ``sorryAx then return true
  -- Non-project constants are sorry-free
  if !projectNames.contains name then return false
  -- Check memo
  let m ← memo.get
  if let some result := m.find? name then return result
  -- Mark as false initially (handles cycles)
  memo.modify (·.insert name false)
  let some cinfo := env.find? name | return false
  let allConsts := getAllConstants cinfo
  for c in allConsts do
    if c == name then continue
    if ← hasSorryTransitive env projectNames memo c then
      memo.modify (·.insert name true)
      return true
  return false

/-- Data accumulated for a parent declaration from its sub-declarations. -/
structure MergedData where
  extraDeps : Array Name := #[]
  childHasSorry : Bool := false

unsafe def main : List String → IO Unit := fun args => do
  let rootModuleStr ← match args.head? with
    | some m => pure m
    | none =>
      IO.eprintln "Usage: lake env lean --run ExportDecls.lean <RootModule>"
      IO.eprintln "Example: lake env lean --run ExportDecls.lean QuantumInformation"
      IO.Process.exit 1

  let rootModule := rootModuleStr.toName

  enableInitializersExecution
  initSearchPath (← findSysroot)
  let env ← importModules #[{ module := rootModule }] {}

  let mods := env.header.moduleNames
  let rootName := rootModule.getRoot

  -- Collect all project declaration names into a set (including internal/private)
  let mut projectNames : NameHashSet := {}
  for i in [:mods.size] do
    if mods[i]!.getRoot != rootName then continue
    let md := env.header.moduleData[i]!
    for j in [:md.constNames.size] do
      projectNames := projectNames.insert md.constNames[j]!

  -- Precompute transitive sorry status for all project declarations
  let memo ← IO.mkRef ({} : NameMap Bool)
  for name in projectNames.toArray do
    let _ ← hasSorryTransitive env projectNames memo name
  let sorryMap ← memo.get

  -- First pass: find sub-declarations and merge their data into parents
  let mut mergedMap : NameMap MergedData := {}

  for name in projectNames.toArray do
    if !name.isInternalDetail then continue
    -- Only merge truly auto-generated decls (no source location).
    -- Private user declarations (_private.*) have declRange and should be kept.
    if (declRangeExt.find? env name).isSome then continue
    let some parent := findParent name projectNames | continue
    let some cinfo := env.find? name | continue

    let childSorry := containsSorryAx cinfo
    let childDeps := getAllConstants cinfo

    let prev := mergedMap.find? parent |>.getD {}
    mergedMap := mergedMap.insert parent {
      extraDeps := prev.extraDeps ++ childDeps
      childHasSorry := prev.childHasSorry || childSorry
    }

  -- Helper: collect deps for a declaration (including merged sub-decl deps)
  let collectDeps := fun (name : Name) (cinfo : ConstantInfo) => do
    let ownConsts := getAllConstants cinfo
    let mergedConsts := match mergedMap.find? name with
      | some md => md.extraDeps
      | none => #[]
    let allConsts := ownConsts ++ mergedConsts

    let mut seen : NameHashSet := {}
    let mut projectDeps : Array String := #[]
    for c in allConsts do
      if c == name || c == ``sorryAx then continue
      if !projectNames.contains c then continue
      if seen.contains c then continue
      -- Skip sub-declarations (they're merged into parents)
      if c.isInternalDetail && (findParent c projectNames).isSome then continue
      -- Skip internal deps UNLESS they have sorry (sorry blockers must be visible)
      if c.isInternal then
        let cHasSorry := match sorryMap.find? c with
          | some v => v
          | none => false
        if !cHasSorry then continue
      seen := seen.insert c
      projectDeps := projectDeps.push c.toString
    pure projectDeps

  -- Build JSON — skip sub-declarations
  let mut decls : Array Json := #[]

  for i in [:mods.size] do
    if mods[i]!.getRoot != rootName then continue
    let md := env.header.moduleData[i]!
    let modStr := mods[i]!.toString

    for j in [:md.constNames.size] do
      let name := md.constNames[j]!

      -- Skip auto-generated sub-declarations (merged into parent)
      if name.isInternalDetail then
        if (declRangeExt.find? env name).isNone then
          if (findParent name projectNames).isSome then continue

      let some cinfo := env.find? name | continue

      let isPrivate := name.isInternal
      let hasSorry := match sorryMap.find? name with
        | some v => v
        | none => false

      -- contains_sorry includes own sorry + merged children's sorry
      let ownSorry := containsSorryAx cinfo
      let childSorry := match mergedMap.find? name with
        | some md => md.childHasSorry
        | none => false
      let containsSorry := ownSorry || childSorry

      let some kind := getKind cinfo | continue

      let projectDeps ← collectDeps name cinfo

      -- Line number from declaration range (1-indexed for display)
      let lineNum : Option Nat := match declRangeExt.find? env name with
        | some range => some (range.range.pos.line + 1)
        | none => none

      let mut fields : Array (String × Json) := #[
        ("name", .str name.toString),
        ("kind", .str kind),
        ("module", .str modStr),
        ("has_sorry", .bool hasSorry),
        ("contains_sorry", .bool containsSorry),
        ("is_private", .bool isPrivate),
        ("deps", .arr (projectDeps.map .str))
      ]

      match lineNum with
      | some l => fields := fields.push ("line", .num l)
      | none => pure ()

      decls := decls.push <| Json.mkObj fields.toList

  let output := Json.mkObj [
    ("root_module", .str rootModuleStr),
    ("declaration_count", .num decls.size),
    ("declarations", .arr decls)
  ]

  IO.println output.pretty
