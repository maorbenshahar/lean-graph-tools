/-
Test: verify that `importModules (loadExts := true)` enables correct pretty-printing
of Lean/Mathlib notations like `4 ^ n`, `*`, `0 ≤ x`, `→ₗ[ℂ]`.

The root cause of the original bug: `importModules` defaults to `loadExts := false`,
which means PersistentEnvExtension states (including `@[app_unexpander]` tables) are
never populated via `addImportedFn`. Without those unexpanders, `ppExpr` falls back
to showing `HPow.hPow 4 n`, `HMul.hMul`, `LE.le 0 x`, `LinearMap (RingHom.id ℂ)`.

Fix: pass `loadExts := true` to `importModules`.

Run with:
  cd /home/maor/Desktop/git/QuantumInformation/.claude/worktrees/agent-a6ae8225/QuantumInformation
  lake env lean --run /home/maor/Desktop/git/sig-tree/lean/TestPP.lean
-/
import Lean
open Lean Meta

unsafe def main : List String → IO Unit := fun _ => do
  enableInitializersExecution
  initSearchPath (← findSysroot)
  -- loadExts := true is the critical fix
  let env ← importModules #[{ module := `QuantumInformation }] {} (loadExts := true)

  let opts := ({} : Options)
    |>.setBool `pp.fieldNotation false
    |>.setBool `pp.fullNames false
    |>.setBool `pp.universes false
    |>.setBool `pp.instanceNames false
    |>.setBool `pp.all false
    |>.setBool `pp.raw false

  let coreCtx : Core.Context := { options := opts, fileName := "<test>", fileMap := FileMap.ofString "" }
  let coreState : Core.State := { env := env }

  let ppType (e : Expr) : IO String := do
    let action : MetaM String := return (← PrettyPrinter.ppExpr e).pretty (width := 120)
    match ← (action.run' {} {} |>.run' coreCtx coreState).toIO' with
    | .ok s => return s
    | .error ex => return s!"<error: {← ex.toMessageData.toString}>"

  -- Pretty-print Protocols.BB84.GeneralSecurity.ckr_security_reduction
  -- Expected: shows `4 ^ n`, `*`, `0 ≤ ε_coll`, `→ₗ[ℂ]`, `ℕ`, `ℝ`
  -- NOT: HPow.hPow, HMul.hMul, LE.le 0, LinearMap (RingHom.id Complex)
  let name := `Protocols.BB84.GeneralSecurity.ckr_security_reduction
  match env.find? name with
  | none => IO.println s!"Declaration not found: {name}"
  | some ci =>
    IO.println s!"Type of {name}:"
    IO.println (← ppType ci.type)
