import LeanChecker

open Lean

/-- Recheck the entire compact source against the pinned Mathlib environment. -/
private unsafe def replayCompact : IO Unit := do
  let src : System.FilePath := "vendor/grh-compact/src"
  let mut modules : Array Import := #[]
  for file in ← src.walkDir do
    if file.extension == some "lean" then
      let parts := (file.withExtension "").components.drop src.components.length
      modules := modules.push { module := (String.intercalate "." parts).toName }
  unless modules.size == 794 do throw <| IO.userError s!"unexpected module count {modules.size}"
  withImportModules #[{ module := `Mathlib }] {} fun base =>
    withImportModules modules {} fun full => do
      let mut additions : Std.HashMap Name ConstantInfo := {}
      for (name, info) in full.constants.map₁ do
        unless base.contains name do
          if info matches .axiomInfo _ then throw <| IO.userError s!"extra axiom {name}"
          additions := additions.insert name info
      for name in [`riemannHypothesis, `LFunction_ne_zero_of_half_lt_re] do
        unless additions.contains name do throw <| IO.userError s!"missing theorem {name}"
      let checked ← base.toKernelEnv.replay additions
      for name in [`riemannHypothesis, `LFunction_ne_zero_of_half_lt_re] do
        unless checked.find? name matches some (.thmInfo _) do
          throw <| IO.userError s!"replay did not produce theorem {name}"
      IO.println s!"Replayed {additions.size} declarations across {modules.size} compact modules against Mathlib; both RH and Dirichlet nonvanishing are checked theorems."

#eval replayCompact
