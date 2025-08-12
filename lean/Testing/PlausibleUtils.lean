import Plausible

namespace Testing.PlausibleUtils

open Plausible

section BasicHelpers

def checkProperty (p : Prop) [Testable p] (numTests : Nat := 100) : IO Unit := do
  let cfg : Configuration := { numInst := numTests }
  let result ← Testable.check cfg p
  match result with
  | TestResult.success _ => IO.println s!"✓ Property held for {numTests} tests"
  | TestResult.failure _ xs => do
    IO.println s!"✗ Found counterexample:"
    for x in xs do
      IO.println s!"  {x}"
  | TestResult.gaveUp n => IO.println s!"⚠ Gave up after {n} tests"

def checkWithMsg (msg : String) (p : Prop) [Testable p] (numTests : Nat := 100) : IO Unit := do
  IO.println s!"Testing: {msg}"
  checkProperty p numTests

end BasicHelpers

section PropertyPatterns

def checkForAll {α : Type} [Sampleable α] [PrintableProp α] 
    (property : α → Prop) [∀ x, Testable (property x)] 
    (numTests : Nat := 100) : IO Unit := do
  checkProperty (∀ x, property x) numTests

def checkExists {α : Type} [Sampleable α] [PrintableProp α]
    (property : α → Prop) [∀ x, Testable (property x)]
    (numTests : Nat := 100) : IO Unit := do
  checkProperty (∃ x, property x) numTests

def checkImplication {α : Type} [Sampleable α] [PrintableProp α]
    (precond : α → Prop) [∀ x, Testable (precond x)]
    (postcond : α → Prop) [∀ x, Testable (postcond x)]
    (numTests : Nat := 100) : IO Unit := do
  checkProperty (∀ x, precond x → postcond x) numTests

end PropertyPatterns

section SpecHelpers

def quickCheck (spec : Prop) [Testable spec] : IO Bool := do
  let cfg : Configuration := { numInst := 20 }
  let result ← Testable.check cfg spec
  match result with
  | TestResult.success _ => pure true
  | _ => pure false

def findCounterexample {α : Type} [Sampleable α] [PrintableProp α]
    (property : α → Prop) [∀ x, Testable (property x)]
    (maxAttempts : Nat := 100) : IO (Option α) := do
  sorry

end SpecHelpers

section TacticHelpers

macro "plausible_check" : tactic => `(tactic| plausible (config := { numInst := 100 }))

macro "quick_plausible" : tactic => `(tactic| plausible (config := { numInst := 20 }))

end TacticHelpers

end Testing.PlausibleUtils