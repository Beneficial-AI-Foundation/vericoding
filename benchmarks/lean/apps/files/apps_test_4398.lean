-- <vc-preamble>
-- Helper functions (assumed to exist)
noncomputable axiom SplitLines : String → List String
noncomputable axiom StringToInt : String → Int
noncomputable axiom SplitBySpace : String → List String

noncomputable def ValidInput (input : String) : Prop :=
  let lines := SplitLines input
  lines.length ≥ 2 ∧
  (let n := StringToInt (lines[0]!)
   let parts := SplitBySpace (lines[1]!)
   parts.length ≥ 2 ∧
   n ≥ 0 ∧
   n ≤ (parts[0]!).length ∧ n ≤ (parts[1]!).length)

noncomputable def GetN (input : String) : Int :=
  let lines := SplitLines input
  StringToInt (lines[0]!)

noncomputable def GetS (input : String) : String :=
  let lines := SplitLines input
  let parts := SplitBySpace (lines[1]!)
  parts[0]!

noncomputable def GetT (input : String) : String :=
  let lines := SplitLines input
  let parts := SplitBySpace (lines[1]!)
  parts[1]!

def AlternateChars (s t : String) (n : Int) : String :=
  if n ≤ 0 then ""
  else if s.length = 0 ∨ t.length = 0 then ""
  else String.mk [s.get ⟨0⟩] ++ String.mk [t.get ⟨0⟩] ++ AlternateChars (s.drop 1) (t.drop 1) (n - 1)
termination_by n.natAbs

@[reducible, simp]
def solve_precond (input : String) : Prop :=
  input.length > 0
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
noncomputable def solve (input : String) (h_precond : solve_precond input) : String :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
noncomputable def solve_postcond (input : String) (result : String) (h_precond : solve_precond input) : Prop :=
  (ValidInput input → 
    (let n := GetN input
     let s := GetS input
     let t := GetT input
     result.length = (2 * n + 1).natAbs ∧
     (result.length > 0 → result.get ⟨result.length - 1⟩ = '\n') ∧
     result.take (result.length - 1) = AlternateChars s t n)) ∧
  (¬ValidInput input → result = "")

theorem solve_spec_satisfied (input : String) (h_precond : solve_precond input) :
    solve_postcond input (solve input h_precond) h_precond := by
  sorry
-- </vc-theorems>