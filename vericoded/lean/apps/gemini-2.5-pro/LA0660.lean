import Mathlib
-- <vc-preamble>
-- Assume these helper functions exist
axiom SplitStringPure : String → List String
axiom IsValidInt : String → Bool
axiom StringToIntPure : String → Int

noncomputable def ValidInput (input : String) : Bool :=
  if h : input.length > 0 then
    let parts := SplitStringPure input
    parts.length ≥ 2 && IsValidInt (parts[0]!) && IsValidInt (parts[1]!)
  else
    false

def SameGroup (a b : Int) : Bool :=
  let n1 := [1, 3, 5, 7, 8, 10, 12]
  let n2 := [4, 6, 9, 11]
  (a ∈ n1 && b ∈ n1) || (a ∈ n2 && b ∈ n2) || (a == 2 && b == 2)

noncomputable def CorrectOutput (input result : String) : Prop :=
  input.length > 0 →
  if ValidInput input then
    let parts := SplitStringPure input
    let a := StringToIntPure (parts[0]!)
    let b := StringToIntPure (parts[1]!)
    (result = "Yes\n" ↔ SameGroup a b) ∧ (result = "No\n" ↔ ¬SameGroup a b)
  else
    result = ""

@[reducible, simp]
def solve_precond (input : String) : Prop :=
  input.length > 0
-- </vc-preamble>

-- <vc-helpers>
-- No helpers needed.
-- </vc-helpers>

-- <vc-definitions>
noncomputable def solve (input : String) (h_precond : solve_precond input) : String :=
  let parts := SplitStringPure input
  if decide (parts.length ≥ 2) && IsValidInt (parts[0]!) && IsValidInt (parts[1]!) then
    let a := StringToIntPure (parts[0]!)
    let b := StringToIntPure (parts[1]!)
    if SameGroup a b then
      "Yes\n"
    else
      "No\n"
  else
    ""
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
noncomputable def solve_postcond (input : String) (result : String) (h_precond : solve_precond input) : Prop :=
  (result = "Yes\n" ∨ result = "No\n" ∨ result = "") ∧ CorrectOutput input result

theorem solve_spec_satisfied (input : String) (h_precond : solve_precond input) :
    solve_postcond input (solve input h_precond) h_precond := by
  unfold solve_postcond solve CorrectOutput ValidInput
  simp [h_precond]
  split_ifs <;> simp_all
-- </vc-theorems>
