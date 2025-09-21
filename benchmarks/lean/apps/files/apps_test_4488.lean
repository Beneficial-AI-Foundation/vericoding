-- <vc-preamble>
axiom FindNextNewline : String → Nat → Int

axiom SplitLinesSpec : String → List String

axiom IsValidInteger : String → Prop

axiom ParseIntHelper : String → Nat → Int

axiom ParseIntSpec : String → Int

axiom ValidInput : String → Prop

@[reducible, simp]
def solve_precond (input : String) : Prop :=
  input.length > 0
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (input : String) (h_precond : solve_precond input) : String :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (input : String) (result : String) (h_precond : solve_precond input) : Prop :=
  (ValidInput input →
    let lines := SplitLinesSpec input
    let a := ParseIntSpec (lines[0]!)
    let b := ParseIntSpec (lines[1]!)
    (result = "LESS\n" ↔ a < b) ∧
    (result = "GREATER\n" ↔ a > b) ∧
    (result = "EQUAL\n" ↔ a = b)) ∧
  (¬ValidInput input → result = "")

theorem solve_spec_satisfied (input : String) (h_precond : solve_precond input) :
    solve_postcond input (solve input h_precond) h_precond := by
  sorry
-- </vc-theorems>