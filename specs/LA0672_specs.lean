-- <vc-preamble>
def Distance (s t : Int) : Nat :=
  if s ≥ t then Int.natAbs (s - t) else Int.natAbs (t - s)

def ValidInput (x a b : Int) : Prop :=
  1 ≤ x ∧ x ≤ 1000 ∧
  1 ≤ a ∧ a ≤ 1000 ∧
  1 ≤ b ∧ b ≤ 1000 ∧
  x ≠ a ∧ x ≠ b ∧ a ≠ b ∧
  Distance x a ≠ Distance x b

def CorrectResult (x a b : Int) (result : String) : Prop :=
  (result = "A" ↔ Distance x a < Distance x b) ∧
  (result = "B" ↔ Distance x b < Distance x a)

@[reducible, simp]
def solve_precond (x a b : Int) : Prop :=
  ValidInput x a b
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (x a b : Int) (h_precond : solve_precond x a b) : String :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (x a b : Int) (result : String) (h_precond : solve_precond x a b) : Prop :=
  (result = "A" ∨ result = "B") ∧ CorrectResult x a b result

theorem solve_spec_satisfied (x a b : Int) (h_precond : solve_precond x a b) :
    solve_postcond x a b (solve x a b h_precond) h_precond := by
  sorry
-- </vc-theorems>