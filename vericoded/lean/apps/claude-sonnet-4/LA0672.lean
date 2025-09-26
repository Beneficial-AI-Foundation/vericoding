import Mathlib
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
-- LLM HELPER
lemma distance_trichotomy (x a b : Int) (h : Distance x a ≠ Distance x b) :
  Distance x a < Distance x b ∨ Distance x b < Distance x a := by
  omega
-- </vc-helpers>

-- <vc-definitions>
def solve (x a b : Int) (h_precond : solve_precond x a b) : String :=
  if Distance x a < Distance x b then "A" else "B"
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (x a b : Int) (result : String) (h_precond : solve_precond x a b) : Prop :=
  (result = "A" ∨ result = "B") ∧ CorrectResult x a b result

theorem solve_spec_satisfied (x a b : Int) (h_precond : solve_precond x a b) :
    solve_postcond x a b (solve x a b h_precond) h_precond := by
  unfold solve solve_postcond CorrectResult
  split_ifs with h_lt
  · -- Case: Distance x a < Distance x b, return "A"
    constructor
    · left; rfl
    · constructor
      · constructor
        · intro; exact h_lt
        · intro; rfl
      · constructor
        · intro h_eq; contradiction
        · intro h_ba; exfalso; linarith [h_lt, h_ba]
  · -- Case: Distance x a ≥ Distance x b, return "B"
    constructor
    · right; rfl
    · constructor
      · constructor
        · intro h_eq; contradiction
        · intro h_ab; exfalso; exact h_lt h_ab
      · constructor
        · intro h_eq
          have h_neq : Distance x a ≠ Distance x b := by
            unfold solve_precond ValidInput at h_precond
            exact h_precond.right.right.right.right.right.right.right.right.right
          have h_tri := distance_trichotomy x a b h_neq
          cases h_tri with
          | inl h_ab => exfalso; exact h_lt h_ab
          | inr h_ba => exact h_ba
        · intro; rfl
-- </vc-theorems>
