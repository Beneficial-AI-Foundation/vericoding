-- <vc-preamble>
/- Define the triangular number function -/
def triangle : Nat → Nat
  | 0 => 0
  | n + 1 => (n + 1) + triangle n

/- Precondition for tail_triangle function -/
@[reducible, simp]
def tailTriangle_precond (n : Nat) (idx : Nat) (sum : Nat) : Prop :=
  idx ≤ n ∧ sum = triangle idx ∧ triangle n < 0x100000000
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def tailTriangle (n : Nat) (idx : Nat) (sum : Nat) (h_precond : tailTriangle_precond n idx sum) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def tailTriangle_postcond (n : Nat) (idx : Nat) (sum : Nat) (result : Nat) (h_precond : tailTriangle_precond n idx sum) : Prop :=
  result = triangle n

theorem tailTriangle_spec_satisfied (n : Nat) (idx : Nat) (sum : Nat) (h_precond : tailTriangle_precond n idx sum) :
    tailTriangle_postcond n idx sum (tailTriangle n idx sum h_precond) h_precond := by
  sorry
-- </vc-theorems>