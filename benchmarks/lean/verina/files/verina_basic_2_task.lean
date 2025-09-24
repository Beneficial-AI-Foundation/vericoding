-- <vc-preamble>
@[reducible, simp]
def findSmallest_precond (s : Array Nat) : Prop :=
  True
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def findSmallest (s : Array Nat) (h_precond : findSmallest_precond (s)) : Option Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def findSmallest_postcond (s : Array Nat) (result: Option Nat) (h_precond : findSmallest_precond (s)) :=
  let xs := s.toList
  match result with
  | none => xs = []
  | some r => r ∈ xs ∧ (∀ x, x ∈ xs → r ≤ x)

theorem findSmallest_spec_satisfied (s: Array Nat) (h_precond : findSmallest_precond (s)) :
    findSmallest_postcond (s) (findSmallest (s) h_precond) h_precond := by
  sorry
-- </vc-theorems>