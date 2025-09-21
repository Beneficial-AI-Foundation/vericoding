-- <vc-preamble>
@[reducible, simp]
def maxOfList_precond (lst : List Nat) : Prop :=
  lst.length > 0
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def maxOfList (lst : List Nat) (h_precond : maxOfList_precond (lst)) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def maxOfList_postcond (lst : List Nat) (result: Nat) (h_precond : maxOfList_precond (lst)) : Prop :=
  result ∈ lst ∧ ∀ x ∈ lst, x ≤ result

theorem maxOfList_spec_satisfied (lst: List Nat) (h_precond : maxOfList_precond (lst)) :
    maxOfList_postcond (lst) (maxOfList (lst) h_precond) h_precond := by
  sorry
-- </vc-theorems>