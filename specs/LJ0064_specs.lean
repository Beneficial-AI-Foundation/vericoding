-- <vc-preamble>
-- Precondition for smallest_list_length
@[reducible, simp]
def smallestListLength_precond (list : Array (Array Int)) : Prop :=
  list.size > 0
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def smallestListLength (list : Array (Array Int)) (h_precond : smallestListLength_precond list) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def smallestListLength_postcond (list : Array (Array Int)) (min : Nat) (h_precond : smallestListLength_precond list) : Prop :=
  min ≥ 0 ∧ 
  (∀ i, i < list.size → min ≤ list[i]!.size) ∧
  (∃ i, i < list.size ∧ min = list[i]!.size)

theorem smallestListLength_spec_satisfied (list : Array (Array Int)) (h_precond : smallestListLength_precond list) :
    smallestListLength_postcond list (smallestListLength list h_precond) h_precond := by
  sorry
-- </vc-theorems>