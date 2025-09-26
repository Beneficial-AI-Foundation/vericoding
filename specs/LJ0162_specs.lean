-- <vc-preamble>
@[reducible, simp]
def smallestListLength_precond (lists : Array (Array Int)) :=
  lists.size > 0
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def smallestListLength (lists : Array (Array Int)) (h_precond : smallestListLength_precond (lists)) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def smallestListLength_postcond (lists : Array (Array Int)) (result: Nat) (h_precond : smallestListLength_precond (lists)) :=
  (∃ i, i < lists.size ∧ result = lists[i]!.size) ∧ 
  (∀ i, i < lists.size → result ≤ lists[i]!.size)

theorem smallestListLength_spec_satisfied (lists: Array (Array Int)) (h_precond : smallestListLength_precond (lists)) :
    smallestListLength_postcond (lists) (smallestListLength (lists) h_precond) h_precond := by
  sorry
-- </vc-theorems>