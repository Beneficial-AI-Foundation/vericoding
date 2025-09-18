-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def jumping (seq : List Int) (target : Int) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem jumping_result_bounded_by_length (seq : List Int) (target : Int) :
  seq ≠ [] → jumping seq target ≤ seq.length :=
  sorry

theorem jumping_preserves_input (seq : List Int) (target : Int) : 
  jumping seq target = jumping seq target ∧ seq = seq :=
  sorry

theorem jumping_specific_case1 :
  jumping [0, 3, 0, 1, -3] 3 = 2 :=
  sorry

theorem jumping_specific_case2 :
  jumping [0, -1, -2, -3, -4] 4 = 2 :=
  sorry

theorem jumping_specific_case3 :
  jumping [0, -1, -2, -3, -4] 3 = 0 :=
  sorry
-- </vc-theorems>