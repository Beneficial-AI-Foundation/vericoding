-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def repeat_sum (lists : List (List Nat)) : Nat := sorry

theorem repeat_sum_non_negative (lists : List (List Nat)) :
  repeat_sum lists ≥ 0 := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem repeat_sum_disjoint_zero (lists : List (List Nat)) 
  (h : ∀ i j n, i < j → j < lists.length → 
    n ∈ (lists.get! i) → ¬ n ∈ (lists.get! j)) :
  repeat_sum lists = 0 := sorry

theorem repeat_sum_empty (lists : List (List Nat)) :
  lists = [] → repeat_sum lists = 0 := sorry
-- </vc-theorems>