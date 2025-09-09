-- <vc-helpers>
-- </vc-helpers>

def repeat_sum (lists : List (List Nat)) : Nat := sorry

theorem repeat_sum_non_negative (lists : List (List Nat)) :
  repeat_sum lists ≥ 0 := sorry

theorem repeat_sum_disjoint_zero (lists : List (List Nat)) 
  (h : ∀ i j n, i < j → j < lists.length → 
    n ∈ (lists.get! i) → ¬ n ∈ (lists.get! j)) :
  repeat_sum lists = 0 := sorry

theorem repeat_sum_empty (lists : List (List Nat)) :
  lists = [] → repeat_sum lists = 0 := sorry

/-
info: 10
-/
-- #guard_msgs in
-- #eval repeat_sum [[1, 2, 3], [2, 8, 9], [7, 123, 8]]

/-
info: 0
-/
-- #guard_msgs in
-- #eval repeat_sum [[1], [2], [3, 4, 4, 4], [123456789]]

/-
info: 9
-/
-- #guard_msgs in
-- #eval repeat_sum [[1, 8, 8], [8, 8, 8], [8, 8, 8, 1]]

-- Apps difficulty: introductory
-- Assurance level: guarded