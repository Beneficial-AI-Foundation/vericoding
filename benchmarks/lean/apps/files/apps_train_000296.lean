def max_sum_after_partitioning (arr : List Int) (k : Nat) : Int :=
sorry

def sum (l : List Int) : Int :=
sorry

def max (l : List Int) : Int :=
sorry

-- <vc-helpers>
-- </vc-helpers>

def len (l : List Int) : Nat :=
sorry

theorem result_bounds {arr : List Int} {k : Nat}
  (h1 : arr.length > 0)
  (h2 : ∀ x ∈ arr, x > 0)
  (h3 : k > 0)
  (h4 : k ≤ 100) :
  sum arr ≤ max_sum_after_partitioning arr k ∧ 
  max_sum_after_partitioning arr k ≤ len arr * max arr :=
sorry

theorem k_equals_one {arr : List Int}
  (h1 : arr.length > 0)
  (h2 : ∀ x ∈ arr, x > 0) :
  max_sum_after_partitioning arr 1 = sum arr :=
sorry

theorem k_equals_length {arr : List Int}
  (h1 : arr.length > 0)
  (h2 : ∀ x ∈ arr, x > 0) :
  max_sum_after_partitioning arr arr.length = len arr * max arr :=
sorry

theorem single_element {arr : List Int} {k : Nat}
  (h1 : arr.length = 1)
  (h2 : k > 0) :
  max_sum_after_partitioning arr k = arr[0] :=
sorry

/-
info: 84
-/
-- #guard_msgs in
-- #eval max_sum_after_partitioning [1, 15, 7, 9, 2, 5, 10] 3

/-
info: 83
-/
-- #guard_msgs in
-- #eval max_sum_after_partitioning [1, 4, 1, 5, 7, 3, 6, 1, 9, 9, 3] 4

/-
info: 1
-/
-- #guard_msgs in
-- #eval max_sum_after_partitioning [1] 1

-- Apps difficulty: interview
-- Assurance level: unguarded