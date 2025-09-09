def sum_list : List Nat → Nat 
  | [] => 0
  | x::xs => x + sum_list xs

-- <vc-helpers>
-- </vc-helpers>

def min_sequence_sum (n : Nat) (a : List Nat) : Nat :=
  sorry

theorem min_sequence_sum_non_negative
  (n : Nat) (a : List Nat) (h : a.length = n)
  : min_sequence_sum n a ≥ 0 :=
sorry

theorem min_sequence_sum_upper_bound
  (n : Nat) (a : List Nat) (h : a.length = n)
  : min_sequence_sum n a ≤ sum_list a :=
sorry 

theorem min_sequence_sum_all_equal
  (n : Nat) (a : List Nat) (h : a.length = n)
  (h' : ∀ i j, i < n → j < n → a[i]? = a[j]?)
  : min_sequence_sum n a = 0 :=
sorry

theorem min_sequence_sum_all_zeros
  (n : Nat) (a : List Nat) (h : a.length = n)
  (h' : ∀ i, i < n → a[i]? = some 0)
  : min_sequence_sum n a = 0 :=
sorry

theorem min_sequence_sum_all_ones 
  (n : Nat) (a : List Nat) (h : a.length = n)
  (h' : ∀ i, i < n → a[i]? = some 1)
  : min_sequence_sum n a = 0 :=
sorry

theorem min_sequence_sum_single_zero 
  : min_sequence_sum 1 [0] = 0 :=
sorry

theorem min_sequence_sum_equal_large_nums
  {x : Nat} (h : x = 2^31)
  : min_sequence_sum 2 [x, x] = 0 :=
sorry

/-
info: 14
-/
-- #guard_msgs in
-- #eval min_sequence_sum 5 [2, 3, 4, 5, 6]

/-
info: 0
-/
-- #guard_msgs in
-- #eval min_sequence_sum 4 [7, 7, 7, 7]

/-
info: 2
-/
-- #guard_msgs in
-- #eval min_sequence_sum 3 [1, 1, 3]

-- Apps difficulty: interview
-- Assurance level: unguarded