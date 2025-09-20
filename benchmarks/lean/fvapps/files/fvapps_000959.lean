-- <vc-preamble>
def sum_list : List Nat → Nat 
  | [] => 0
  | x::xs => x + sum_list xs
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def min_sequence_sum (n : Nat) (a : List Nat) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
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
-- </vc-theorems>