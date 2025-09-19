-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def max_non_overlapping (nums: List Int) (target: Int) : Nat :=
  sorry

def abs (n: Int) : Nat :=
  sorry

def sum_list (l: List Nat) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem max_non_overlapping_non_negative (nums: List Int) (target: Int) :
  max_non_overlapping nums target ≥ 0 :=
sorry

theorem max_non_overlapping_bounded_by_length (nums: List Int) (target: Int) :
  max_non_overlapping nums target ≤ nums.length :=
sorry

theorem max_non_overlapping_empty_list (target: Int) :
  max_non_overlapping [] target = 0 :=
sorry

theorem max_non_overlapping_all_zeros (n: Nat) :
  max_non_overlapping (List.replicate n 0) 0 = n :=
sorry

theorem max_non_overlapping_self_consistent (nums: List Int) (target: Int) :
  max_non_overlapping nums target = max_non_overlapping nums target :=
sorry
-- </vc-theorems>