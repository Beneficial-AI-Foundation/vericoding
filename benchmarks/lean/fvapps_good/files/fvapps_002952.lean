-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def combs_non_empty_boxes (n k : Int) : Int :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem invalid_inputs (n k : Int) :
  k < 0 ∨ k > n → combs_non_empty_boxes n k = -1 :=
sorry

theorem single_box (n : Int) :
  n > 0 → combs_non_empty_boxes n 1 = 1 :=
sorry

theorem max_boxes (n : Int) :
  n > 0 → combs_non_empty_boxes n n = 1 :=
sorry

theorem result_properties_nonneg (n k : Int) :
  combs_non_empty_boxes n k ≥ 0 :=
sorry

theorem result_properties_zero_boxes (n : Int) :
  combs_non_empty_boxes n 0 = 0 :=
sorry

theorem result_properties_positive (n k : Int) :
  k > 0 → k ≤ n → combs_non_empty_boxes n k > 0 :=
sorry

theorem valid_range_result (n k : Int) :
  1 < k → k ≤ n → combs_non_empty_boxes n k > 0 :=
sorry

theorem valid_range_upper_bound (n k : Nat) :
  1 < k → k ≤ n → combs_non_empty_boxes n k ≤ k^n :=
sorry
-- </vc-theorems>