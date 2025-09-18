-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def count_ones (n : Nat) : Nat :=
  sorry

def max_pn (n : Nat) : Nat :=
  sorry

def an_over (n : Nat) : List Float :=
  sorry

def an_over_average (n : Nat) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem count_ones_bounds {n : Nat} (h : n > 0) :
  count_ones n ≤ n ∧ count_ones n ≥ 0 := by
sorry

theorem count_ones_nat {n : Nat} (h : n > 0) :
  count_ones n ≥ 0 := by
sorry

theorem max_pn_gt_one {n : Nat} (h : n > 0) :
  max_pn n > 1 := by
sorry

theorem max_pn_nat {n : Nat} (h : n > 0) :
  max_pn n ≥ 0 := by
sorry

theorem an_over_length {n : Nat} (h : n > 0) :
  (an_over n).length = n := by
sorry

theorem an_over_all_positive {n : Nat} (h : n > 0) :
  ∀ x ∈ an_over n, x > 0 := by
sorry

theorem an_over_average_positive {n : Nat} (h : n > 0) :
  an_over_average n > 0 := by
sorry

theorem an_over_average_nat {n : Nat} (h : n > 0) :
  an_over_average n ≥ 0 := by
sorry
-- </vc-theorems>