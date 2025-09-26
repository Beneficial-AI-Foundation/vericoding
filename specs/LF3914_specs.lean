-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def count_pairs_int (d : Nat) (m : Nat) : Nat := sorry

theorem count_pairs_int_non_negative (d m : Nat) (h : d > 0) (h2 : m > 1) :
  (count_pairs_int d m) ≥ 0 := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem count_pairs_int_zero_when_d_large (d m : Nat) (h : d > 0) (h2 : m > 1) (h3 : d ≥ m-1) :
  count_pairs_int d m = 0 := sorry

theorem count_pairs_int_upper_bound (d m : Nat) (h : d > 0) (h2 : m > 1) :
  count_pairs_int d m ≤ max 0 (m-d-1) := sorry

theorem count_pairs_int_small_m (d : Nat) (h : d > 0) :
  count_pairs_int d (d+1) = 0 ∧ count_pairs_int d d = 0 := sorry
-- </vc-theorems>