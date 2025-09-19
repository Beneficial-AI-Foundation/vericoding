-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def find_kth_point (n : Nat) (k : Nat) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem result_bounded (n : Nat) (k : Nat) (h : k > 0) :
  let res := find_kth_point n k
  res ≤ n ∧ res ≥ 0 := by
  sorry

theorem first_point_divides_evenly (n : Nat) (h : n > 0) :
  find_kth_point n 1 = n / 2 := by 
  sorry

theorem second_point_divides_evenly (n : Nat) (h : n > 0) :
  find_kth_point n 2 = n / 4 := by
  sorry

theorem k_must_be_positive (n : Nat) :
  ∀ k : Nat, k = 0 → find_kth_point n k = find_kth_point n k → False := by
  sorry
-- </vc-theorems>