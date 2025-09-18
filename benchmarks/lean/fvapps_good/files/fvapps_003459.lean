-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def fixed_points_perms (n k : Nat) : Nat := sorry

theorem fixed_points_perms_zero_when_k_gt_n (n k : Nat) :
  k > n → fixed_points_perms n k = 0 := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem fixed_points_perms_nonnegative (n k : Nat) :
  k ≤ n → fixed_points_perms n k ≥ 0 := sorry

theorem fixed_points_perms_all_elements_fixed (n : Nat) :
  fixed_points_perms n n = 1 := sorry

theorem fixed_points_perms_zero_case :
  fixed_points_perms 0 0 = 1 := sorry

theorem fixed_points_perms_recurrence (n k : Nat) :
  0 < k → k < n → 
  fixed_points_perms n k = fixed_points_perms (n-1) (k-1) * n / k := sorry
-- </vc-theorems>