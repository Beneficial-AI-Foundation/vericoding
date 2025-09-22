-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def calc_max_sweetness (n k : Nat) : Nat := sorry

theorem calc_max_sweetness_positive (n k : Nat) (h1 : n > 0) (h2 : k > 0) : 
  calc_max_sweetness n k > 0 := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem calc_max_sweetness_upper_bound (n k : Nat) :
  calc_max_sweetness n k ≤ n * k := sorry

theorem calc_max_sweetness_multiple (n k : Nat) (h : k > 0) :
  calc_max_sweetness n k % k = 0 := sorry

theorem calc_max_sweetness_n_one (k : Nat) :
  calc_max_sweetness 1 k = k := sorry

theorem calc_max_sweetness_n_gt_one (n k : Nat) (h : n > 1) :
  calc_max_sweetness n k = ((n / 2) + (n % 2)) * k := sorry

theorem calc_max_sweetness_k_zero (n : Nat) :
  calc_max_sweetness n 0 = 0 := sorry

theorem calc_max_sweetness_step_two (k : Nat) :
  calc_max_sweetness 2 k - calc_max_sweetness 1 k = 0 := sorry

theorem calc_max_sweetness_step_three (k : Nat) :
  calc_max_sweetness 3 k - calc_max_sweetness 2 k = k := sorry
-- </vc-theorems>