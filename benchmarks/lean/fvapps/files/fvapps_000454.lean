-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def minOperations (n : Nat) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem minOperations_nonnegative (n : Nat) :
  minOperations n ≥ 0 := sorry

theorem minOperations_one_zero :
  minOperations 1 = 0 := sorry  

theorem minOperations_positive (n : Nat) :
  n > 1 → minOperations n > 0 := sorry

theorem minOperations_upper_bound (n : Nat) :
  minOperations n ≤ n * n := sorry

theorem minOperations_approximates_nsquare_div_4 (n : Nat) (d : Float) :
  d = Float.abs (Float.ofNat (minOperations n) - Float.ofNat (n * n) / 4) →
  d < 1 := sorry
-- </vc-theorems>