-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def climbStairs (n : Int) : Int := sorry

theorem climbStairs_positive (n : Int) (h : n ≥ 0) :
  climbStairs n > 0 := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem climbStairs_fibonacci (n : Int) (h : n ≥ 2) :
  climbStairs n = climbStairs (n-1) + climbStairs (n-2) := sorry

theorem climbStairs_base_cases :
  climbStairs 0 = 1 ∧ climbStairs 1 = 1 := sorry

theorem climbStairs_negative_undefined (n : Int) (h : n < 0) :
  False := sorry

theorem climbStairs_strictly_increasing (n : Int) (h : n ≥ 2) :
  climbStairs n > climbStairs (n-1) := sorry
-- </vc-theorems>