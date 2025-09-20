-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def rounding (n : Int) (m : Int) : Int := sorry

theorem rounding_symmetry 
  {n : Int} {m : Int} (hm : m > 0) (hn : n ≥ -1000) (hn2 : n ≤ 1000) (hm2 : m ≤ 100) :
  rounding n m = rounding (2 * rounding n m - n) m := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem rounding_zero :
  rounding 0 1 = 0 := sorry

theorem result_near_input 
  {n m : Int} (hm : m > 0) (hn : n ≥ -100) (hn2 : n ≤ 100) (hm2 : m ≤ 10) :
  (rounding n m - n).natAbs ≤ m/2 := sorry
-- </vc-theorems>