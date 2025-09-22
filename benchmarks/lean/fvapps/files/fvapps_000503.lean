-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def compare_and_calc (n1 n2 : Int) : Int := sorry

theorem compare_and_calc_spec (n1 n2 : Int) : 
  compare_and_calc n1 n2 = if n1 > n2 then n1 - n2 else n1 + n2 := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem compare_and_calc_same (n : Int) : 
  compare_and_calc n n = n + n := sorry
-- </vc-theorems>