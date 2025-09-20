-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def max_lcm_three_nums (n: Nat) : Nat := sorry

def lcm (a b: Nat) : Nat := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem small_cases :
  max_lcm_three_nums 1 = 1 ∧ 
  max_lcm_three_nums 2 = 2 ∧
  max_lcm_three_nums 3 = 6 := sorry
-- </vc-theorems>