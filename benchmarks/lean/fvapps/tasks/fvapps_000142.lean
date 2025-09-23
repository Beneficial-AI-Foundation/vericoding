-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def min_steps (n : Nat) : Nat := sorry

def isPrime (n : Nat) : Bool := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem min_steps_nonnegative (n : Nat) (h : n ≥ 1) : 
  min_steps n ≥ 0 := sorry

theorem min_steps_upper_bound (n : Nat) (h : n ≥ 2) :
  min_steps n ≤ n := sorry 

theorem min_steps_small_numbers :
  min_steps 1 = 0 ∧ 
  min_steps 2 = 2 ∧
  min_steps 4 = 4 := sorry
-- </vc-theorems>