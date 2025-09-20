-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def tower_of_hanoi (n : Nat) : Nat := sorry

theorem tower_power_of_two (n : Nat) : 
  tower_of_hanoi n = 2^n - 1 := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem tower_positive (n : Nat) : 
  n > 0 → tower_of_hanoi n > 0 := sorry

theorem tower_more_than_double (n : Nat) :
  n > 0 → tower_of_hanoi n > 2 * tower_of_hanoi (n-1) := sorry

theorem tower_base_zero :
  tower_of_hanoi 0 = 0 := sorry

theorem tower_base_one :
  tower_of_hanoi 1 = 1 := sorry
-- </vc-theorems>