-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def find_next_power (val : Nat) (pow : Nat) : Nat := sorry

theorem find_next_power_greater 
  (val : Nat) (pow : Nat)
  (h1 : val ≥ 1) (h2 : pow ≥ 2) (h3 : pow ≤ 8) :
  find_next_power val pow > val := sorry
-- </vc-definitions>

-- <vc-theorems>
-- </vc-theorems>