-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def any_odd (n : Nat) : Bool := sorry

def pattern := 0xAAAAAAAAAAAAAAAA
-- </vc-definitions>

-- <vc-theorems>
theorem any_odd_manual_calc {x : Nat} : 
  any_odd x = true ↔ ∃ i, x >>> (2*i + 1) &&& 1 = 1 := sorry 

theorem any_odd_pattern {x : Nat} :
  any_odd x = true ↔ (x &&& pattern) ≠ 0 := sorry

theorem any_odd_zero :
  any_odd 0 = false := sorry

theorem any_odd_agreement {x : Nat} :
  any_odd x = (x &&& pattern ≠ 0) := sorry
-- </vc-theorems>