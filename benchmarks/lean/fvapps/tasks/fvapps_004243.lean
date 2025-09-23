-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def reverse_number (n : Int) : Int := 
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem sign_preserved (x : Int) : 
  x ≥ 0 → reverse_number x ≥ 0 ∧ 
  x < 0 → reverse_number x < 0 := 
  sorry

theorem trailing_zeros_removed (x n : Nat) :
  x > 0 → 
  n ≥ 0 →
  n ≤ 5 →
  reverse_number (x * 10^n) = 
    reverse_number x :=
  sorry
-- </vc-theorems>