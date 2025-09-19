-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def am_i_wilson (n : Int) : Bool :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem am_i_wilson_output_is_bool (n : Int) :
  am_i_wilson n = true ∨ am_i_wilson n = false := by sorry

theorem am_i_wilson_known_wilson_primes :
  am_i_wilson 5 = true ∧ 
  am_i_wilson 13 = true ∧ 
  am_i_wilson 563 = true := by sorry

theorem am_i_wilson_non_wilson_primes (n : Int) :
  n ≠ 5 → n ≠ 13 → n ≠ 563 → am_i_wilson n = false := by sorry

theorem am_i_wilson_negative (n : Int) :
  n < 0 → am_i_wilson n = false := by sorry
-- </vc-theorems>