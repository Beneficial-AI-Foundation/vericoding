-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def mobius (n : Nat) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem mobius_output_range (n : Nat) (h : n > 0) : 
  mobius n = -1 ∨ mobius n = 0 ∨ mobius n = 1 :=
  sorry

theorem mobius_square_factors (n : Nat) (h : n > 1) :
  mobius (n * n) = 0 :=
  sorry
-- </vc-theorems>