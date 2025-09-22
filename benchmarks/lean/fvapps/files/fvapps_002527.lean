-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def convert_bits (a b : Int) : Int := sorry

theorem convert_from_zero_cases :
  (convert_bits 0 0 = 0) ∧ 
  (convert_bits 0 1 = 1) ∧
  (convert_bits 0 2 = 1) ∧ 
  (convert_bits 0 3 = 2) ∧
  (convert_bits 0 4 = 1) := sorry
-- </vc-definitions>

-- <vc-theorems>
-- </vc-theorems>