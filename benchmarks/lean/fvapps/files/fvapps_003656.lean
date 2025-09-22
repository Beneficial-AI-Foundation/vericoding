-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def close_to_zero (input : String) : Int := sorry

def abs (n : Int) : Int := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem close_to_zero_returns_from_input_or_zero 
  (nums : List Int) : 
  nums.isEmpty → close_to_zero (toString nums) = 0 ∧
  ¬nums.isEmpty → close_to_zero (toString nums) = 0 ∨ 
    close_to_zero (toString nums) ∈ nums := sorry

theorem empty_string_returns_zero : 
  close_to_zero "" = 0 := sorry
-- </vc-theorems>