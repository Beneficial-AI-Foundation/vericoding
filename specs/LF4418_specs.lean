-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def string_to_number (s : String) : Int := sorry

theorem string_to_number_roundtrip (n : Int) : 
  string_to_number (toString n) = n := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem string_to_number_invalid_empty :
  ∀ s : String, s = "" → string_to_number s = 0 := sorry

theorem string_to_number_invalid_nondigit (s : String)
  (h: ∃ c ∈ s.data, c < '0' ∨ c > '9') :
  string_to_number s = 0 := sorry
-- </vc-theorems>