-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def band_name_generator (s : String) : String := sorry

theorem band_name_generator_first_char_is_capital (s : String) 
  (h : s.length > 0) :
  let result := band_name_generator s
  Char.isUpper (result.get 0) := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem band_name_generator_first_last_same (s : String)
  (h1 : s.length > 0)
  (h2 : s.front = s.back) :
  band_name_generator s = s.capitalize ++ s.drop 1 := sorry

theorem band_name_generator_first_last_different (s : String) 
  (h1 : s.length > 0)
  (h2 : s.front ≠ s.back) :
  band_name_generator s = "The " ++ s.capitalize := sorry
-- </vc-theorems>