/-
My friend wants a new band name for her band. She like bands that use the formula: "The" + a noun with the first letter capitalized, for example:

`"dolphin" -> "The Dolphin"`

However, when a noun STARTS and ENDS with the same letter, she likes to repeat the noun twice and connect them together with the first and last letter, combined into one word (WITHOUT "The" in front), like this:

`"alaska" -> "Alaskalaska"`

Complete the function that takes a noun as a string, and returns her preferred band name written as a string.
-/

-- <vc-helpers>
-- </vc-helpers>

def band_name_generator (s : String) : String := sorry

theorem band_name_generator_first_char_is_capital (s : String) 
  (h : s.length > 0) :
  let result := band_name_generator s
  Char.isUpper (result.get 0) := sorry

theorem band_name_generator_first_last_same (s : String)
  (h1 : s.length > 0)
  (h2 : s.front = s.back) :
  band_name_generator s = s.capitalize ++ s.drop 1 := sorry

theorem band_name_generator_first_last_different (s : String) 
  (h1 : s.length > 0)
  (h2 : s.front ≠ s.back) :
  band_name_generator s = "The " ++ s.capitalize := sorry

/-
info: 'The Knife'
-/
-- #guard_msgs in
-- #eval band_name_generator "knife"

/-
info: 'Tartart'
-/
-- #guard_msgs in
-- #eval band_name_generator "tart"

/-
info: 'The Bed'
-/
-- #guard_msgs in
-- #eval band_name_generator "bed"

-- Apps difficulty: introductory
-- Assurance level: unguarded