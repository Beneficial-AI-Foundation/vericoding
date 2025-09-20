-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def string_expansion (s : String) : String := sorry

-- We can remove the first theorem since String type guarantees it's a string
-- </vc-definitions>

-- <vc-theorems>
theorem string_expansion_empty_string (s : String) :
  s = "" → string_expansion s = "" := sorry

theorem string_expansion_only_numbers (s : String) :
  s.all Char.isDigit → string_expansion s = "" := sorry

theorem string_expansion_fixed_cases :
  (string_expansion "3abc" = "aaabbbccc") ∧ 
  (string_expansion "3D2a5d2f" = "DDDaadddddff") ∧
  (string_expansion "0d0a" = "") ∧
  (string_expansion "" = "") := sorry
-- </vc-theorems>