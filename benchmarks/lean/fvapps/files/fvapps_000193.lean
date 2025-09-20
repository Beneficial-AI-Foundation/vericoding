-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def is_valid (s : String) : Bool := sorry

theorem valid_empty_string :
  is_valid "" = true := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem valid_after_abc_removal (s : String) :
  is_valid s = is_valid (s.replace "abc" "") := sorry

theorem valid_implies_empty_after_abc_removal {s : String} :
  is_valid s = true → 
  (let final := s.replace "abc" "";
   final = "") := sorry

theorem invalid_with_other_chars {s : String} :
  s.contains 'd' → 
  is_valid s = false := sorry

theorem valid_when_only_abc_remains {s : String} :
  s.replace "abc" "" = "" →
  is_valid s = true := sorry
-- </vc-theorems>