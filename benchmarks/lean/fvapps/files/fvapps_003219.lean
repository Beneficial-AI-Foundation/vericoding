-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def name_in_str (text name : String) : Bool := sorry

theorem case_insensitivity (text name : String) :
  name_in_str text name = name_in_str text.toUpper name ∧
  name_in_str text name = name_in_str text name.toUpper ∧
  name_in_str text name = name_in_str text.toUpper name.toUpper := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem empty_name_true (text : String) :
  name_in_str text "" = true := sorry

theorem empty_string_false (name : String) :
  name ≠ "" → name_in_str "" name = false := sorry

theorem substring_implies_sequence (text name : String) :
  (∃ i : Nat, text.toLower.data.take i = name.toLower.data) → 
  name_in_str text name = true := sorry

theorem concatenation_property (text1 text2 name : String) :
  name_in_str text1 name ∨ name_in_str text2 name →
  name_in_str (text1 ++ text2) name = true := sorry
-- </vc-theorems>