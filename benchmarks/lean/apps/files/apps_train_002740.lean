-- <vc-helpers>
-- </vc-helpers>

def could_be (s1 s2 : String) : Bool := sorry

theorem empty_target_is_false (s1 s2 : String) :
  s2.trim = "" → could_be s1 s2 = false := sorry

theorem subset_name_property (first middle last : String) (h : first ≠ "") :
  could_be (s!"{first} {middle} {last}") (s!"{first} {last}") = true := sorry

theorem basic_case_exact_match :
  could_be "John Smith" "John Smith" = true := sorry

theorem basic_case_case_insensitive :
  could_be "John Smith" "john smith" = true := sorry

theorem basic_case_hyphen_match :
  could_be "John-Smith" "John-Smith" = true := sorry

theorem basic_case_hyphen_mismatch :
  could_be "John-Smith" "John Smith" = false := sorry

/-
info: True
-/
-- #guard_msgs in
-- #eval could_be "Carlos Ray Norris" "Carlos Ray Norris"

/-
info: True
-/
-- #guard_msgs in
-- #eval could_be "Carlos Ray Norris" "Carlos. Ray; Norris,"

/-
info: False
-/
-- #guard_msgs in
-- #eval could_be "Carlos-Ray Norris" "Carlos Ray Norris"

-- Apps difficulty: introductory
-- Assurance level: unguarded