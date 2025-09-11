-- <vc-preamble>
def int_to_negabinary (n : Int) : String := sorry
def negabinary_to_int (s : String) : Int := sorry
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def isValidBinaryStr (s : String) : Bool :=
  s.length > 0 && s.all (fun c => c = '0' || c = '1')
-- </vc-definitions>

-- <vc-theorems>
theorem round_trip (n : Int) : 
  negabinary_to_int (int_to_negabinary n) = n := sorry

theorem valid_binary_string (n : Int) :
  isValidBinaryStr (int_to_negabinary n) := sorry 

theorem neg_bin_str_converts (s : String) (h : isValidBinaryStr s) :
  ∃ n : Int, negabinary_to_int s = n := sorry

theorem zero_special_case :
  int_to_negabinary 0 = "0" := sorry

/-
info: '11010'
-/
-- #guard_msgs in
-- #eval int_to_negabinary 6

/-
info: 6
-/
-- #guard_msgs in
-- #eval negabinary_to_int "11010"

/-
info: '1110'
-/
-- #guard_msgs in
-- #eval int_to_negabinary -6

/-
info: -6
-/
-- #guard_msgs in
-- #eval negabinary_to_int "1110"

/-
info: '100'
-/
-- #guard_msgs in
-- #eval int_to_negabinary 4

/-
info: 4
-/
-- #guard_msgs in
-- #eval negabinary_to_int "100"
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: unguarded