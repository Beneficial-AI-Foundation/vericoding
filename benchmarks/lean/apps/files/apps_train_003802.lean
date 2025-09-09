-- <vc-helpers>
-- </vc-helpers>

def string_to_int_list (s : String) : List Int := sorry

theorem string_to_int_list_preserves_list (nums : List Int) :
  let s := String.intercalate "," (nums.map toString)
  string_to_int_list s = nums :=
sorry

theorem string_to_int_list_extra_commas (nums : List Int) (h : nums ≠ []) :
  let s := (String.intercalate "," (nums.map toString)).replace "," ",,"
  string_to_int_list s = nums :=
sorry

theorem string_to_int_list_empty_cases :
  string_to_int_list "" = [] ∧ 
  string_to_int_list "," = [] ∧
  string_to_int_list ",,,," = [] :=
sorry

/-
info: [1, 2, 3, 4, 5]
-/
-- #guard_msgs in
-- #eval string_to_int_list "1,2,3,4,5"

/-
info: [1, 2, 3, 4, 5]
-/
-- #guard_msgs in
-- #eval string_to_int_list "1,2,3,,,4,,5,,,"

/-
info: []
-/
-- #guard_msgs in
-- #eval string_to_int_list ",,,,,,,,"

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible