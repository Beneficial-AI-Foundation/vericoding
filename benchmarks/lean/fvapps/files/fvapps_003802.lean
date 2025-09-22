-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def string_to_int_list (s : String) : List Int := sorry

theorem string_to_int_list_preserves_list (nums : List Int) :
  let s := String.intercalate "," (nums.map toString)
  string_to_int_list s = nums :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem string_to_int_list_extra_commas (nums : List Int) (h : nums ≠ []) :
  let s := (String.intercalate "," (nums.map toString)).replace "," ",,"
  string_to_int_list s = nums :=
sorry

theorem string_to_int_list_empty_cases :
  string_to_int_list "" = [] ∧ 
  string_to_int_list "," = [] ∧
  string_to_int_list ",,,," = [] :=
sorry
-- </vc-theorems>