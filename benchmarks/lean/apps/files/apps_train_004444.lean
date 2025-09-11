-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def is_int_array (xs : List Int) : Bool := sorry

theorem int_array_property (arr : List Int) : 
  is_int_array arr = true := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem int_array_from_int_list_property (arr : List Int) : 
  is_int_array arr = true := sorry

theorem not_list_property [Inhabited α] (x : α) :
  is_int_array ([] : List Int) = false := sorry

theorem empty_array_property :
  is_int_array ([] : List Int) = true := sorry

/-
info: True
-/
-- #guard_msgs in
-- #eval is_int_array []

/-
info: True
-/
-- #guard_msgs in
-- #eval is_int_array [1, 2, 3, 4]

/-
info: False
-/
-- #guard_msgs in
-- #eval is_int_array [1.0, 2.0, 3.0001]

/-
info: False
-/
-- #guard_msgs in
-- #eval is_int_array None

/-
info: False
-/
-- #guard_msgs in
-- #eval is_int_array ""
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: unguarded