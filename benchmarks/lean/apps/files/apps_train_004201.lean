-- <vc-helpers>
-- </vc-helpers>

def can_jump (arr : List Nat) : Bool := sorry

theorem single_element_array_no_jump {arr : List Nat} (h : arr.length = 1) : 
  ¬(can_jump arr) := sorry

theorem zero_first_element_no_jump {arr : List Nat} (h : arr.length ≥ 2) (h2 : arr.get? 0 = some 0) :
  ¬(can_jump arr) := sorry

theorem large_first_element_can_jump {arr : List Nat} (h : arr.length ≥ 2) 
  (h2 : arr.get? 0 = some (arr.length + 1)) :
  can_jump arr := sorry

/-
info: True
-/
-- #guard_msgs in
-- #eval can_jump [2, 5]

/-
info: False
-/
-- #guard_msgs in
-- #eval can_jump [5]

/-
info: True
-/
-- #guard_msgs in
-- #eval can_jump [3, 0, 2, 3]

-- Apps difficulty: introductory
-- Assurance level: unguarded