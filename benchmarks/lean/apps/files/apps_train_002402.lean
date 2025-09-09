-- <vc-helpers>
-- </vc-helpers>

def check_possibility (nums : List Int) : Bool := sorry

theorem single_element_valid {n : List Int} :
  n.length = 1 → check_possibility n = true := sorry

theorem two_elements_fixable {n : List Int} :
  n.length = 2 → check_possibility n = true := sorry

theorem sorted_list_valid {n : List Int} :
  (∀ i j, i < j → i < n.length → j < n.length → n[i]! ≤ n[j]!) →
  check_possibility n = true := sorry

theorem three_descending_not_fixable :
  check_possibility [3, 2, 1] = false := sorry

/-
info: True
-/
-- #guard_msgs in
-- #eval check_possibility [4, 2, 3]

/-
info: False
-/
-- #guard_msgs in
-- #eval check_possibility [4, 2, 1]

/-
info: True
-/
-- #guard_msgs in
-- #eval check_possibility [1, 2, 3]

-- Apps difficulty: introductory
-- Assurance level: unguarded