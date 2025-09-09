-- <vc-helpers>
-- </vc-helpers>

def reverse (nums : List Int) : List Int := sorry

theorem reverse_length_preservation {nums : List Int} :
  (List.length (reverse nums)) = (List.length nums) := sorry

theorem reverse_nonempty_preservation {nums : List Int} :
  nums ≠ [] → reverse nums ≠ [] := sorry

theorem reverse_last_element_preservation {nums : List Int} (h : nums ≠ []) :
  List.getLast nums h = List.getLast (reverse nums) (reverse_nonempty_preservation h) := sorry

/-
info: expected1
-/
-- #guard_msgs in
-- #eval reverse [5, 2, 1]

/-
info: expected2
-/
-- #guard_msgs in
-- #eval reverse [84, 42, 21, 10, 2]

/-
info: expected3
-/
-- #guard_msgs in
-- #eval reverse [83, 47, 28, 16, 7]

-- Apps difficulty: introductory
-- Assurance level: unguarded