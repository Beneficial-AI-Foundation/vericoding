-- <vc-helpers>
-- </vc-helpers>

def min_cuts_for_skyscrapers (n : Nat) (heights : List Nat) : Nat := sorry

theorem cuts_non_negative (n : Nat) (heights : List Nat) :
  min_cuts_for_skyscrapers n heights ≥ 0 := sorry

theorem single_building_no_cuts (h : Nat) :
  min_cuts_for_skyscrapers 1 [h] = 0 := sorry

theorem cuts_non_negative_multi (n : Nat) (heights : List Nat) :
  n ≥ 2 → min_cuts_for_skyscrapers n heights ≥ 0 := sorry

/-
info: 8
-/
-- #guard_msgs in
-- #eval min_cuts_for_skyscrapers 5 [1, 2, 3, 4, 5]

/-
info: 0
-/
-- #guard_msgs in
-- #eval min_cuts_for_skyscrapers 5 [5, 4, 3, 2, 1]

-- Apps difficulty: interview
-- Assurance level: unguarded