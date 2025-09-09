-- <vc-helpers>
-- </vc-helpers>

def symmetric_subscribers (eng : List Int) (french : List Int) : Nat := sorry

theorem symmetric_subscribers_non_negative 
  (eng : List Int) (french : List Int) : 
  symmetric_subscribers eng french ≥ 0 := sorry

theorem symmetric_subscribers_upper_bound 
  (eng : List Int) (french : List Int) :
  symmetric_subscribers eng french ≤ List.length eng + List.length french := sorry

theorem symmetric_subscribers_identical_lists
  (nums : List Int) :
  symmetric_subscribers nums nums = 0 := sorry

/-
info: 8
-/
-- #guard_msgs in
-- #eval symmetric_subscribers [1, 2, 3, 4, 5, 6, 7, 8, 9] [10, 1, 2, 3, 11, 21, 55, 6, 8]

/-
info: 4
-/
-- #guard_msgs in
-- #eval symmetric_subscribers [1, 2, 3] [3, 4, 5]

/-
info: 4
-/
-- #guard_msgs in
-- #eval symmetric_subscribers [1, 2] [3, 4]

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible