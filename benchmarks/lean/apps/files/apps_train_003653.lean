-- <vc-helpers>
-- </vc-helpers>

def cycle (s : List Int) : List Int := sorry

theorem cycle_empty_for_short_sequences {s : List Int} 
  (h : s.length ≤ 1) :
  cycle s = [] := sorry

/-
info: [0, 3]
-/
-- #guard_msgs in
-- #eval cycle [2, 3, 4, 2, 3, 4]

/-
info: [1, 3]
-/
-- #guard_msgs in
-- #eval cycle [1, 2, 3, 4, 2, 3, 4]

/-
info: [0, 1]
-/
-- #guard_msgs in
-- #eval cycle [1, 1, 1, 1, 1]

/-
info: []
-/
-- #guard_msgs in
-- #eval cycle []

/-
info: []
-/
-- #guard_msgs in
-- #eval cycle [7]

/-
info: []
-/
-- #guard_msgs in
-- #eval cycle [1, 2, 3, 4]

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible