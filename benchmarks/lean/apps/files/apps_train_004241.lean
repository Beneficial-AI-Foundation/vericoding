-- <vc-helpers>
-- </vc-helpers>

def find (seq : List Int) : Int := sorry

theorem find_simple_sequence
    (start : Int) :
    find [start, start + 2, start + 6] = start + 4 := sorry

theorem find_symmetric_sequence
    (center : Int) :
    find [center - 4, center - 2, center + 2, center + 4] = center := sorry

/-
info: 7
-/
-- #guard_msgs in
-- #eval find [3, 9, 1, 11, 13, 5]

/-
info: 1
-/
-- #guard_msgs in
-- #eval find [5, -1, 0, 3, 4, -3, 2, -2]

/-
info: 0
-/
-- #guard_msgs in
-- #eval find [2, -2, 8, -8, 4, -4, 6, -6]

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible