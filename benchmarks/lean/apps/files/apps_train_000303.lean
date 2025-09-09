-- <vc-helpers>
-- </vc-helpers>

def candy (ratings : List Nat) : Nat := sorry

theorem candy_empty :
  candy [] = 0 := sorry

theorem candy_single (rating : Nat) :
  candy [rating] = 1 := sorry

/-
info: 5
-/
-- #guard_msgs in
-- #eval candy [1, 0, 2]

/-
info: 4
-/
-- #guard_msgs in
-- #eval candy [1, 2, 2]

/-
info: 0
-/
-- #guard_msgs in
-- #eval candy []

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible