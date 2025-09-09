-- <vc-helpers>
-- </vc-helpers>

def trap (heights : List Nat) : Nat := sorry

theorem trap_empty : 
  trap [] = 0 := sorry

theorem trap_singleton (h : Nat) :
  trap [h] = 0 := sorry

theorem trap_valley (h : Nat) :
  h > 0 → trap [h, 0, h] = h := sorry

/-
info: 6
-/
-- #guard_msgs in
-- #eval trap [0, 1, 0, 2, 1, 0, 1, 3, 2, 1, 2, 1]

/-
info: 9
-/
-- #guard_msgs in
-- #eval trap [4, 2, 0, 3, 2, 5]

/-
info: 0
-/
-- #guard_msgs in
-- #eval trap []

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible