-- <vc-helpers>
-- </vc-helpers>

def h_index (citations : List Nat) : Nat := sorry

theorem h_index_empty : 
  h_index [] = 0 := sorry

/-
info: 3
-/
-- #guard_msgs in
-- #eval h_index [3, 0, 6, 1, 5]

/-
info: 0
-/
-- #guard_msgs in
-- #eval h_index [0]

/-
info: 1
-/
-- #guard_msgs in
-- #eval h_index [100]

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible