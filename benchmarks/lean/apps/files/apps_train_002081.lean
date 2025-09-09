def Action : Type := (String × Nat)
def Actions : Type := List Action

-- <vc-helpers>
-- </vc-helpers>

def solve_order_book (actions: Actions) : Nat := sorry

theorem solve_multiple_possibilities :
  let test_actions := [("ADD", 5), ("ADD", 5), ("ACCEPT", 5)]
  solve_order_book test_actions = 2 := sorry

/-
info: 8
-/
-- #guard_msgs in
-- #eval solve_order_book [("ADD", 1), ("ACCEPT", 1), ("ADD", 2), ("ACCEPT", 2), ("ADD", 3), ("ACCEPT", 3)]

/-
info: 2
-/
-- #guard_msgs in
-- #eval solve_order_book [("ADD", 1), ("ADD", 2), ("ADD", 3), ("ACCEPT", 2)]

/-
info: 0
-/
-- #guard_msgs in
-- #eval solve_order_book [("ADD", 1), ("ADD", 2), ("ADD", 3), ("ADD", 4), ("ADD", 5), ("ACCEPT", 3), ("ACCEPT", 5)]

-- Apps difficulty: competition
-- Assurance level: guarded_and_plausible