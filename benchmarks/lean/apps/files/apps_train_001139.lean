-- <vc-helpers>
-- </vc-helpers>

def solve_party_guests (n : Nat) (friends : List Nat) : Nat := sorry

theorem solve_party_guests_non_negative (n : Nat) (friends : List Nat) :
  n > 0 → solve_party_guests n friends ≥ 0 := sorry

theorem solve_party_guests_monotonic (n : Nat) (friends : List Nat) (a : Nat) :
  n > 0 → solve_party_guests (n + 1) (friends ++ [a]) ≥ solve_party_guests n friends := sorry

/-
info: 2
-/
-- #guard_msgs in
-- #eval solve_party_guests 2 [0, 0]

/-
info: 4
-/
-- #guard_msgs in
-- #eval solve_party_guests 6 [3, 1, 0, 0, 5, 5]

/-
info: 0
-/
-- #guard_msgs in
-- #eval solve_party_guests 3 [1, 2, 3]

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible