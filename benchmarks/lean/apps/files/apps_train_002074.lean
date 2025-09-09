-- <vc-helpers>
-- </vc-helpers>

def count_pairs_with_mod (n : Nat) (p : Nat) (k : Nat) (numbers : List Nat) : Nat :=
  sorry

theorem empty_list_zero_pairs (p : Nat) (h: p ≥ 2) :
  count_pairs_with_mod 0 p 0 [] = 0 :=
  sorry

/-
info: 1
-/
-- #guard_msgs in
-- #eval count_pairs_with_mod 3 3 0 [0, 1, 2]

/-
info: 3
-/
-- #guard_msgs in
-- #eval count_pairs_with_mod 6 7 2 [1, 2, 3, 4, 5, 6]

/-
info: 1
-/
-- #guard_msgs in
-- #eval count_pairs_with_mod 5 5 3 [3, 0, 4, 1, 2]

-- Apps difficulty: competition
-- Assurance level: guarded_and_plausible