-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def count_non_friend_pairs (n m : Nat) (pairs : List (Nat × Nat)) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem count_empty_pairs {n : Nat} (h1 : n > 0) (h2 : n ≤ 20) :
  count_non_friend_pairs n 0 [] = n * (n-1) / 2 :=
  sorry

theorem count_single_node :
  count_non_friend_pairs 1 0 [] = 0 :=
  sorry

theorem count_empty_graph {n : Nat} (h1 : n ≥ 2) (h2 : n ≤ 20) :
  count_non_friend_pairs n 0 [] = n * (n-1) / 2 :=
  sorry

/-
info: 6
-/
-- #guard_msgs in
-- #eval count_non_friend_pairs 5 3 [(1, 2), (3, 4), (1, 5)]

/-
info: 4
-/
-- #guard_msgs in
-- #eval count_non_friend_pairs 4 2 [(1, 2), (3, 4)]

/-
info: 3
-/
-- #guard_msgs in
-- #eval count_non_friend_pairs 3 0 []
-- </vc-theorems>

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible