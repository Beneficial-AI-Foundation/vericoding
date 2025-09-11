-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def count_triples_within_dist (n: Nat) (d: Nat) (points: List Int) : Nat := sorry

theorem count_is_non_negative (n: Nat) (d: Nat) (points: List Int) :
  count_triples_within_dist n d points ≥ 0 := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem increasing_distance_increases_count (n: Nat) (d: Nat) (points: List Int) :
  count_triples_within_dist n (2 * d) points ≥ count_triples_within_dist n d points := sorry 

theorem small_lists_give_zero (n: Nat) (d: Nat) (points: List Int) :
  n ≤ 2 → count_triples_within_dist n d points = 0 := sorry

/-
info: 4
-/
-- #guard_msgs in
-- #eval count_triples_within_dist 4 3 [1, 2, 3, 4]

/-
info: 2
-/
-- #guard_msgs in
-- #eval count_triples_within_dist 4 2 [-3, -2, -1, 0]

/-
info: 1
-/
-- #guard_msgs in
-- #eval count_triples_within_dist 5 19 [1, 10, 20, 30, 50]
-- </vc-theorems>

-- Apps difficulty: competition
-- Assurance level: guarded