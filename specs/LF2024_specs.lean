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
-- </vc-theorems>