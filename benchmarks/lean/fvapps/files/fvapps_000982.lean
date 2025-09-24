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
-- </vc-theorems>