-- <vc-helpers>
-- </vc-helpers>

def calc_max_happiness (N M : Nat) (distances : List Nat) (deliciousness : List (List Nat)) : Nat :=
  sorry

theorem max_happiness_nonnegative (N M : Nat) (distances : List Nat) (deliciousness : List (List Nat)) :
  calc_max_happiness N M distances deliciousness ≥ 0 := sorry

theorem max_happiness_is_nat (N M : Nat) (distances : List Nat) (deliciousness : List (List Nat)) :
  ∃ n : Nat, calc_max_happiness N M distances deliciousness = n := sorry

theorem zero_deliciousness_gives_zero (N M : Nat) (distances : List Nat) (deliciousness : List (List Nat))
  (h1 : N > 0)
  (h2 : M > 0)
  (h3 : distances.length = N - 1)
  (h4 : deliciousness.length = N)
  (h5 : ∀ l ∈ deliciousness, l.length = M) 
  (h6 : ∀ l ∈ deliciousness, ∀ x ∈ l, x = 0) :
  calc_max_happiness N M distances deliciousness = 0 := sorry

theorem doubled_distances_decrease_happiness (N M : Nat) (distances : List Nat) (deliciousness : List (List Nat)) 
  (doubled_distances : List Nat)
  (h : doubled_distances = distances.map (· * 2)) :
  calc_max_happiness N M doubled_distances deliciousness ≤ calc_max_happiness N M distances deliciousness := sorry

/-
info: 11
-/
-- #guard_msgs in
-- #eval calc_max_happiness 3 4 [1, 4] [[2, 2, 5, 1], [1, 3, 3, 2], [2, 2, 5, 1]]

/-
info: 20
-/
-- #guard_msgs in
-- #eval calc_max_happiness 5 3 [1, 2, 3, 4] [[10, 1, 1], [1, 1, 1], [1, 10, 1], [1, 1, 1], [1, 1, 10]]

-- Apps difficulty: competition
-- Assurance level: unguarded