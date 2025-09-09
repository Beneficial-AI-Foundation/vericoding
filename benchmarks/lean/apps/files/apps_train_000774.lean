-- <vc-helpers>
-- </vc-helpers>

def count_graphs (n : Nat) (m : Nat) (distances : List Nat) : Nat :=
  sorry

theorem result_is_modulo (n : Nat) (distances : List Nat)
    (h1 : n ≥ 3) (h2 : distances.length ≥ 1) 
    (h3 : ∀ d ∈ distances, d ≥ 1 ∧ d ≤ 99) :
    let result := count_graphs n (n-1) distances
    0 ≤ result ∧ result ≤ 1000000007 :=
  sorry

theorem valid_distance_one (n : Nat) (h : n ≥ 3) :
    let distances := List.replicate (n-2) 1
    count_graphs n (n-1) distances = 1 :=
  sorry

theorem invalid_distances_return_zero (n : Nat) (h : n ≥ 3) :
    let distances := List.replicate (n-2) n
    count_graphs n (n-1) distances = 0 :=
  sorry

/-
info: 2
-/
-- #guard_msgs in
-- #eval count_graphs 4 3 [1, 2, 1]

/-
info: 0
-/
-- #guard_msgs in
-- #eval count_graphs 4 6 [1, 2, 1]

/-
info: 0
-/
-- #guard_msgs in
-- #eval count_graphs 3 2 [2, 2]

-- Apps difficulty: interview
-- Assurance level: unguarded