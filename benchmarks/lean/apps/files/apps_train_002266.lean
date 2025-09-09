def solve_leaf_removal (n k : Nat) (edges : List (Nat × Nat)) : Nat :=
  sorry

-- <vc-helpers>
-- </vc-helpers>

def is_valid_tree (n : Nat) (edges : List (Nat × Nat)) : Bool :=
  sorry

theorem leaf_removal_basic_properties {n k : Nat} {edges : List (Nat × Nat)} 
    (h1 : n ≥ 2)
    (h2 : k ≥ 1) 
    (h3 : k ≤ 5)
    (h4 : is_valid_tree n edges = true) :
    let result := solve_leaf_removal n k edges
    result ≥ 0 ∧ result ≤ (n + k - 1) / k :=
  sorry

theorem leaf_removal_single_node {k : Nat}
    (h : k ≥ 1) :
    solve_leaf_removal 1 k [] = 0 := 
  sorry

/-
info: 2
-/
-- #guard_msgs in
-- #eval solve_leaf_removal 8 3 [(1, 2), (1, 5), (7, 6), (6, 8), (3, 1), (6, 4), (6, 1)]

/-
info: 3
-/
-- #guard_msgs in
-- #eval solve_leaf_removal 10 3 [(1, 2), (1, 10), (2, 3), (1, 5), (1, 6), (2, 4), (7, 10), (10, 9), (8, 10)]

/-
info: 4
-/
-- #guard_msgs in
-- #eval solve_leaf_removal 5 1 [(1, 2), (2, 3), (4, 3), (5, 3)]

-- Apps difficulty: introductory
-- Assurance level: unguarded