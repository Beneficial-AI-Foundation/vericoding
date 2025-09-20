-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve_tree_distance_queries (n : Nat) (root : Nat) (edges : List (Nat × Nat × Nat × Nat)) 
  (queries : List (Nat × Nat × Nat × Nat)) : List Nat := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem star_tree_leaf_distance {n : Nat} (h1 : n ≥ 3) :
  let edges := List.range (n-1) |> List.map (fun i => (1, i+2, 1, 1))
  let queries := [(1, 1, 2, 3)]
  (solve_tree_distance_queries n 1 edges queries).head! = 2 := sorry

theorem star_tree_properties {n : Nat} (h1 : n ≥ 3) :
  let edges := List.range (n-1) |> List.map (fun i => (1, i+2, 1, 1))
  ∀ a b : Nat, 
    a ≠ 1 → b ≠ 1 → a ≤ n → b ≤ n →
    let queries := [(1, 1, a, b)]
    (solve_tree_distance_queries n 1 edges queries).head! = 2 := sorry
-- </vc-theorems>