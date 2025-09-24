-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve_leaf_removal (n k : Nat) (edges : List (Nat × Nat)) : Nat :=
  sorry

def is_valid_tree (n : Nat) (edges : List (Nat × Nat)) : Bool :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
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
-- </vc-theorems>