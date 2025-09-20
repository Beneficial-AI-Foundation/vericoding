-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def MODULO := 1000000007

def solve_tree_splitting (n : Nat) (parents : List Nat) (colors : List Nat) : Nat := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem single_node_bounds (n : Nat) (h : 0 < n ∧ n ≤ 10) :
  let parents := List.replicate (n-1) 0
  let colors := List.replicate n 0
  let result := solve_tree_splitting n parents colors
  result ≥ 0 ∧ result < MODULO := sorry

theorem chain_tree_bounds (n : Nat) (colors : List Nat)
    (h1 : 1 < n ∧ n ≤ 20)
    (h2 : ∀ c ∈ colors, c = 0 ∨ c = 1)
    (h3 : colors.length = n) :
  let parents := List.range (n-1)
  let result := solve_tree_splitting n parents colors
  result ≥ 0 ∧ result < MODULO := sorry

theorem star_tree_bounds (n : Nat) (h : 1 < n ∧ n ≤ 20) :
  let parents := List.replicate (n-1) 0
  let colors := List.map (fun i => i % 2) (List.range n)
  let result := solve_tree_splitting n parents colors
  result ≥ 0 ∧ result < MODULO := sorry

theorem edge_cases :
  (solve_tree_splitting 2 [0] [0,1] ≥ 0) ∧
  (solve_tree_splitting 3 [0,0] [1,1,1] ≥ 0) ∧
  (solve_tree_splitting 3 [0,0] [0,0,0] ≥ 0) := sorry
-- </vc-theorems>