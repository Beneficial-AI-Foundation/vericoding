-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve_tree_trimming (n : Nat) (parents : List Nat) : Nat :=
  sorry

def is_valid_tree (n : Nat) (parents : List Nat) : Bool :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem tree_trimming_bounds {n : Nat} {parents : List Nat}
  (h1 : n ≥ 2) (h2 : is_valid_tree n parents = true) :
  let result := solve_tree_trimming n parents
  1 ≤ result ∧ result ≤ n :=
sorry

theorem small_tree_optimum {n : Nat} {parents : List Nat}
  (h1 : n ≥ 2) (h2 : n ≤ 3) (h3 : is_valid_tree n parents = true) :
  solve_tree_trimming n parents = n :=
sorry

theorem line_tree_bounds {n : Nat}
  (h : n ≥ 2) :
  let parents := List.range (n-1)
  let result := solve_tree_trimming n parents
  1 ≤ result ∧ result ≤ n :=
sorry

theorem star_tree_bounds {n : Nat}
  (h : n ≥ 2) :
  let parents := List.replicate (n-1) 1
  let result := solve_tree_trimming n parents
  1 ≤ result ∧ result ≤ n :=
sorry
-- </vc-theorems>