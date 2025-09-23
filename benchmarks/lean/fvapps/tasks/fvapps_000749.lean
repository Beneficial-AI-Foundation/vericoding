-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve_tree_mex (n : Nat) (parents : List Nat) : Nat :=
  sorry

def is_valid_tree (n : Nat) (parents : List Nat) : Bool :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem tree_mex_positive (n : Nat) (parents : List Nat) :
  is_valid_tree n parents → solve_tree_mex n parents > 0 :=
sorry

theorem tree_mex_ge_nodes (n : Nat) (parents : List Nat) :
  is_valid_tree n parents → solve_tree_mex n parents ≥ n :=
sorry

theorem tree_mex_monotonic (n : Nat) (parents : List Nat) :
  n > 2 →
  is_valid_tree n parents →
  solve_tree_mex n parents > solve_tree_mex (n-1) (parents.take (n-2)) :=
sorry

theorem line_tree_formula (n : Nat) :
  n ≥ 2 →
  solve_tree_mex n (List.map (fun i => i) (List.range (n-1))) = n * (n+1) / 2 :=
sorry
-- </vc-theorems>