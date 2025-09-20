-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve_tree_dfs (n : Nat) (parents : List Nat := []) : List Float :=
sorry

def is_valid_tree (parents : List Nat) : Bool :=
sorry

def abs (x : Float) : Float :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem single_node_properties (n : Nat) (h : n = 1) :
  let result := solve_tree_dfs n
  (result.length = 1) ∧
  (abs (result[0]! - 1.0) < 0.000001) :=
sorry

theorem valid_tree_properties {n : Nat} {parents : List Nat}
  (h : is_valid_tree parents = true) :
  let result := solve_tree_dfs (n + 1) parents
  (result.length = n + 1) ∧
  (abs (result[0]! - 1.0) < 0.000001) ∧
  (∀ i p, i < parents.length → p = parents[i]! → result[i+1]! > result[p-1]!) ∧
  (∀ x, x ∈ result → x ≥ 1.0) ∧
  (∀ x, x ∈ result → x ≤ Float.ofNat (n + 1)) :=
sorry
-- </vc-theorems>