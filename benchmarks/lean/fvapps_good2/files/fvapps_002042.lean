-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def is_valid_tree (n : Nat) (parents : List Nat) : Bool :=
  sorry

def solve_tree_values (n : Nat) (parents : List Nat) (sums : List Int) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem single_node_tree (n : Int) (h : n > 0) :
  solve_tree_values 1 [] [n] = n :=
sorry

theorem star_tree_valid (n : Nat) (parents : List Nat) (values : List Int)
  (h1 : n ≥ 2)
  (h2 : parents.length = n - 1)
  (h3 : ∀ p ∈ parents, p = 1)
  (h4 : values.length = n)
  (h5 : is_valid_tree n parents = true) :
  let result := solve_tree_values n parents values
  if ∃ v ∈ values, v < 0
  then result ≥ -1
  else result ≥ values.get! 0 :=
sorry

theorem path_tree_valid (n : Nat) (parents : List Nat) (values : List Int)
  (h1 : n ≥ 2)
  (h2 : parents.length = n - 1)
  (h3 : values.length = n)
  (h4 : ∀ (i : Nat), i < parents.length → parents.get! i ≤ i + 1)
  (h5 : is_valid_tree n parents = true) :
  let result := solve_tree_values n parents values
  if ∃ v ∈ values, v < 0
  then result ≥ -1
  else result ≥ values.get! 0 :=
sorry
-- </vc-theorems>