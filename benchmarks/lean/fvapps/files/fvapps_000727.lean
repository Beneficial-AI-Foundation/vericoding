-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def minArraySize (height : Nat) : Nat := (2 ^ height) - 1

def calcMaxProduct (height : Nat) (values : List Nat) : Nat :=
sorry

def treeProduct (values : List Nat) (height : Nat) : Nat :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem calc_max_product_zero_height (values : List Nat) :
  calcMaxProduct 0 values = 0 := by
  sorry

theorem calc_max_product_bounds {height : Nat} {values : List Nat}
  (h1 : height > 0)
  (h2 : values.length ≥ minArraySize height) :
  0 ≤ calcMaxProduct height values ∧ calcMaxProduct height values < 1000000007 := by
  sorry

theorem tree_product_monotonic {height : Nat} {values : List Nat}
  (h1 : height > 0)
  (h2 : values.length ≥ minArraySize height)
  (h3 : ∀ x ∈ values, x > 0) :
  let scaledValues := values.map (· * 2)
  treeProduct scaledValues height > treeProduct values height := by
  sorry

theorem min_array_size_valid (height : Nat) :
  minArraySize height = 2^height - 1 := by
  sorry
-- </vc-theorems>