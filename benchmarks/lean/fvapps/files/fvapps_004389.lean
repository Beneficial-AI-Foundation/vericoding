-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def create_octahedron (size : Nat) : List (List (List Nat)) := sorry

theorem even_size_returns_empty (size : Int) :
  size > 0 ∧ size % 2 = 0 → create_octahedron size.toNat = [] := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem non_positive_returns_empty (size : Int) :
  size ≤ 0 → create_octahedron size.toNat = [] := sorry

theorem octahedron_size_properties {size : Nat} (h1 : size ≥ 3) (h2 : size ≤ 11) (h3 : size % 2 = 1) :
  let result := create_octahedron size
  let center := size / 2
  -- Size checks
  (result.length = size) ∧
  (∀ layer ∈ result, layer.length = size) ∧
  (∀ layer ∈ result, ∀ row ∈ layer, row.length = size) ∧
  -- Value checks (0 or 1)
  (∀ layer ∈ result, ∀ row ∈ layer, ∀ v ∈ row, v = 0 ∨ v = 1) ∧
  -- Center is 1
  ((result.get! center).get! center).get! center = 1 ∧
  -- Corners are 0
  ((result.get! 0).get! 0).get! 0 = 0 ∧
  ((result.get! 0).get! 0).get! (size-1) = 0 ∧
  ((result.get! 0).get! (size-1)).get! 0 = 0 ∧
  ((result.get! 0).get! (size-1)).get! (size-1) = 0 ∧
  ((result.get! (size-1)).get! 0).get! 0 = 0 ∧
  ((result.get! (size-1)).get! 0).get! (size-1) = 0 ∧
  ((result.get! (size-1)).get! (size-1)).get! 0 = 0 ∧
  ((result.get! (size-1)).get! (size-1)).get! (size-1) = 0 := sorry
-- </vc-theorems>