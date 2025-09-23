-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def can_create_pattern (n : Nat) (mat : Matrix) : Bool :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem empty_matrix_is_valid (n : Nat) (h : n > 0) :
  let mat := List.replicate n (List.replicate n '0')
  can_create_pattern n mat = true := by
  sorry

theorem single_edge_ones_are_valid (n : Nat) (h : n > 0) :
  let emptyMat := List.replicate n (List.replicate n '0')
  let lastRow := List.replicate n '1'
  let mat := List.take (n-1) emptyMat ++ [lastRow]
  can_create_pattern n mat = true := by
  sorry

theorem no_isolated_ones (n : Nat) (mat : Matrix) (h1 : n > 0)
  (h2 : mat.length = n)
  (h3 : ∀ row ∈ mat, row.length = n)
  (h4 : ∀ row ∈ mat, ∀ c ∈ row, c = '0' ∨ c = '1') :
  ∀ i j, i < n → j < n →
    (mat.get! i).get! j = '1' →
    (i = n-1 ∨ j = n-1 ∨ 
     (j < n-1 ∧ (mat.get! i).get! (j+1) = '1') ∨
     (i < n-1 ∧ (mat.get! (i+1)).get! j = '1')) ∨
    can_create_pattern n mat = false := by
  sorry

/-
info: True
-/
-- #guard_msgs in
-- #eval can_create_pattern 4 ["0010", "0011", "0000", "0000"]

/-
info: False
-/
-- #guard_msgs in
-- #eval can_create_pattern 2 ["10", "01"]

/-
info: True
-/
-- #guard_msgs in
-- #eval can_create_pattern 2 ["00", "00"]
-- </vc-theorems>