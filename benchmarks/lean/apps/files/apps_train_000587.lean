-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def modifyList {α} (xs : List α) (i : Nat) (v : α) : List α := sorry

def check_grid_stability (grid : List (List Nat)) (rows cols : Nat) : String := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem corner_cells_stability {n : Nat} (h : n ≥ 2) :
  let grid₁ := List.replicate n (List.replicate n 0)
  let grid₂ := modifyList grid₁ 0 (modifyList (List.get! grid₁ 0) 0 2)
  let grid₃ := modifyList grid₁ 0 (modifyList (List.get! grid₁ 0) 0 1)
  check_grid_stability grid₂ n n = "Unstable" ∧
  check_grid_stability grid₃ n n = "Stable" := sorry

theorem center_cells_stability {n : Nat} (h : n ≥ 3) :
  let grid₁ := List.replicate n (List.replicate n 0)
  let center := n / 2
  let grid₂ := modifyList grid₁ center (modifyList (List.get! grid₁ center) center 4)
  let grid₃ := modifyList grid₁ center (modifyList (List.get! grid₁ center) center 3)
  check_grid_stability grid₂ n n = "Unstable" ∧
  check_grid_stability grid₃ n n = "Stable" := sorry

theorem arbitrary_grid_stability (grid : List (List Nat)) :
  grid ≠ [] →
  (List.get! grid 0) ≠ [] →
  (∀ row ∈ grid, row.length = (List.get! grid 0).length) →
  (∀ row ∈ grid, ∀ x ∈ row, x ≤ 4) →
  let rows := grid.length
  let cols := (List.get! grid 0).length
  check_grid_stability grid rows cols = "Stable" ∨
  check_grid_stability grid rows cols = "Unstable" := sorry

/-
info: 'Stable'
-/
-- #guard_msgs in
-- #eval check_grid_stability [[1, 2, 1], [2, 3, 2], [1, 2, 1]] 3 3

/-
info: 'Unstable'
-/
-- #guard_msgs in
-- #eval check_grid_stability [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 4, 0]] 3 4

/-
info: 'Unstable'
-/
-- #guard_msgs in
-- #eval check_grid_stability [[1, 1, 1], [1, 4, 1], [1, 1, 1]] 3 3
-- </vc-theorems>

-- Apps difficulty: interview
-- Assurance level: unguarded