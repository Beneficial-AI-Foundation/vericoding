-- <vc-preamble>
def Matrix (α : Type) := List (List α)

def swim_time (grid : Matrix Nat) : Nat := sorry
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def can_reach (t : Nat) (grid : Matrix Nat) (i j : Nat) (visited : List (Nat × Nat)) : Bool := sorry

theorem swim_time_non_negative (grid : Matrix Nat) : 
  swim_time grid ≥ 0 := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem swim_time_bounds {grid : Matrix Nat} (h : grid.length > 0) :
  swim_time grid ≥ (grid.head!.head!) ∧
  swim_time grid ≥ (grid.getLast!.getLast!) ∧
  swim_time grid ≤ grid.length * grid.length := sorry

theorem swim_time_monotonic {grid grid2 : Matrix Nat} {i j : Nat}
  (h1 : i < grid.length)
  (h2 : j < grid.length)
  (h3 : ∀ x y, x ≠ i ∨ y ≠ j → 
    (grid.get! x).get! y = (grid2.get! x).get! y)
  (h4 : (grid2.get! i).get! j = (grid.get! i).get! j + 1) :
  swim_time grid2 ≥ swim_time grid := sorry

theorem swim_time_path_exists (grid : Matrix Nat) : 
  can_reach (swim_time grid) grid 0 0 [] = true := sorry

/-
info: 3
-/
-- #guard_msgs in
-- #eval swim_time [[0, 2], [1, 3]]

/-
info: 16
-/
-- #guard_msgs in
-- #eval swim_time [[0, 1, 2, 3, 4], [24, 23, 22, 21, 5], [12, 13, 14, 15, 16], [11, 17, 18, 19, 20], [10, 9, 8, 7, 6]]

/-
info: 3
-/
-- #guard_msgs in
-- #eval swim_time [[0, 1], [2, 3]]
-- </vc-theorems>

-- Apps difficulty: interview
-- Assurance level: unguarded