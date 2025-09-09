-- <vc-helpers>
-- </vc-helpers>

def count_brown_regions (n : Nat) (grid : List String) : Nat := sorry

def empty_grid : List String := ["00000000", "00000000", "00000000", "00000000", 
                               "00000000", "00000000", "00000000", "00000000"]

theorem count_brown_regions_bounds {n : Nat} {grid : List String} 
  (h1 : n ≥ 3) : 
  0 ≤ count_brown_regions n grid ∧ count_brown_regions n grid < 21945 := sorry

theorem empty_grid_gives_zero : 
  count_brown_regions 3 empty_grid = 0 := sorry

theorem grid_constraints (grid : List String) 
  (h1 : grid.length = 8)
  (h2 : ∀ row ∈ grid, row.length = 8)
  (h3 : ∀ row ∈ grid, ∀ c ∈ row.data, c = '0' ∨ c = '1') :
  True := sorry

theorem output_modulo {n : Nat} {grid : List String}
  (h1 : n ≥ 3) :
  0 ≤ count_brown_regions n grid ∧ count_brown_regions n grid < 21945 := sorry

theorem idempotency {n : Nat} {grid : List String}
  (h1 : n ≥ 3) :
  count_brown_regions n grid = count_brown_regions n grid := sorry

/-
info: 6
-/
-- #guard_msgs in
-- #eval count_brown_regions 3 ["01000010", "11000001", "00000000", "00011000", "00011000", "00010100", "00001000", "00000000"]

/-
info: 22
-/
-- #guard_msgs in
-- #eval count_brown_regions 4 ["01000010", "11000001", "00000000", "00011000", "00011000", "00010100", "00001000", "00000000"]

/-
info: 1
-/
-- #guard_msgs in
-- #eval count_brown_regions 1000000000 ["11111111", "11111111", "11111111", "11111111", "11111111", "11111111", "11111111", "11111111"]

-- Apps difficulty: interview
-- Assurance level: unguarded