-- <vc-helpers>
-- </vc-helpers>

def count_stars_in_region (grid : List (List Nat)) (x1 y1 x2 y2 : Nat) : Nat :=
  sorry

theorem grid_generation_full_sum (n m : Nat) (h1 : 1 ≤ n ∧ n ≤ 10) (h2 : 1 ≤ m ∧ m ≤ 10) :
  let grid := List.replicate n (List.replicate m 0)
  count_stars_in_region grid 1 1 n m = 0 :=
  sorry

theorem grid_generation_single_points (n m : Nat) (h1 : 1 ≤ n ∧ n ≤ 10) (h2 : 1 ≤ m ∧ m ≤ 10) :
  let grid := List.replicate n (List.replicate m 0)
  ∀ i j, 1 ≤ i ∧ i ≤ n → 1 ≤ j ∧ j ≤ m → 
    count_stars_in_region grid i j i j = 0 :=
  sorry

theorem count_stars_single_point (grid : List (List Nat)) (x y : Nat)
  (h1 : grid.length = 3) 
  (h2 : ∀ row ∈ grid, row.length = 3)
  (h3 : 1 ≤ x ∧ x ≤ 3)
  (h4 : 1 ≤ y ∧ y ≤ 3) :
  count_stars_in_region grid x y x y = grid.getLast!.getLast! :=
  sorry

theorem count_stars_full_region (grid : List (List Nat))
  (h1 : grid.length = 3)
  (h2 : ∀ row ∈ grid, row.length = 3) :
  count_stars_in_region grid 1 1 3 3 = grid.foldl (λ acc row => acc + row.foldl (λ x y => x + y) 0) 0 :=
  sorry

/-
info: 10
-/
-- #guard_msgs in
-- #eval count_stars_in_region [[10, 10, 10], [10, 10, 10], [10, 10, 10]] 1 1 1 1

/-
info: 90
-/
-- #guard_msgs in
-- #eval count_stars_in_region grid 1 1 3 3

/-
info: 60
-/
-- #guard_msgs in
-- #eval count_stars_in_region grid 2 1 3 3

/-
info: 30
-/
-- #guard_msgs in
-- #eval count_stars_in_region grid 3 1 3 3

-- Apps difficulty: interview
-- Assurance level: unguarded