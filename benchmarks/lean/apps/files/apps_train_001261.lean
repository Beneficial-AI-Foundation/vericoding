-- <vc-helpers>
-- </vc-helpers>

def check_bed_arrangement (n : Nat) (grid : List (List Nat)) : String :=
  sorry

theorem empty_grid_safe {n : Nat} (h : 2 ≤ n) (h2 : n ≤ 10) :
  let grid := List.replicate n (List.replicate n 0)
  check_bed_arrangement n grid = "SAFE" :=
sorry

theorem single_bed_safe {n : Nat} (h : 2 ≤ n) (h2 : n ≤ 10) :
  let grid := List.replicate n (List.replicate n 0)
  check_bed_arrangement n grid = "SAFE" :=
sorry

theorem adjacent_horizontal_beds_unsafe {n : Nat} (h : 2 ≤ n) (h2 : n ≤ 10)
  (row : Nat) (col : Nat) :
  let row' := row % n
  let col' := col % (n-1)
  let grid := List.replicate n (List.replicate n 0)
  check_bed_arrangement n grid = "UNSAFE" :=
sorry

theorem adjacent_vertical_beds_unsafe {n : Nat} (h : 2 ≤ n) (h2 : n ≤ 10)
  (row : Nat) (col : Nat) :
  let row' := row % (n-1)
  let col' := col % n
  let grid := List.replicate n (List.replicate n 0)
  check_bed_arrangement n grid = "UNSAFE" :=
sorry

theorem diagonal_beds_safe {n : Nat} (h : 2 ≤ n) (h2 : n ≤ 10) :
  let grid := List.replicate n (List.replicate n 0)
  check_bed_arrangement n grid = "SAFE" :=
sorry

/-
info: 'SAFE'
-/
-- #guard_msgs in
-- #eval check_bed_arrangement 4 [[1, 0, 1, 0], [0, 0, 0, 1], [0, 1, 0, 0], [1, 0, 0, 1]]

/-
info: 'UNSAFE'
-/
-- #guard_msgs in
-- #eval check_bed_arrangement 4 [[1, 0, 1, 0], [0, 0, 0, 0], [1, 0, 1, 1], [0, 1, 0, 0]]

/-
info: 'SAFE'
-/
-- #guard_msgs in
-- #eval check_bed_arrangement 2 [[1, 0], [0, 1]]

-- Apps difficulty: interview
-- Assurance level: unguarded