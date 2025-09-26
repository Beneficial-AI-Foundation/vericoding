-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def count_paths (n m : Nat) (grid : Grid) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem count_paths_dimensions {n m : Nat} {grid : Grid} 
  (h1 : grid.length = n)
  (h2 : ∀ (row : List Char), row ∈ grid → row.length = m) :
  let result := count_paths n m grid
  0 ≤ result ∧ result ≤ 10^9+7 :=
sorry

theorem count_paths_blocked_start_end {n m : Nat} {grid : Grid}
  (h1 : grid.length = n) 
  (h2 : ∀ (row : List Char), row ∈ grid → row.length = m)
  (h3 : (grid.get! 0).get! 0 = 'R' ∨ (grid.get! (n-1)).get! (m-1) = 'R') :
  count_paths n m grid = 0 :=
sorry

theorem count_paths_single_row {n : Nat} 
  (grid : Grid)
  (h1 : grid.length = 1)
  (h2 : (grid.get! 0).length = n)
  (h3 : ∀ i < n, (grid.get! 0).get! i = '.') :
  count_paths 1 n grid = 1 :=
sorry

theorem count_paths_single_col {n : Nat}
  (grid : Grid) 
  (h1 : grid.length = n)
  (h2 : ∀ (row : List Char), row ∈ grid → row.length = 1)
  (h3 : ∀ i < n, (grid.get! i).get! 0 = '.') :
  count_paths n 1 grid = 1 :=
sorry

theorem count_paths_modulo {n m : Nat} {grid : Grid}
  (h1 : grid.length = n)
  (h2 : ∀ (row : List Char), row ∈ grid → row.length = m) :
  let result := count_paths n m grid
  0 ≤ result ∧ result < 10^9+7 :=
sorry

/-
info: 1
-/
-- #guard_msgs in
-- #eval count_paths 1 1 ["."]

/-
info: 0
-/
-- #guard_msgs in
-- #eval count_paths 2 3 ["...", "..R"]

/-
info: 4
-/
-- #guard_msgs in
-- #eval count_paths 4 4 ["...R", ".RR.", ".RR.", "R..."]
-- </vc-theorems>