-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def sum (xs : List Int) : Int := xs.foldl (· + ·) 0

def diagonal_sum (matrix : List (List Int)) : Int := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem diagonal_sum_square_matrix (matrix : List (List Int)) : 
  let size := min (matrix.length) (matrix.map List.length |>.minimum?.getD 0)
  let square_matrix := matrix.take size |>.map (List.take size)
  diagonal_sum square_matrix = 
  sum ((List.range size).map (fun i => (square_matrix.get! i).get! i)) := sorry

theorem diagonal_sum_uniform_matrix (size : Nat) (value : Int) : 
  diagonal_sum (List.replicate size (List.replicate size value)) = 
  value * size := sorry

theorem diagonal_sum_bounds (matrix : List (List Int)) :
  !matrix.isEmpty →
  let size := min matrix.length (matrix.map List.length |>.minimum?.getD 0)
  let square_matrix := matrix.take size |>.map (List.take size)
  let min_val := (square_matrix.map (λ row => (row.minimum?.getD 0))).minimum?.getD 0
  let max_val := (square_matrix.map (λ row => (row.maximum?.getD 0))).maximum?.getD 0
  min_val * size ≤ diagonal_sum square_matrix ∧ 
  diagonal_sum square_matrix ≤ max_val * size := sorry

/-
info: 5
-/
-- #guard_msgs in
-- #eval diagonal_sum [[1, 2], [3, 4]]

/-
info: 15
-/
-- #guard_msgs in
-- #eval diagonal_sum [[1, 2, 3], [4, 5, 6], [7, 8, 9]]

/-
info: 34
-/
-- #guard_msgs in
-- #eval diagonal_sum [[1, 2, 3, 4], [5, 6, 7, 8], [9, 10, 11, 12], [13, 14, 15, 16]]
-- </vc-theorems>