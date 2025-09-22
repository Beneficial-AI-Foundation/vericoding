-- <vc-preamble>
def listSum (xs : List Nat) : Nat :=
  match xs with
  | [] => 0
  | h::t => h + listSum t
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def Matrix (α : Type) := List (List α)

def count_squares (matrix : Matrix Int) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem all_ones_matrix_squares {m n : Nat} (h1 : m > 0) (h2 : n > 0) :
  let matrix := List.replicate m (List.replicate n 1)
  count_squares matrix = m * n
  :=
sorry

theorem binary_matrix_bounds (matrix : Matrix Int)
  (h1 : matrix ≠ []) :
  let result := count_squares matrix
  let m := matrix.length
  let n := (List.head! matrix).length
  result ≥ 0 ∧
  result ≤ m * n * (min m n)
  :=
sorry

theorem square_all_ones {n : Nat} (h : n > 0) :
  let matrix := List.replicate n (List.replicate n 1)
  count_squares matrix = n * (n + 1) * (2 * n + 1) / 6
  :=
sorry

theorem empty_and_edge_cases :
  count_squares [[0]] = 0 ∧
  count_squares [[1]] = 1 ∧
  count_squares [[0, 0], [0, 0]] = 0
  :=
sorry
-- </vc-theorems>