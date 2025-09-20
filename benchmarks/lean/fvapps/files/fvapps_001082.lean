-- <vc-preamble>
def array_max (arr : Array Int) : Int :=
  arr.foldl (fun acc x => max acc x) (-999999)

def matrix_max (matrix : Array (Array Int)) : Int :=
  matrix.foldl (fun acc row => max acc (array_max row)) (-999999)
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def abs (n : Int) : Int := sorry

def find_max_sum_submatrix (matrix : Array (Array Int)) : Array (Array Int) :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem singleton_matrix_is_own_max_sum
  (val : Int)
  (matrix : Array (Array Int))
  (h : matrix = #[#[val]]) :
  find_max_sum_submatrix matrix = #[#[val]] :=
sorry
-- </vc-theorems>