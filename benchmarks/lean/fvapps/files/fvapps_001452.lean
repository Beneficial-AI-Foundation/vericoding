-- <vc-preamble>
def make_zero_matrix (n m : Nat) : List String :=
  List.replicate n (String.mk (List.replicate m '0'))

def make_one_matrix (n m : Nat) : List String :=
  List.replicate n (String.mk (List.replicate m '1'))
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def String.replicate (n : Nat) (c : Char) : String :=
  sorry

def List.modifyNth {α : Type} (idx : Nat) (f : α → α) (xs : List α) : List α :=
  sorry

def process_matrix_queries (n m : Nat) (matrix : List String) (queries : List (List Nat)) : List String :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem empty_queries_preserves_matrix (n m : Nat) (matrix : List String)
    (h1 : n > 0) (h2 : m > 0) (h3 : n ≤ 10) (h4 : m ≤ 10)
    (h5 : matrix = make_zero_matrix n m) :
    process_matrix_queries n m matrix [] = matrix :=
sorry

theorem single_element_query_sets_one (n m : Nat) (matrix : List String)
    (h1 : n > 0) (h2 : m > 0) (h3 : n ≤ 5) (h4 : m ≤ 5)
    (h5 : matrix = make_zero_matrix n m)
    (i j : Nat) (h6 : i ≤ n) (h7 : j ≤ m) :
    process_matrix_queries n m matrix [[i, j, i, j]] =
    List.modifyNth (i - 1)
      (fun s => s.take (j - 1) ++ "1" ++ s.drop j)
      matrix :=
sorry

theorem full_matrix_query_sets_all_ones (n m : Nat) (matrix : List String)
    (h1 : n > 0) (h2 : m > 0) (h3 : n ≤ 5) (h4 : m ≤ 5)
    (h5 : matrix = make_zero_matrix n m) :
    process_matrix_queries n m matrix [[1, 1, n, m]] =
    make_one_matrix n m :=
sorry
-- </vc-theorems>