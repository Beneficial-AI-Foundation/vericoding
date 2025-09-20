-- <vc-preamble>
def list_sum (xs : List Nat) : Nat :=
  xs.foldl (· + ·) 0
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def sum_float (xs : List Float) : Float := sorry

def solve_bucket_probability (N K : Nat) (arr : List (List Nat)) : List Float :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem bucket_probability_properties
  (N K : Nat) (arr : List (List Nat))
  (h1 : N > 0)
  (h2 : K > 0)
  (h3 : ∀ row ∈ arr, row.length = K ∧ list_sum row > 0)
  (result := solve_bucket_probability N K arr) :
  result.length = K ∧
  (sum_float result - 1).abs < 0.000001 ∧
  ∀ p ∈ result, 0 ≤ p ∧ p ≤ 1 :=
sorry

theorem bucket_single_bucket
  (result := solve_bucket_probability 1 1 [[1]]) :
  (result[0]! - 1).abs < 0.000001 :=
sorry

theorem bucket_equal_prob_1
  (result := solve_bucket_probability 1 2 [[1, 1]]) :
  ∀ r ∈ result, (r - 0.5).abs < 0.000001 :=
sorry

theorem bucket_equal_prob_2
  (result := solve_bucket_probability 2 2 [[1, 1], [1, 1]]) :
  ∀ r ∈ result, (r - 0.5).abs < 0.000001 :=
sorry
-- </vc-theorems>