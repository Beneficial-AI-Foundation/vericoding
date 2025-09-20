-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def maximum (l : List Int) : Int :=
  sorry

def minimum (l : List Int) : Int :=
  sorry

def min_difference_sum (n k : Nat) (arr : List Int) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem min_difference_sum_non_negative
  {n k : Nat} {arr : List Int}
  (h1 : n = arr.length)
  (h2 : k ≤ n)
  (h3 : n > 0) :
  min_difference_sum n k arr ≥ 0 :=
sorry

theorem min_difference_sum_upper_bound
  {n k : Nat} {arr : List Int}
  (h1 : n = arr.length)
  (h2 : k ≤ n)
  (h3 : n > 0) :
  min_difference_sum n k arr ≤ (maximum arr - minimum arr) * k :=
sorry

theorem min_difference_sum_k_equals_n
  {n k : Nat} {arr : List Int}
  (h1 : n = arr.length)
  (h2 : k = n)
  (h3 : n > 0) :
  min_difference_sum n k arr = 0 :=
sorry

theorem min_difference_sum_k_equals_one
  {n k : Nat} {arr : List Int}
  (h1 : n = arr.length)
  (h2 : k = 1)
  (h3 : n > 1) :
  min_difference_sum n k arr = maximum arr - minimum arr :=
sorry
-- </vc-theorems>