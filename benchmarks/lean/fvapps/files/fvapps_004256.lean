-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def max_collatz_length : Int → List Int
  | n => sorry
-- </vc-definitions>

-- <vc-theorems>
theorem non_positive_returns_empty {n : Int} (h : n ≤ 0) :
  max_collatz_length n = [] := sorry

theorem result_format {n : Int} (h : n > 0) (h2 : n ≤ 100) :
  let result := max_collatz_length n
  result.length = 2 ∧ 
  result[0]! ≤ n ∧
  result[1]! > 0 := sorry

theorem monotonic_lengths {n : Int} (h : n > 1) (h2 : n ≤ 100) :
  (max_collatz_length n)[1]! ≥ (max_collatz_length (n-1))[1]! := sorry

theorem base_case :
  max_collatz_length 1 = [1, 1] := sorry

theorem result_smaller_than_input {n : Int} (h : n > 0) :
  let result := max_collatz_length n
  result[0]! > 0 ∧ result[0]! ≤ n := sorry
-- </vc-theorems>