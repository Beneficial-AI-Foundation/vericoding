-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def compute_matrix_a (n m k : Nat) (matrix_b : List (List Nat)) : List String := sorry

theorem identity_case {val : Nat} (h : val ≤ 100) :
  compute_matrix_a 1 1 1 [[val]] = [toString val] := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem oneByTwoByOne_case {val1 val2 : Nat} (h1 : val1 ≤ 100) (h2 : val2 ≤ 100) :
  let result := compute_matrix_a 1 2 1 [[val1], [val2]]
  result.length = 2 ∧ result.get! 0 = toString val1 := sorry
-- </vc-theorems>