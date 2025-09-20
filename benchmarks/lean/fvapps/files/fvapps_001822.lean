-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def isSequential (n: Nat) : Bool := sorry
def sequentialDigits (low high: Nat) : List Nat := sorry

-- Results should be between the given bounds
-- </vc-definitions>

-- <vc-theorems>
theorem result_between_bounds {low high : Nat} {n : Nat} (h: n ∈ sequentialDigits low high) : 
  low ≤ n ∧ n ≤ high := sorry

-- All returned numbers should have sequential digits

theorem all_sequential {low high : Nat} {n : Nat} (h: n ∈ sequentialDigits low high) :
  isSequential n = true := sorry

-- Results should be sorted ascending

theorem results_sorted {low high : Nat} {i j : Nat} (hi: i < (sequentialDigits low high).length) 
  (hj: j < (sequentialDigits low high).length) (h_lt: i < j) :
  (sequentialDigits low high)[i]! ≤ (sequentialDigits low high)[j]! := sorry

-- Edge case behavior

theorem edge_case_same_number_12 :
  sequentialDigits 12 12 = [12] := sorry

theorem edge_case_same_number_10 :
  sequentialDigits 10 10 = [] := sorry
-- </vc-theorems>