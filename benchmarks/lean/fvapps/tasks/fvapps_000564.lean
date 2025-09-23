-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def print_pattern (n: Nat) : List (List Char) := sorry

theorem print_pattern_dimensions {n : Nat} (h : n > 0) :
  let result := print_pattern n
  List.length result = n ∧ 
  ∀ row ∈ result, List.length row = n := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem print_pattern_valid_chars {n : Nat} (h : n > 0) :
  let result := print_pattern n
  ∀ row ∈ result, ∀ c ∈ row, c = '1' ∨ c = ' ' := sorry

theorem print_pattern_border {n : Nat} (h : n > 0) :
  let result := print_pattern n
  (∀ j < n, (result.get! 0).get! j = '1') ∧
  (∀ j < n, (result.get! (n-1)).get! j = '1') ∧
  (∀ i < n, (result.get! i).get! 0 = '1') ∧
  (∀ i < n, (result.get! i).get! (n-1) = '1') := sorry

theorem print_pattern_diagonals {n : Nat} (h : n > 0) :
  let result := print_pattern n
  (∀ i < n, (result.get! i).get! i = '1') ∧
  (∀ i < n, (result.get! i).get! (n-1-i) = '1') := sorry

theorem print_pattern_minimum_size :
  print_pattern 1 = [['1']] := sorry

theorem print_pattern_symmetry {n : Nat} (h : n > 0) :
  let result := print_pattern n
  (∀ row ∈ result, row = List.reverse row) ∧
  result = List.reverse result := sorry
-- </vc-theorems>