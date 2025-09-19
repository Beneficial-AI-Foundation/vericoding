-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def merge (line : List Nat) : List Nat := sorry

theorem merge_preserves_length (line : List Nat) (h : line ≠ []) :
  List.length (merge line) = List.length line := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem zeros_preserved (n : Nat) (h : n > 0) :
  merge (List.replicate n 0) = List.replicate n 0 := sorry

theorem trailing_zeros_preserved (line : List Nat) (h : line ≠ []) :
  let result := merge line
  let nonZeroCount := (result.filter (· ≠ 0)).length
  result.drop nonZeroCount = List.replicate (line.length - nonZeroCount) 0 := sorry

theorem merged_values_are_doubles (line : List Nat) (h₁ : line ≠ []) 
    (h₂ : ∀ x ∈ line, x ≤ 1000) :
  let result := merge line
  ∀ x ∈ result, x = 0 ∨ x ∈ line ∨ (x/2) ∈ line := sorry

theorem sum_relationship (line : List Nat) (h : line ≠ []) :
  let input_sum := line.foldl (·+·) 0
  let output_sum := (merge line).foldl (·+·) 0
  output_sum ≥ input_sum ∧ (output_sum - input_sum) % 2 = 0 := sorry
-- </vc-theorems>