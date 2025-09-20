-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def pair_zeros (xs : List Int) : List Int := sorry

theorem pair_zeros_length_valid (xs : List Int) : 
  List.length (pair_zeros xs) ≤ List.length xs := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem pair_zeros_preserves_nonzero (xs : List Int) (x : Int) :
  x ∈ pair_zeros xs → x ≠ 0 → x ∈ xs := sorry

theorem pair_zeros_zero_count (xs : List Int) :
  let input_zeros := (xs.filter (· = 0)).length
  let output_zeros := ((pair_zeros xs).filter (· = 0)).length
  output_zeros = (input_zeros + 1) / 2 := sorry

theorem pair_zeros_preserves_ordering (xs : List Int) :
  (xs.filter (· ≠ 0)) = ((pair_zeros xs).filter (· ≠ 0)) := sorry
-- </vc-theorems>