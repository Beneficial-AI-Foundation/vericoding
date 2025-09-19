-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (n : Nat) (seq : List Nat) : List Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem result_elements_in_original {n : Nat} {seq : List Nat} (h : seq.length > 0) :
  let result := solve n seq
  ∀ x, x ∈ result → x ∈ seq :=
sorry

theorem result_preserves_first_occurrences {n : Nat} {seq : List Nat} (h : seq.length > 0) :
  let result := solve n seq
  let firstOccurrences := seq.foldl (λ acc x => if x ∈ acc then acc else acc ++ [x]) []
  result = firstOccurrences :=
sorry

theorem result_length_bounded {n : Nat} {seq : List Nat} (h : seq.length > 0) :
  let result := solve n seq
  result.length ≤ seq.length :=
sorry
-- </vc-theorems>