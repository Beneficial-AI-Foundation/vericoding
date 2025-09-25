-- <vc-preamble>
def countMaxOccurrences (arr : List Int) : Nat :=
  let counts := arr.map (λ x => arr.count x)
  counts.foldl Nat.max 0
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def longestArithSeqLength (arr : List Int) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem min_length_at_least_two {arr : List Int} (h : arr.length ≥ 1) :
  longestArithSeqLength arr ≥ 2 :=
sorry

theorem dupes_counted_properly {arr : List Int} (h : arr.length ≥ 2) :
  longestArithSeqLength arr ≥ countMaxOccurrences arr :=
sorry

theorem arithmetic_sequence_preserved {arr : List Int} (h₁ : arr.length ≥ 3) (h₂ : arr.length ≤ 10) :
  let diff := arr[1]! - arr[0]!
  let arithSeq := (List.range arr.length).map (λ i => arr[0]! + diff * (Int.ofNat i))
  longestArithSeqLength arithSeq = arithSeq.length :=
sorry

theorem reverse_same_result {arr : List Int} (h : arr.length ≥ 2) :
  longestArithSeqLength arr = longestArithSeqLength arr.reverse :=
sorry
-- </vc-theorems>