-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def longest_arithmetic_subsequence (arr: List Int) (diff: Int) : Nat :=
  sorry

def countOccurrences (xs : List Int) (x : Int) : Nat :=
  sorry

def maxOccurrences (xs : List Int) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem las_length_bounded {arr: List Int} {diff: Int} :
  arr ≠ [] → longest_arithmetic_subsequence arr diff ≤ arr.length :=
sorry

theorem las_non_negative {arr: List Int} {diff: Int} :
  arr ≠ [] → longest_arithmetic_subsequence arr diff ≥ 0 :=
sorry

theorem las_zero_diff {arr: List Int} :
  arr ≠ [] → longest_arithmetic_subsequence arr 0 = maxOccurrences arr :=
sorry

theorem las_reverse_symmetry {arr: List Int} {diff: Int} :
  arr ≠ [] → diff > 0 →
    longest_arithmetic_subsequence arr diff =
    longest_arithmetic_subsequence arr.reverse (-diff) :=
sorry
-- </vc-theorems>