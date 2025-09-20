-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def find_max_diff_subsequence (arr : List Int) : List Int :=
  sorry

inductive IsSubsequence : List Int → List Int → Prop where
  | nil {arr : List Int} : IsSubsequence [] arr
  | cons {x : Int} {sub arr : List Int} :
    x ∈ arr →
    IsSubsequence sub (arr.dropWhile (· ≠ x)) →
    IsSubsequence (x::sub) arr

-- First element and last element are preserved
-- </vc-definitions>

-- <vc-theorems>
theorem first_and_last_preserved {arr : List Int} (h : arr.length ≥ 2) :
  let result := find_max_diff_subsequence arr
  result.head? = arr.head? ∧ result.getLast? = arr.getLast? :=
  sorry

-- Result is a subsequence of the input

theorem is_subsequence {arr : List Int} (h : arr.length ≥ 2) :
  let result := find_max_diff_subsequence arr
  IsSubsequence result arr :=
  sorry
-- </vc-theorems>