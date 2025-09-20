-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def count_fours (nums : List Nat) : List Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem count_fours_length {nums : List Nat} :
  List.length (count_fours nums) = List.length nums :=
  sorry

theorem count_fours_nonnegative {nums : List Nat} :
  ∀ n ∈ count_fours nums, n ≥ 0 :=
  sorry

theorem count_fours_matches_digit {nums : List Nat} (i : Nat) (h : i < nums.length) :
  have h' : i < (count_fours nums).length := by
    rw [count_fours_length]
    exact h
  (count_fours nums)[i]'h' = ((toString (nums[i]'h)).toList.filter (· = '4')).length :=
  sorry

theorem count_fours_empty :
  count_fours [] = [] :=
  sorry
-- </vc-theorems>