-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def min_turns_to_divisible_by_10 (n : Int) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem divisible_by_10_returns_0 (x : Int) :
  x ≥ 0 → x % 10 = 0 → min_turns_to_divisible_by_10 x = 0 :=
  sorry

theorem divisible_by_5_returns_1 (x : Int) :
  x ≥ 0 → x % 5 = 0 → x % 10 ≠ 0 → min_turns_to_divisible_by_10 x = 1 :=
  sorry 

theorem not_divisible_by_5_returns_neg_1 (x : Int) :
  x ≥ 0 → x % 5 ≠ 0 → min_turns_to_divisible_by_10 x = -1 :=
  sorry
-- </vc-theorems>