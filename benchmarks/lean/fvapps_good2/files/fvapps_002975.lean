-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def divisible_by_three (s : String) : Bool :=
  sorry

def digit_sum (s : String) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem divisible_by_three_matches_mod (n : Nat) :
  divisible_by_three (toString n) = (n % 3 = 0) :=
sorry

theorem divisible_by_three_digit_sum (n : Nat) :
  divisible_by_three (toString n) = (digit_sum (toString n) % 3 = 0) :=
sorry

theorem append_zeros_preserves_divisibility (n : Nat) (k : Nat) (h : 0 < k ∧ k ≤ 10) :
  divisible_by_three (toString n ++ String.mk (List.replicate k '0')) =
  divisible_by_three (toString n) :=
sorry
-- </vc-theorems>