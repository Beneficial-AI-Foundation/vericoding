-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def single_digit (n : Nat) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem single_digit_result_bounds (n : Nat) :
  0 ≤ single_digit n ∧ single_digit n ≤ 9 :=
  sorry

theorem single_digit_fixed_point (n : Nat) :
  single_digit (single_digit n) = single_digit n :=
  sorry

theorem single_digit_identity (n : Nat) (h : n ≤ 9) :
  single_digit n = n :=
  sorry
-- </vc-theorems>