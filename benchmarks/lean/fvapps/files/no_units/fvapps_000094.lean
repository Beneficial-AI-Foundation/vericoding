-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve_uneven_digit (n: Nat) : Int :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem solve_uneven_digit_one :
  solve_uneven_digit 1 = -1 := by
  sorry

theorem solve_uneven_digit_two :
  solve_uneven_digit 2 = 23 := by
  sorry

theorem solve_uneven_digit_positive (n: Nat) (h: n > 1) :
  solve_uneven_digit n > 0 := by
  sorry

theorem solve_uneven_digit_length (n: Nat) (h: n > 1) :
  (toString (solve_uneven_digit n).natAbs).length = n := by
  sorry

theorem solve_uneven_digit_no_zeros (n: Nat) (h: n > 1) :
  ¬((toString (solve_uneven_digit n).natAbs).contains '0') := by
  sorry

theorem solve_uneven_digit_not_divisible (n: Nat) (h: n > 1) (d: Char) :
  d ∈ (toString (solve_uneven_digit n).natAbs).data →
  ¬((solve_uneven_digit n).natAbs % (d.toNat - 48) = 0) := by
  sorry
-- </vc-theorems>