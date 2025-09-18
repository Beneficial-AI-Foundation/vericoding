-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve_remainder (a b c : Nat) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem solve_remainder_bounded
  (a b c : Nat)
  (h1 : a > 0)
  (h2 : b < a)
  (h3 : c > 0) :
  solve_remainder a b c ≤ c :=
sorry

theorem solve_remainder_mod
  (a b c : Nat)
  (h1 : a > 0)
  (h2 : b < a)
  (h3 : c > 0) :
  solve_remainder a b c % a = b :=
sorry

theorem solve_remainder_largest
  (a b c : Nat)
  (h1 : a > 0)
  (h2 : b < a)
  (h3 : c > 0) :
  let next := solve_remainder a b c + a
  next > c ∨ next % a ≠ b :=
sorry
-- </vc-theorems>