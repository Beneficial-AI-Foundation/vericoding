-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def convergents_of_e (n : Nat) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem convergents_always_positive (n : Nat) (h : n > 0) :
  convergents_of_e n > 0 :=
  sorry

theorem convergents_returns_nat (n : Nat) (h : n > 0) :
  convergents_of_e n ≥ 0 :=
  sorry

theorem convergents_known_results :
  convergents_of_e 10 = 17 ∧ convergents_of_e 57 = 125 :=
  sorry

theorem convergents_digits_only (n : Nat) (h : n > 0) :
  ∃ k, convergents_of_e n < 10^k :=
  sorry
-- </vc-theorems>