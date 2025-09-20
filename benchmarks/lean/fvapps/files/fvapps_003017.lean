-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def triple_double (n1 n2 : Nat) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem triple_double_returns_zero_or_one (n1 n2 : Nat) :
  triple_double n1 n2 = 0 ∨ triple_double n1 n2 = 1 :=
  sorry

theorem triple_double_basic_pattern (d : Nat) (h : d > 0 ∧ d ≤ 9) :
  triple_double (d * 111) (d * 11) = 1 :=
  sorry

theorem triple_double_with_surrounding (d : Nat) (h : d > 0 ∧ d ≤ 9) :
  triple_double (42000 + d * 111 + 57) (98000 + d * 11 + 32) = 1 :=
  sorry

theorem triple_double_no_triple (n1 n2 : Nat) :
  (∀ d : Nat, 0 ≤ d → d ≤ 9 → ¬ ∃ p : Nat, n1 = d * p) →
  triple_double n1 n2 = 0 :=
  sorry
-- </vc-theorems>