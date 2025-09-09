-- <vc-helpers>
-- </vc-helpers>

def triple_double (n1 n2 : Nat) : Nat :=
  sorry

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

/-
info: 1
-/
-- #guard_msgs in
-- #eval triple_double 451999277 41177722899

/-
info: 0
-/
-- #guard_msgs in
-- #eval triple_double 1222345 12345

/-
info: 1
-/
-- #guard_msgs in
-- #eval triple_double 666789 12345667

-- Apps difficulty: introductory
-- Assurance level: unguarded