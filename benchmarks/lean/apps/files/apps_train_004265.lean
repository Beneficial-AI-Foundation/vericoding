-- <vc-helpers>
-- </vc-helpers>

def convergents_of_e (n : Nat) : Nat :=
  sorry

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

/-
info: 17
-/
-- #guard_msgs in
-- #eval convergents_of_e 10

/-
info: 125
-/
-- #guard_msgs in
-- #eval convergents_of_e 57

/-
info: 298
-/
-- #guard_msgs in
-- #eval convergents_of_e 125

/-
info: 938
-/
-- #guard_msgs in
-- #eval convergents_of_e 298

-- Apps difficulty: introductory
-- Assurance level: unguarded