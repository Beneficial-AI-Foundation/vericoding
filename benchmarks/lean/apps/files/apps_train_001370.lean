-- <vc-helpers>
-- </vc-helpers>

def MOD := (10^9) + 7

def getsum (n : Nat) : Nat :=
  sorry

theorem getsum_base_cases :
  (getsum 1 = 9) ∧ (getsum 2 = 99) :=
  sorry

theorem getsum_positive (n : Nat) (h : n > 0) :
  getsum n > 0 :=
  sorry

theorem getsum_invalid_input (n : Nat) :
  n = 0 → getsum n = 0 :=
  sorry

/-
info: 9
-/
-- #guard_msgs in
-- #eval getsum 1

/-
info: 99
-/
-- #guard_msgs in
-- #eval getsum 2

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible