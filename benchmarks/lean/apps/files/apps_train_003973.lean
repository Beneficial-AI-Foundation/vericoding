-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def persistence (n : Nat) : Nat := sorry

def multiplyDigits (n : Nat) : Nat := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem persistence_non_negative (n : Nat) : persistence n ≥ 0 := sorry

theorem persistence_single_digit (n : Nat) : n < 10 → persistence n = 0 := sorry

/-
info: 3
-/
-- #guard_msgs in
-- #eval persistence 39

/-
info: 0
-/
-- #guard_msgs in
-- #eval persistence 4

/-
info: 4
-/
-- #guard_msgs in
-- #eval persistence 999
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible