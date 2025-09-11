-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def cycle (n : Nat) : Int := sorry

theorem cycle_invalid_input (n : Nat)
  (h : n % 2 = 0 ∨ n % 5 = 0) : cycle n = -1 := sorry
-- </vc-definitions>

-- <vc-theorems>
/-
info: 2
-/
-- #guard_msgs in
-- #eval cycle 33

/-
info: -1
-/
-- #guard_msgs in
-- #eval cycle 94

/-
info: 98
-/
-- #guard_msgs in
-- #eval cycle 197
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible