-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def smallest (n: Nat) : Nat := sorry

theorem divides_up_to_n (n: Nat) (h: n > 0) :
  ∀ i, i > 0 → i ≤ n → (smallest n) % i = 0 := sorry
-- </vc-definitions>

-- <vc-theorems>
/-
info: 60
-/
-- #guard_msgs in
-- #eval smallest 5

/-
info: 2520
-/
-- #guard_msgs in
-- #eval smallest 10

/-
info: 360360
-/
-- #guard_msgs in
-- #eval smallest 15
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible