-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def candy (ratings : List Nat) : Nat := sorry

theorem candy_empty :
  candy [] = 0 := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem candy_single (rating : Nat) :
  candy [rating] = 1 := sorry

/-
info: 5
-/
-- #guard_msgs in
-- #eval candy [1, 0, 2]

/-
info: 4
-/
-- #guard_msgs in
-- #eval candy [1, 2, 2]

/-
info: 0
-/
-- #guard_msgs in
-- #eval candy []
-- </vc-theorems>

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible