-- <vc-preamble>
def find_the_ball (start : Nat) (swaps : List (Nat × Nat)) : Nat :=
  sorry
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def iterateN (f : Nat → Nat) : Nat → Nat → Nat
  | 0, x => x
  | n+1, x => iterateN f n (f x)
-- </vc-definitions>

-- <vc-theorems>
theorem find_the_ball_no_swaps (start : Nat) :
  find_the_ball start [] = start :=
sorry

/-
info: 5
-/
-- #guard_msgs in
-- #eval find_the_ball 5 []

/-
info: 2
-/
-- #guard_msgs in
-- #eval find_the_ball 0 [(0, 1), (1, 2)]

/-
info: 3
-/
-- #guard_msgs in
-- #eval find_the_ball 0 [(0, 1), (1, 2), (2, 3)]
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible