-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def passer_rating (att yds comp td ints : Nat) : Float :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem passer_rating_bounds (att yds comp td ints : Nat) (h : att > 0) :
  let rating := passer_rating att yds comp td ints
  0 ≤ rating ∧ rating ≤ 158.3 := sorry

theorem completions_less_than_attempts (att yds comp td ints : Nat) :
  comp ≤ att → passer_rating att yds comp td ints = passer_rating att yds comp td ints := sorry

theorem terrible_rating_conditions (att : Nat) (h : att > 0) :
  let rating := passer_rating att 0 0 0 att
  rating < 10 := sorry

/-
info: 112.2
-/
-- #guard_msgs in
-- #eval passer_rating 432 3554 291 28 2

/-
info: 158.3
-/
-- #guard_msgs in
-- #eval passer_rating 5 76 4 1 0

/-
info: 39.6
-/
-- #guard_msgs in
-- #eval passer_rating 48 192 19 2 3
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: unguarded