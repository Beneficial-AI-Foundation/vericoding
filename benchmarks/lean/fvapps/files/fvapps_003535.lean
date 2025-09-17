-- <vc-preamble>
def array_change (arr : List Int) : Nat :=
  sorry
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def sum (l : List Int) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem array_change_returns_nonnegative (arr : List Int) (h : arr.length ≥ 1) :
  array_change arr ≥ 0 :=
  sorry

/-
info: 3
-/
-- #guard_msgs in
-- #eval array_change [1, 1, 1]

/-
info: 5
-/
-- #guard_msgs in
-- #eval array_change [-1000, 0, -2, 0]

/-
info: 12
-/
-- #guard_msgs in
-- #eval array_change [2, 1, 10, 1]
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible