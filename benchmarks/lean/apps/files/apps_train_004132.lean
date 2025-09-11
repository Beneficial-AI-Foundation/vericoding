-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def nth_smallest (arr : List Int) (pos : Nat) : Int := sorry

theorem last_smallest_is_max (arr : List Int) (h : arr.length > 0) :
  ∀ x ∈ arr, x ≤ nth_smallest arr arr.length := sorry
-- </vc-definitions>

-- <vc-theorems>
/-
info: 2
-/
-- #guard_msgs in
-- #eval nth_smallest [3, 1, 2] 2

/-
info: 7
-/
-- #guard_msgs in
-- #eval nth_smallest [15, 20, 7, 10, 4, 3] 3

/-
info: 2
-/
-- #guard_msgs in
-- #eval nth_smallest [2, 169, 13, -5, 0, -1] 4
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible