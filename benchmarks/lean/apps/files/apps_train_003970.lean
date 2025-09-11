-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def find_dup (arr : List Nat) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem find_dup_minimal :
  find_dup [1, 1] = 1 :=
  sorry

/-
info: 1
-/
-- #guard_msgs in
-- #eval find_dup [1, 1, 2, 3]

/-
info: 2
-/
-- #guard_msgs in
-- #eval find_dup [1, 2, 2, 3]

/-
info: 1
-/
-- #guard_msgs in
-- #eval find_dup [5, 4, 3, 2, 1, 1]
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible