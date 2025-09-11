-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def restore_permutation (n : Nat) (a : List Nat) : List Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem restore_perm_singleton : 
  restore_permutation 1 [0] = [1] :=
sorry

theorem restore_perm_pair :
  restore_permutation 2 [0, 1] = [1, 2] :=
sorry

/-
info: [3, 2, 1]
-/
-- #guard_msgs in
-- #eval restore_permutation 3 [0, 0, 0]

/-
info: [1, 2]
-/
-- #guard_msgs in
-- #eval restore_permutation 2 [0, 1]

/-
info: [1, 4, 3, 2, 5]
-/
-- #guard_msgs in
-- #eval restore_permutation 5 [0, 1, 1, 1, 10]
-- </vc-theorems>

-- Apps difficulty: competition
-- Assurance level: unguarded