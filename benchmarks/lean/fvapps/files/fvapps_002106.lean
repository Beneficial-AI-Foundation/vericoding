-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
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
-- </vc-theorems>