-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def MOD := 1000000007

def count_special_permutations (n : Nat) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem count_special_permutations_non_negative (n : Nat) (h : n > 0) : 
  count_special_permutations n ≥ 0 :=
  sorry

theorem count_special_permutations_one_is_zero :
  count_special_permutations 1 = 0 :=
  sorry

theorem count_special_permutations_two_is_zero :
  count_special_permutations 2 = 0 :=
  sorry

theorem count_special_permutations_positive_for_n_gt_two (n : Nat) (h : n > 2) :
  count_special_permutations n > 0 :=
  sorry
-- </vc-theorems>