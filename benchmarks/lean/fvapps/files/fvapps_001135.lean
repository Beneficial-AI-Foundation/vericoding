-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def M := 1000000007

def count_good_triplets (nums : List Nat) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem count_good_triplets_nonnegative (nums : List Nat) :
  count_good_triplets nums ≥ 0 :=
sorry

theorem count_good_triplets_empty :
  count_good_triplets [] = 0 :=
sorry

theorem count_good_triplets_singleton (n : Nat) :
  count_good_triplets [n] = 0 :=
sorry

theorem count_good_triplets_pair (n m : Nat) :
  count_good_triplets [n, m] = 0 :=
sorry

theorem count_good_triplets_all_ones_small (n : Nat) :
  n < 3 →
  count_good_triplets (List.replicate n 1) = 0 :=
sorry

theorem count_good_triplets_permutation_invariant (nums nums' : List Nat) :
  List.Perm nums nums' →
  count_good_triplets nums = count_good_triplets nums' :=
sorry
-- </vc-theorems>