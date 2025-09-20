-- <vc-preamble>
def sorted (xs : List Nat) : Prop :=
  ∀ i j, i < j → i < xs.length → j < xs.length →
    xs[i]! ≤ xs[j]!
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def count_inversions (arr : List Nat) (n : Nat) (m : Nat) : Nat :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem count_inversions_non_negative (arr : List Nat) (n : Nat) (m : Nat) :
  count_inversions arr n m ≥ 0 :=
sorry

theorem count_inversions_sorted_zero (arr : List Nat) (n : Nat) (m : Nat) :
  sorted arr → count_inversions arr n m = 0 :=
sorry

theorem count_inversions_scale_invariant (arr : List Nat) (n : Nat) (m : Nat) :
  count_inversions arr n m = count_inversions (List.map (· * 2) arr) n m :=
sorry

theorem count_inversions_monotone (arr : List Nat) (n : Nat) (m1 m2 : Nat) :
  m1 ≤ m2 → count_inversions arr n m1 ≤ count_inversions arr n m2 :=
sorry

theorem count_inversions_single_element (n m : Nat) (a : Nat) :
  count_inversions [a] n m = 0 :=
sorry

theorem count_inversions_same_elements (n m a : Nat) :
  count_inversions [a,a,a] n m = 0 :=
sorry
-- </vc-theorems>