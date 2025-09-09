def count_inversions (arr : List Nat) (n : Nat) (m : Nat) : Nat := sorry

theorem count_inversions_non_negative (arr : List Nat) (n : Nat) (m : Nat) :
  count_inversions arr n m ≥ 0 := sorry

-- <vc-helpers>
-- </vc-helpers>

def sorted (xs : List Nat) : Prop :=
  ∀ i j, i < j → i < xs.length → j < xs.length → 
    xs[i]! ≤ xs[j]!

theorem count_inversions_sorted_zero (arr : List Nat) (n : Nat) (m : Nat) :
  sorted arr → count_inversions arr n m = 0 := sorry

theorem count_inversions_scale_invariant (arr : List Nat) (n : Nat) (m : Nat) :
  count_inversions arr n m = count_inversions (List.map (· * 2) arr) n m := sorry

theorem count_inversions_monotone (arr : List Nat) (n : Nat) (m1 m2 : Nat) :
  m1 ≤ m2 → count_inversions arr n m1 ≤ count_inversions arr n m2 := sorry

theorem count_inversions_single_element (n m : Nat) (a : Nat) :
  count_inversions [a] n m = 0 := sorry

theorem count_inversions_same_elements (n m a : Nat) :
  count_inversions [a,a,a] n m = 0 := sorry

/-
info: 12
-/
-- #guard_msgs in
-- #eval count_inversions [2, 1, 3] 3 3

/-
info: 30000
-/
-- #guard_msgs in
-- #eval count_inversions [99, 2, 1000, 24] 4 100

-- Apps difficulty: interview
-- Assurance level: unguarded