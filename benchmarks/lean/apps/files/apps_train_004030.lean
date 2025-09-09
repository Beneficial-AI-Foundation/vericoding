def isSorted (l : List Int) : Prop :=
  ∀ i j, i < j → j < l.length → l[i]! ≤ l[j]!

def noDuplicates (l : List Int) : Prop :=
  ∀ x i j, i < j → j < l.length → l[i]! = x → l[j]! ≠ x

-- <vc-helpers>
-- </vc-helpers>

def mergeArrays (a b : List Int) : List Int := sorry

theorem merge_arrays_is_sorted (a b : List Int) (h₁ : isSorted a) (h₂ : isSorted b) : 
  isSorted (mergeArrays a b) := sorry

theorem merge_arrays_no_duplicates (a b : List Int) :
  noDuplicates (mergeArrays a b) := sorry

theorem merge_arrays_contains_all (a b : List Int) :
  ∀ x, (x ∈ a ∨ x ∈ b) ↔ x ∈ mergeArrays a b := sorry

theorem merge_arrays_length_bound (a b : List Int) :
  (mergeArrays a b).length ≤ a.length + b.length := sorry

theorem merge_arrays_self_idempotent (a : List Int) (h : isSorted a) :
  mergeArrays a a = (a.toArray.qsort (· ≤ ·)).toList := sorry

theorem merge_arrays_empty_identity (a : List Int) (h : isSorted a) :
  mergeArrays a [] = (a.toArray.qsort (· ≤ ·)).toList ∧ 
  mergeArrays [] a = (a.toArray.qsort (· ≤ ·)).toList := sorry

/-
info: [1, 2, 3, 4, 5, 6]
-/
-- #guard_msgs in
-- #eval merge_arrays #[1, 3, 5] #[2, 4, 6]

/-
info: [2, 4, 6, 8]
-/
-- #guard_msgs in
-- #eval merge_arrays #[2, 4, 8] #[2, 4, 6]

/-
info: [1, 2, 3]
-/
-- #guard_msgs in
-- #eval merge_arrays #[1, 2, 3] #[]

-- Apps difficulty: introductory
-- Assurance level: unguarded