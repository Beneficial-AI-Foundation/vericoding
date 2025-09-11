-- <vc-preamble>
def IsSorted (l : List Int) : Prop :=
  ∀ i j, i < j → j < l.length → l[i]! ≤ l[j]!

def IsReverseSorted (l : List Int) : Prop :=
  ∀ i j, i < j → j < l.length → l[i]! ≥ l[j]!

def Nodup (l : List Int) : Prop :=
  ∀ i j, i < j → j < l.length → l[i]! ≠ l[j]!
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def min_moves_to_sort (n : Nat) (arr : List Int) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem moves_less_than_length {n : Nat} {arr : List Int} (h : n = arr.length) :
  min_moves_to_sort n arr ≤ n :=
  sorry

/-
info: 2
-/
-- #guard_msgs in
-- #eval min_moves_to_sort 5 [2, 1, 4, 5, 3]

/-
info: 0
-/
-- #guard_msgs in
-- #eval min_moves_to_sort 3 [1, 2, 3]

/-
info: 3
-/
-- #guard_msgs in
-- #eval min_moves_to_sort 4 [4, 3, 2, 1]
-- </vc-theorems>

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible