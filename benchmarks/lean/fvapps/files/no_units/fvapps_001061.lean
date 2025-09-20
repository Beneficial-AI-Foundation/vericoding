-- <vc-preamble>
def IsSorted (l : List Int) : Prop :=
  ∀ i j, i < j → j < l.length → l[i]! ≤ l[j]!

def IsReverseSorted (l : List Int) : Prop :=
  ∀ i j, i < j → j < l.length → l[i]! ≥ l[j]!

def Nodup (l : List Int) : Prop :=
  ∀ i j, i < j → j < l.length → l[i]! ≠ l[j]!
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def min_moves_to_sort (n : Nat) (arr : List Int) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem moves_less_than_length {n : Nat} {arr : List Int} (h : n = arr.length) :
  min_moves_to_sort n arr ≤ n :=
  sorry
-- </vc-theorems>