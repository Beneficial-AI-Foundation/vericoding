Array inversion indicates how far the array is from being sorted.

Inversions are pairs of elements in array that are out of order.

## Examples

```
[1, 2, 3, 4]  =>  0 inversions
[1, 3, 2, 4]  =>  1 inversion: 2 and 3
[4, 1, 2, 3]  =>  3 inversions: 4 and 1, 4 and 2, 4 and 3
[4, 3, 2, 1]  =>  6 inversions: 4 and 3, 4 and 2, 4 and 1, 3 and 2, 3 and 1, 2 and 1
```

## Goal

The goal is to come up with a function that can calculate inversions for any arbitrary array

def count_inversions (lst : List Int) : Nat :=
  sorry

def isSorted (l : List Int) : Prop :=
  ∀ i j, i < j → j < l.length → l[i]! ≤ l[j]!

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: guarded
