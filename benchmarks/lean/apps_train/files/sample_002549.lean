/-
Given a set of elements (integers or string characters) that may occur more than once, we need to know the amount of subsets that none of their values have repetitions.
Let's see with an example:
``` 
set numbers = {1, 2, 3, 4}
``` 
The subsets are:
``` 
{{1}, {2}, {3}, {4}, {1,2}, {1,3}, {1,4}, {2,3}, {2,4},{3,4}, {1,2,3}, {1,2,4}, {1,3,4}, {2,3,4}, {1,2,3,4}} (15 subsets, as you can see the empty set, {}, is not counted)
``` 
Let's see an example with repetitions of an element:
```
set letters= {a, b, c, d, d}
```
The subsets for this case will be:
```
{{a}, {b}, {c}, {d}, {a,b}, {a,c}, {a,d}, {b,c}, {b,d},{c,d}, {a,b,c}, {a,b,d}, {a,c,d}, {b,c,d}, {a,b,c,d}} (15 subsets, only the ones that have no repeated elements inside)
```

The function ```est_subsets()``` (javascript: ``estSubsets()```) will calculate the number of these subsets.
It will receive the array as an argument and according to its features will output the amount of different subsets without repetitions of its elements.
```python
est_subsets([1, 2, 3, 4]) == 15
est_subsets(['a', 'b', 'c', 'd', 'd']) == 15
```
Features of the random tests:
```
Low Performance Tests: 40
Length of the arrays between 6 and 15

High Performance Tests: 80
Length of the arrays between 15 and 100 (Python an Ruby) and between 15 and 50 javascript)
```
Just do it!
-/

def est_subsets {α : Type} [BEq α] [Hashable α] (arr : List α) : Nat :=
  sorry

-- <vc-helpers>
-- </vc-helpers>

def list_unique_count {α : Type} [BEq α] [Hashable α] (arr : List α) : Nat :=
  sorry

theorem est_subsets_count_prop {α : Type} [BEq α] [Hashable α] (arr : List α) :
  est_subsets arr = 2^(list_unique_count arr) - 1 :=
  sorry

theorem est_subsets_nonneg {α : Type} [BEq α] [Hashable α] (arr : List α) :
  est_subsets arr ≥ 0 :=
  sorry

theorem est_subsets_empty {α : Type} [BEq α] [Hashable α] :
  est_subsets ([] : List α) = 0 :=
  sorry

theorem est_subsets_duplicates {α : Type} [BEq α] [Hashable α] (arr : List α) :
  est_subsets arr = est_subsets (arr ++ arr) :=
  sorry

theorem est_subsets_is_nat {α : Type} [BEq α] [Hashable α] (arr : List α) :
  est_subsets arr = 2^(list_unique_count arr) - 1 :=
  sorry

/-
info: 15
-/
-- #guard_msgs in
-- #eval est_subsets [1, 2, 3, 4]

/-
info: 15
-/
-- #guard_msgs in
-- #eval est_subsets ["a", "b", "c", "d", "d"]

/-
info: 15
-/
-- #guard_msgs in
-- #eval est_subsets [1, 2, 2, 3, 3, 3, 4]

-- Apps difficulty: introductory
-- Assurance level: guarded