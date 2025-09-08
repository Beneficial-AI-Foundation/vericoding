/-
###Instructions

A time period starting from ```'hh:mm'``` lasting until ```'hh:mm'``` is stored in an array:
```
['08:14', '11:34']
```
A set of different time periods is then stored in a 2D Array like so, each in its own sub-array:
```
[['08:14','11:34'], ['08:16','08:18'], ['22:18','01:14'], ['09:30','10:32'], ['04:23','05:11'], ['11:48','13:48'], ['01:12','01:14'], ['01:13','08:15']]
```
Write a function that will take a 2D Array like the above as argument and return a 2D Array of the argument's sub-arrays sorted in ascending order.

Take note of the following:

* The first time period starts at the earliest time  possible ```('00:00'+)```.
* The next time period is the one that starts the soonest **after** the prior time period finishes. If several time periods begin at the same hour, pick the first one showing up in the original array.
* The next time period can start the same time the last one finishes.

This:
```
[['08:14','11:34'], ['08:16','08:18'], ['13:48','01:14'], ['09:30','10:32'], ['04:23','05:11'], ['11:48','13:48'], ['01:12','01:14'], ['01:13','08:15']]
```
Should return:
```
[['01:12','01:14'], ['04:23','05:11'], ['08:14','11:34'], ['11:48','13:48'], ['13:48','01:14'], ['08:16','08:18'], ['09:30','10:32'], ['01:13','08:15']]
```
-/

-- <vc-helpers>
-- </vc-helpers>

def sort_time (pairs : List TimePair) : List TimePair :=
  sorry

theorem sort_time_length_preserving
  (pairs : List TimePair) :
  List.length (sort_time pairs) = List.length pairs :=
  sorry

theorem sort_time_elements_same
  (pairs : List TimePair) :
  ∀ x, x ∈ sort_time pairs ↔ x ∈ pairs :=
  sorry

theorem sort_time_valid_ordering
  (pairs : List TimePair) 
  (i : Nat)
  (h₁ : i < List.length (sort_time pairs) - 1)
  (h₂ : i < List.length (sort_time pairs))
  (h₃ : i + 1 < List.length (sort_time pairs)) :
  let result := sort_time pairs
  let curr := result[i]'h₂
  let next := result[i+1]'h₃
  next.start < curr.end_ → curr.end_ > next.start :=
  sorry

theorem sort_time_idempotent
  (pairs : List TimePair) :
  sort_time (sort_time pairs) = sort_time pairs :=
  sorry

theorem sort_time_concatenation
  (lists : List (List TimePair))
  (h : lists ≠ []) :
  let flattened := List.join lists
  sort_time flattened = sort_time (sort_time flattened) :=
  sorry

-- Apps difficulty: introductory
-- Assurance level: unguarded