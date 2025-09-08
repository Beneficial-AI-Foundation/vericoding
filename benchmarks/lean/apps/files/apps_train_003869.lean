/-
Is every value in the array an array?

This should only test the second array dimension of the array. The values of the nested arrays don't have to be arrays. 

Examples:

```python
[[1],[2]] => true
['1','2'] => false
[{1:1},{2:2}] => false
```
-/

-- <vc-helpers>
-- </vc-helpers>

def arr_check (arr : List α) : Bool :=
  sorry

theorem valid_array_of_arrays {α : Type} (arr : List (List α)) :
  arr_check arr = true :=
sorry

theorem invalid_array_of_non_arrays {α : Type} (arr : List α) 
  (h : arr.length ≥ 1) :
  arr_check arr = false :=
sorry

theorem array_of_empty_lists {α : Type} (arr : List (List α))
  (h : ∀ l ∈ arr, l.length = 0) :  
  arr_check arr = true :=
sorry

/-
info: True
-/
-- #guard_msgs in
-- #eval arr_check [[]]

/-
info: True
-/
-- #guard_msgs in
-- #eval arr_check [[1], [2], [3]]

/-
info: False
-/
-- #guard_msgs in
-- #eval arr_check ["A", "R", "R", "A", "Y"]

-- Apps difficulty: introductory
-- Assurance level: unguarded