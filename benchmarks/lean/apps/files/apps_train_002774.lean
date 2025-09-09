/-
Your goal in this kata is to implement a difference function, which subtracts one list from another and returns the result.

It should remove all values from list `a`, which are present in list `b`.

```python
array_diff([1,2],[1]) == [2]
```

If a value is present in `b`, all of its occurrences must be removed from the other:

```python
array_diff([1,2,2,2,3],[2]) == [1,3]
```
~~~ if:c
NOTE: In C, assign return array length to pointer *z
~~~
-/

-- <vc-helpers>
-- </vc-helpers>

def array_diff (a b : List Int) : List Int := sorry

theorem array_diff_elements_from_a (a b : List Int) :
  ∀ x ∈ array_diff a b, x ∈ a := sorry

theorem array_diff_no_elements_from_b (a b : List Int) :
  ∀ x ∈ array_diff a b, x ∉ b := sorry

theorem array_diff_preserves_order (a b : List Int) :
  array_diff a b = a.filter (fun x => x ∈ array_diff a b) := sorry

theorem array_diff_empty_b (a : List Int) :
  array_diff a [] = a := sorry

theorem array_diff_identical_lists (a : List Int) :
  array_diff a a = [] := sorry

/-
info: [2]
-/
-- #guard_msgs in
-- #eval array_diff [1, 2] [1]

/-
info: [2, 2]
-/
-- #guard_msgs in
-- #eval array_diff [1, 2, 2] [1]

/-
info: [1]
-/
-- #guard_msgs in
-- #eval array_diff [1, 2, 2] [2]

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible