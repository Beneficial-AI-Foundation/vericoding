/-
# Task
 Your task is to find the similarity of given sorted arrays `a` and `b`, which is defined as follows: 

 you take the number of elements which are present in both arrays and divide it by the number of elements which are present in at least one array.

 It also can be written as a formula `similarity(A, B) = #(A ∩ B) / #(A ∪ B)`, where `#(C)` is the number of elements in C, `∩` is intersection of arrays, `∪` is union of arrays.

 This is known as `Jaccard similarity`.

 The result is guaranteed to fit any floating-point type without rounding.

# Example

 For `a = [1, 2, 4, 6, 7]` and `b = [2, 3, 4, 7]`:
```
elements [2, 4, 7] are present in both arrays;
elements [1, 2, 3, 4, 6, 7] are present in at least one of the arrays.
So the similarity equals to 3 / 6 = 0.5.```

# Input/Output

 - `[input]` integer array `a`

  A `sorted` array of positive integers. 

  All elements are `different` and are `less than 100`.

  `1 ≤ a.length ≤ 100`

 - `[input]` integer array `b`

  An array in the same format as `a`.

 - `[output]` a float number

  The similarity of the arrays.

  ```Haskell

  In Haskell the two arrays are passed as a touple.
  ```
-/

-- <vc-helpers>
-- </vc-helpers>

def similarity (xs ys : List Int) : Float := sorry

theorem similarity_self_identity (xs : List Int) :
  similarity xs xs = (if xs.isEmpty then 0.0 else 1.0) := sorry

theorem similarity_symmetric (xs ys : List Int) :
  similarity xs ys = similarity ys xs := sorry

theorem similarity_bounds (xs ys : List Int) :
  0 ≤ similarity xs ys ∧ similarity xs ys ≤ 1 := sorry

theorem disjoint_similarity (xs ys : List Int) :
  xs ≠ [] → ys ≠ [] → (∀ y ∈ ys, y ∉ xs) → similarity xs ys = 0 := sorry 

theorem empty_list_similarity (xs : List Int) :
  similarity xs [] = 0 ∧ similarity [] xs = 0 ∧ similarity [] [] = 0 := sorry

/-
info: 1.0
-/
-- #guard_msgs in
-- #eval similarity [1, 2, 3] [1, 2, 3]

/-
info: 0.0
-/
-- #guard_msgs in
-- #eval similarity [1, 2, 3] [4, 5, 6]

/-
info: 0.5
-/
-- #guard_msgs in
-- #eval similarity [1, 2, 4, 6, 7] [2, 3, 4, 7]

-- Apps difficulty: introductory
-- Assurance level: unguarded