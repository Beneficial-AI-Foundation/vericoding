/-
>When no more interesting kata can be resolved, I just choose to create the new kata, to solve their own, to enjoy the process  --myjinxin2015 said

# Description:

```if:javascript
Given an array `arr` that contains some integers(positive, negative or 0), and a `range` list such as `[[start1,end1],[start2,end2],...]`, start and end are the index of `arr` and start always less than end. Your task is to calculate the sum value of each range (start index and end index are both inclusive), and return the maximum sum value.
```
```if:ruby
Given an array (`arr`) of integers and an array (`ranges`) of ranges (e.g. `[[1, 32], [16, 24],...]`), which represent an index range of `arr`, calculate the sum of each range (start index and end index are both inclusive) of `arr`, and return the maximum sum.
```
```if:php
Given an array `$a` that contains some integers and a `$range` list such as `[[$start1, $end1], [$start2, $end2], ... ]` where `$start(n)` and `$end(n)` are valid keys of the non-associative array `$a` and `$start(n)` is always guaranteed to be strictly less than `$end(n)`.  Your task is to calculate the sum value of each range (start index and end index are both inclusive) and return the maximum sum value.
```
```if:haskell
Given a list `arr` that contains some integers(positive, negative or 0), and a `range` list such as `[(start1,end1),(start2,end2),...]`, start and end are the index of `arr` and start always less than end. Your task is to calculate the sum value of each range (start index and end index are both inclusive), and return the maximum sum value.
```

For example:

# Note:

 - `arr`/`$a` always has at least 5 elements;
 - `range`/`$range`/`ranges` always has at least 1 element;
 - All inputs are valid;
 - This is a simple version, if you want some challenge, please [try the challenge version](https://www.codewars.com/kata/the-maximum-sum-value-of-ranges-challenge-version/).

# Some Examples
-/

-- <vc-helpers>
-- </vc-helpers>

def maxSum (arr : List Int) (ranges : List (Nat × Nat)) : Int := sorry

def sumRange (arr : List Int) (start stop : Nat) : Int :=
  (arr.take (stop + 1)).drop start |>.foldl (· + ·) 0

theorem maxSum_ge_range_sums {arr : List Int} {ranges : List (Nat × Nat)}
    (arr_nonempty : arr.length > 0)
    (ranges_valid : ∀ (r : Nat × Nat), r ∈ ranges → r.2 < arr.length ∧ r.1 ≤ r.2) :
  ∀ (start stop : Nat), (start, stop) ∈ ranges → 
    maxSum arr ranges ≥ sumRange arr start stop
  := sorry

theorem maxSum_equals_max_range_sum {arr : List Int} {ranges : List (Nat × Nat)}
    (arr_nonempty : arr.length > 0)
    (ranges_valid : ∀ (r : Nat × Nat), r ∈ ranges → r.2 < arr.length ∧ r.1 ≤ r.2) :
  maxSum arr ranges = (ranges.map (λ (r : Nat × Nat) => sumRange arr r.1 r.2)).maximum?.getD 0
  := sorry

theorem maxSum_invariant_under_zero_ranges {arr : List Int} {ranges : List (Nat × Nat)}
    (arr_nonempty : arr.length > 0)
    (ranges_valid : ∀ (r : Nat × Nat), r ∈ ranges → r.2 < arr.length ∧ r.1 ≤ r.2)
    (ranges_nonempty : ranges.length > 1) :
  let zero_ranges := ranges ++ (List.range arr.length).map (λ i => (i,i))
  maxSum arr zero_ranges = maxSum arr ranges
  := sorry

theorem maxSum_single_element_ranges {arr : List Int}
    (arr_nonempty : arr.length > 0) :
  let ranges := (List.range arr.length).map (λ i => (i,i))
  maxSum arr ranges = arr.maximum?.getD 0
  := sorry

/-
info: 6
-/
-- #guard_msgs in
-- #eval max_sum [1, -2, 3, 4, -5, -4, 3, 2, 1] [[1, 3], [0, 4], [6, 8]]

/-
info: 5
-/
-- #guard_msgs in
-- #eval max_sum [1, -2, 3, 4, -5, -4, 3, 2, 1] [[1, 3]]

/-
info: 88
-/
-- #guard_msgs in
-- #eval max_sum [11, -22, 31, 34, -45, -46, 35, 32, 21] [[1, 4], [0, 3], [6, 8], [0, 8]]

-- Apps difficulty: introductory
-- Assurance level: unguarded